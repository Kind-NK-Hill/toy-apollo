from __future__ import annotations

import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.check_public_release import check, machine_path_findings
from tools.export_public_release import export
from tools.public_release_policy import find_forbidden_tracked_files


class PublicReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "source"
        self.root.mkdir()
        self.output = Path(self.temp.name) / "public"
        self.git("init", "--quiet")
        self.git("config", "user.name", "Publication fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("ProbabilityTheory/chapter_01/def_sample.lean",
                   "/- private source /- nested prose -/ -/\ndef sample : Nat := 1\n")
        path = "ProbabilityTheory/chapter_01/def_sample.lean"
        sha = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        corpus = hashlib.sha256(f"{path} {sha}".encode()).hexdigest()
        manifest = ("basename,file_path,module_name,chapter,ledger_status\n"
                    f"def_sample,{path},ProbabilityTheory.chapter_01.def_sample,1,COMPLETED\n")
        self.write("manifest_by_chapter.csv", manifest)
        self.write("COORDINATION_PROVENANCE.md", corpus + " " + hashlib.sha256(manifest.encode()).hexdigest())
        self.write("README.md", "Public description\n")
        self.write("inputs/private.tex", "do not publish\n")
        self.write("plans/private.json", "{}\n")
        self.write("data/task_catalog/catalog_policy_v2.json", "{}\n")
        tools_root = Path(__file__).resolve().parents[1] / "tools"
        for name in ("export_public_release.py", "public_release_policy.py", "prepare_public_snapshot.py"):
            self.write(f"tools/{name}", (tools_root / name).read_text(encoding="utf-8"))
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "fixture")

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)

    def write(self, relative, content):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8", newline="\n")

    def paths(self):
        return [p.relative_to(self.output).as_posix() for p in self.output.rglob("*") if p.is_file()]

    def test_committed_projection_preserves_code_and_omits_private_state(self):
        self.write("README.md", "Uncommitted change must stay local\n")
        export(self.root, "HEAD", self.output)
        self.assertEqual((self.output / "README.md").read_text(), "Public description\n")
        self.assertFalse((self.output / "inputs").exists())
        self.assertFalse((self.output / "plans").exists())
        text = (self.output / "ProbabilityTheory/chapter_01/def_sample.lean").read_text()
        self.assertNotIn("private source", text)
        self.assertIn("def sample : Nat := 1", text)
        rows = list(csv.DictReader(io.StringIO((self.output / "manifest_by_chapter.csv").read_text())))
        self.assertEqual(set(rows[0]), {"basename", "file_path", "module_name", "chapter", "sha256"})
        self.assertEqual(check(self.output, self.paths()), [])

    def test_export_is_deterministic(self):
        export(self.root, "HEAD", self.output)
        other = self.output.with_name("second")
        export(self.root, "HEAD", other)
        for path in self.paths():
            self.assertEqual((self.output / path).read_bytes(), (other / path).read_bytes(), path)

    def test_source_ref_must_bind_executing_tools(self):
        self.write("tools/public_release_policy.py", "# changed policy\n")
        self.git("add", "tools/public_release_policy.py")
        self.git("commit", "--quiet", "-m", "different exporter")
        with self.assertRaisesRegex(ValueError, "executing publication tool"):
            export(self.root, "HEAD", self.output)

    def test_rejects_nonempty_destination_without_mutation(self):
        self.output.mkdir()
        canary = self.output / "keep.txt"
        canary.write_text("keep")
        with self.assertRaisesRegex(ValueError, "empty"):
            export(self.root, "HEAD", self.output)
        self.assertEqual(canary.read_text(), "keep")

    def test_rejects_destination_inside_source(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            export(self.root, "HEAD", self.root / "export")

    def test_tampering_and_added_private_file_fail(self):
        export(self.root, "HEAD", self.output)
        (self.output / "README.md").write_text("tampered")
        (self.output / "project_ledger.json").write_text("{}")
        errors = check(self.output, self.paths())
        self.assertTrue(any("fingerprint mismatch: README.md" in e for e in errors))
        self.assertTrue(any("private path: project_ledger.json" in e for e in errors))

    def test_manifest_escape_is_rejected_before_read(self):
        export(self.root, "HEAD", self.output)
        path = self.output / "data/publication/release_manifest.json"
        data = json.loads(path.read_text())
        data["files"].append({"path": "C:/private.txt", "sha256": "0" * 64})
        path.write_text(json.dumps(data))
        self.assertIn("private manifest path: C:/private.txt", check(self.output, self.paths()))

    def test_private_boundaries_include_windows_and_nested_secrets(self):
        paths = ["inputs/private.tex", "plans/tasks.json", "upstream/snapshot.lean",
                 "docs/archive/old.md", "data/migration/legacy_evidence_relocation_v1.json",
                 "tests/.env.local", "x/state.sqlite3", "../outside", "C:/outside",
                 "tests/fixtures/semantic_fail_diagnosis_result_v1.json"]
        self.assertEqual(find_forbidden_tracked_files(paths), paths)
        self.assertEqual(find_forbidden_tracked_files(["examples/workflow-demo/source.tex"]), [])

    def test_matching_fingerprint_does_not_allow_personal_paths_in_rules(self):
        self.write(".claude/rules/example.md", "Local material:\n`D:/Grad_Study/Practimum/Formalization/research materials`\n")
        self.git("add", ".claude/rules/example.md")
        self.git("commit", "--quiet", "-m", "machine path fixture")
        export(self.root, "HEAD", self.output)
        errors = check(self.output, self.paths())
        self.assertIn("machine-specific path: .claude/rules/example.md:2", errors)
        self.assertFalse(any("fingerprint mismatch" in error for error in errors))

    def test_personal_path_detection_handles_json_escapes_and_posix_homes(self):
        for text in (
            json.dumps({"root": r"C:\Users\named-owner\run"}),
            "/home/named-owner/run",
            "/Users/named-owner/run",
        ):
            with self.subTest(text=text):
                self.assertEqual(machine_path_findings("examples/demo/result.json", text),
                                 ["machine-specific path: examples/demo/result.json:1"])

    def test_setup_examples_and_deliberate_test_fixtures_are_not_personal_paths(self):
        examples = "\n".join((
            r"C:\work\ProbabilityTheoryFormalization", r"C:\exports\public",
            "/absolute/path/reviewer.py", "/home/<username>/project",
            r"C:\Users\username\project", "<workspace>/research materials",
        ))
        self.assertEqual(machine_path_findings("docs/development.md", examples), [])
        self.assertEqual(machine_path_findings("tests/fixtures/path_cases.json",
                                              r"C:\Users\named-owner\run"), [])

    def test_publication_metadata_cannot_claim_semantic_authority(self):
        export(self.root, "HEAD", self.output)
        path = self.output / "data/publication/release_manifest.json"
        data = json.loads(path.read_text())
        data["source_commit"] = "not-a-commit"
        data["authority"] = "semantic_review_pass"
        path.write_text(json.dumps(data))
        errors = check(self.output, self.paths())
        self.assertIn("source_commit must identify a full Git commit", errors)
        self.assertIn("publication manifest cannot assert semantic review authority", errors)
        self.assertIn("corpus and release source commits differ", errors)

    def test_allowlist_and_corpus_map_are_required(self):
        export(self.root, "HEAD", self.output)
        (self.output / "data/publication/corpus_map.json").unlink()
        (self.output / "notes").mkdir()
        (self.output / "notes/private.md").write_text("private")
        errors = check(self.output, self.paths())
        self.assertIn("private path: notes/private.md", errors)
        self.assertIn("public corpus mapping is missing", errors)


if __name__ == "__main__":
    unittest.main()
