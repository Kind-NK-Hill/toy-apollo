from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from formalization_engine.state_store import SubjectBundle, sha256_file, sha256_json
from tools.mat_catalog_review_apply import (
    ApplyError,
    _render_review_supplement_context,
    _validate_review_supplement_binding,
)
from tools.mat_catalog_review_prepare import (
    PrepareError,
    _build_review_supplement,
    _write_immutable_json,
)


class MatCatalogReviewSupplementTests(unittest.TestCase):
    task_id = "def_1_2"

    @staticmethod
    def _git(repo: Path, *args: str) -> str:
        completed = subprocess.run(
            ["git", "-C", str(repo), *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=True,
        )
        return completed.stdout.decode("utf-8").strip()

    def _repo(self, root: Path, files: dict[str, str]) -> tuple[Path, str]:
        root.mkdir(parents=True)
        self._git(root, "init", "-q")
        self._git(root, "config", "user.name", "Fixture")
        self._git(root, "config", "user.email", "fixture@example.test")
        for relative, content in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8", newline="\n")
        self._git(root, "add", ".")
        self._git(root, "commit", "-qm", "fixture")
        return root, self._git(root, "rev-parse", "HEAD")

    def _fixture(self, root: Path) -> tuple[Path, SubjectBundle, Path]:
        primary_path = "ProbabilityTheory/chapter_01/def_1_2.lean"
        closure_path = "ProbabilityTheory/chapter_01/thm_1_2.lean"
        mat_repo, mat_commit = self._repo(
            root / "mat",
            {
                primary_path: "def def_1_2 : Prop := True\n",
                closure_path: "theorem closure : True := by trivial\n",
            },
        )
        kenneth_repo, kenneth_commit = self._repo(
            root / "kenneth", {primary_path: "def def_1_2 : Prop := True\n"}
        )
        subject = SubjectBundle.from_files(
            task_id=self.task_id,
            files={primary_path: (mat_repo / primary_path).read_bytes()},
            primary_path=primary_path,
            source_repo="mat",
            source_commit=mat_commit,
            layout="mat",
            subject_kind="catalog_git_bundle",
        )
        history = root / "gate2.json"
        history.write_text(
            json.dumps({"verdict": "pass", "reason": "author design accepted"}),
            encoding="utf-8",
        )
        spec = {
            "schema": "mat.catalog.review-supplement-spec.v1",
            "task_id": self.task_id,
            "target_commit": mat_commit,
            "kenneth_upstream": {
                "status": "present",
                "repo": str(kenneth_repo),
                "ref": "HEAD",
                "commit": kenneth_commit,
                "files": [
                    {
                        "path": primary_path,
                        "blob": self._git(kenneth_repo, "rev-parse", f"{kenneth_commit}:{primary_path}"),
                        "target_path": primary_path,
                        "relationship": "byte_identical",
                    }
                ],
            },
            "historical_evidence": [
                {
                    "path": str(history),
                    "sha256": sha256_file(history),
                    "purpose": "Kenneth-independent Gate 2 decision",
                }
            ],
            "proof_closure": [
                {
                    "path": closure_path,
                    "blob": self._git(mat_repo, "rev-parse", f"{mat_commit}:{closure_path}"),
                    "purpose": "Direct consumer closes the tagged-limit bridge",
                }
            ],
            "risk_resolutions": [
                {
                    "risk": "Nonempty witness shell",
                    "status": "superseded",
                    "rationale": "The embedded author decision and closure show the intended bridge.",
                }
            ],
            "reviewer_instruction": "Judge the exact subject with the embedded author decision and closure.",
        }
        spec_path = root / "supplement_spec.json"
        spec_path.write_text(json.dumps(spec, indent=2), encoding="utf-8")
        return mat_repo, subject, spec_path

    def test_prepare_embeds_verified_git_and_historical_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mat_repo, subject, spec_path = self._fixture(root)
            supplement = _build_review_supplement(
                spec_path=spec_path,
                task_id=self.task_id,
                target_commit=subject.source_commit,
                subject=subject,
                mat_repo=mat_repo,
            )

            self.assertEqual(supplement["subject_id"], subject.subject_id)
            self.assertIn("author design accepted", supplement["historical_evidence"][0]["content"])
            self.assertIn("theorem closure", supplement["proof_closure"][0]["content"])
            self.assertEqual(supplement["risk_resolutions"][0]["status"], "superseded")
            self.assertEqual(
                supplement["kenneth_upstream"]["files"][0]["relationship"],
                "byte_identical",
            )
            self.assertEqual(
                supplement["kenneth_upstream"]["files"][0]["target_path"],
                "ProbabilityTheory/chapter_01/def_1_2.lean",
            )

            evidence_path = root / "review_supplement_evidence_v2.json"
            _write_immutable_json(evidence_path, supplement)
            _write_immutable_json(evidence_path, supplement)
            changed = dict(supplement)
            changed["reviewer_instruction"] = "different"
            with self.assertRaisesRegex(PrepareError, "Refusing to overwrite"):
                _write_immutable_json(evidence_path, changed)

    def test_prepare_rejects_stale_evidence_and_wrong_closure_blob(self):
        for case in ("history", "closure"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                mat_repo, subject, spec_path = self._fixture(root)
                spec = json.loads(spec_path.read_text(encoding="utf-8"))
                if case == "history":
                    Path(spec["historical_evidence"][0]["path"]).write_text(
                        "tampered", encoding="utf-8"
                    )
                    message = "Historical evidence hash mismatch"
                else:
                    spec["proof_closure"][0]["blob"] = "0" * 40
                    spec_path.write_text(json.dumps(spec), encoding="utf-8")
                    message = "proof-closure blob mismatch"
                with self.assertRaisesRegex(PrepareError, message):
                    _build_review_supplement(
                        spec_path=spec_path,
                        task_id=self.task_id,
                        target_commit=subject.source_commit,
                        subject=subject,
                        mat_repo=mat_repo,
                    )

    def test_explicit_absent_kenneth_requires_a_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mat_repo, subject, spec_path = self._fixture(root)
            spec = json.loads(spec_path.read_text(encoding="utf-8"))
            spec["kenneth_upstream"] = {"status": "absent", "reason": ""}
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaisesRegex(PrepareError, "kenneth_upstream.reason"):
                _build_review_supplement(
                    spec_path=spec_path,
                    task_id=self.task_id,
                    target_commit=subject.source_commit,
                    subject=subject,
                    mat_repo=mat_repo,
                )

    def test_prepare_rejects_drifted_mat_target_for_byte_identical_relationship(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mat_repo, subject, spec_path = self._fixture(root)
            spec = json.loads(spec_path.read_text(encoding="utf-8"))
            spec["kenneth_upstream"]["files"][0]["target_path"] = (
                "ProbabilityTheory/chapter_01/thm_1_2.lean"
            )
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaisesRegex(PrepareError, "byte-identical target mismatch"):
                _build_review_supplement(
                    spec_path=spec_path,
                    task_id=self.task_id,
                    target_commit=subject.source_commit,
                    subject=subject,
                    mat_repo=mat_repo,
                )

    def test_apply_rejects_tampered_supplement_before_state_access(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mat_repo, subject, spec_path = self._fixture(root)
            supplement = _build_review_supplement(
                spec_path=spec_path,
                task_id=self.task_id,
                target_commit=subject.source_commit,
                subject=subject,
                mat_repo=mat_repo,
            )
            evidence_path = root / "review_supplement_evidence_v2.json"
            _write_immutable_json(evidence_path, supplement)
            file_hash = sha256_file(evidence_path)
            content_hash = sha256_json(supplement)
            metadata = {
                "review_supplement_file": str(evidence_path),
                "review_supplement_hash": file_hash,
                "review_supplement_content_hash": content_hash,
            }
            review_input = {
                "review_basis": {
                    "review_supplement": supplement,
                    "review_supplement_file": str(evidence_path),
                    "review_supplement_file_sha256": file_hash,
                    "review_supplement_content_sha256": content_hash,
                },
                "review_context_markdown": _render_review_supplement_context(
                    supplement, file_hash=file_hash, content_hash=content_hash
                ),
            }
            self.assertEqual(
                _validate_review_supplement_binding(
                    pack_dir=root,
                    metadata=metadata,
                    review_input=review_input,
                    subject=subject,
                ),
                supplement,
            )

            evidence_path.write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(ApplyError, "hash mismatch"):
                _validate_review_supplement_binding(
                    pack_dir=root,
                    metadata=metadata,
                    review_input=review_input,
                    subject=subject,
                )


if __name__ == "__main__":
    unittest.main()
