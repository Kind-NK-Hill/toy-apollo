from __future__ import annotations

import gzip
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore
from src.toy_apollo.task_catalog import (
    CatalogFamily,
    CatalogModule,
    CatalogTask,
    TaskCatalog,
)
from src.toy_apollo.workspace_status import (
    analysis_tmp_inventory,
    render_analysis_tmp_index,
    repository_status,
    task_status_rows,
    validate_policy_coverage,
    write_file_inventory,
)


def _catalog() -> TaskCatalog:
    task = CatalogTask(
        task_id="thm_1_1",
        family_id="thm_1_1",
        chapter=1,
        task_kind="Theorem_with_Proof",
        source_plan="chapter1",
        source_plan_path="plans/chapter1.json",
        source_hash="plan-hash",
        primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
        legacy_manifest_role="ledger_task_module",
        lifecycle_state="active",
    )
    family = CatalogFamily(
        family_id=task.family_id,
        book_label="Theorem 1.1",
        family_kind="singleton",
        count_policy="one_task",
        members=(task.task_id,),
    )
    module = CatalogModule(
        path=task.primary_path,
        basename="thm_1_1",
        module_name="ProbabilityTheory.chapter_01.thm_1_1",
        module_role="primary",
        owner_task_id=task.task_id,
        legacy_manifest_role="ledger_task_module",
        chapter=1,
    )
    owned_support = CatalogModule(
        path="ProbabilityTheory/chapter_01/thm_1_1_support.lean",
        basename="thm_1_1_support",
        module_name="ProbabilityTheory.chapter_01.thm_1_1_support",
        module_role="owned_support",
        owner_task_id=task.task_id,
        legacy_manifest_role="owned_support",
        chapter=1,
    )
    shared_support = CatalogModule(
        path="ProbabilityTheory/common_support/shared.lean",
        basename="shared",
        module_name="ProbabilityTheory.common_support.shared",
        module_role="shared",
        owner_task_id=None,
        legacy_manifest_role="shared_support",
        chapter=None,
    )
    return TaskCatalog(
        catalog_id="test-catalog-v1",
        catalog_name="test",
        toy_commit="toy",
        mat_commit="mat",
        manifest_sha256="manifest",
        plan_set_sha256="plans",
        policy_sha256="policy",
        tasks=(task,),
        families=(family,),
        modules=(module, owned_support, shared_support),
        cohorts={"legacy": (task.task_id,)},
        restored_task_ids=(),
        role_migrations=(),
    )


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)


class WorkspaceStatusTests(unittest.TestCase):
    def test_analysis_tmp_index_classifies_every_first_level_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            analysis = workspace / "_analysis_tmp"
            worktree = analysis / "review-worktree"
            fixture = analysis / "pytest_fixture"
            empty = analysis / "empty"
            cache = analysis / "__pycache__"
            sql_workspace = analysis / "sql_workspace_test"
            for path in (worktree, fixture, empty, cache, sql_workspace):
                path.mkdir(parents=True)
            (worktree / "candidate.lean").write_text("theorem t : True := by trivial\n")
            (fixture / "input.json").write_text("{}\n")
            (analysis / "audit.json").write_text("{}\n")
            (analysis / "relay.ps1").write_text("Write-Output 'relay'\n")
            worktrees = [
                {
                    "path": str(worktree),
                    "owner_repository": str(workspace / "mat"),
                    "branch": None,
                    "head": "a" * 40,
                    "dirty": True,
                    "unstaged_files": 1,
                    "staged_files": 0,
                    "untracked_files": 0,
                }
            ]

            inventory = analysis_tmp_inventory(
                workspace_root=workspace,
                worktrees=worktrees,
                exclude_names={".git"},
            )
            rows = {row["name"]: row for row in inventory["rows"]}
            rendered = render_analysis_tmp_index(inventory)

            self.assertEqual(inventory["children"], 7)
            self.assertEqual(rows["review-worktree"]["role"], "registered_worktree")
            self.assertEqual(rows["pytest_fixture"]["role"], "test_or_analysis_fixture")
            self.assertEqual(rows["empty"]["role"], "empty_scratch")
            self.assertEqual(rows["audit.json"]["role"], "analysis_report_or_manifest")
            self.assertEqual(rows["__pycache__"]["role"], "generated_cache")
            self.assertEqual(rows["relay.ps1"]["role"], "analysis_tool")
            self.assertEqual(
                rows["sql_workspace_test"]["role"],
                "linked_state_projection_workspace",
            )
            self.assertIn("review-worktree", rendered)
            self.assertIn("retain_until_deliberate_git_worktree_closeout", rendered)

    def test_repository_status_expands_untracked_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            _git(repo, "init")
            _git(repo, "config", "user.email", "test@example.com")
            _git(repo, "config", "user.name", "Test")
            tracked = repo / "tracked.txt"
            tracked.write_text("first\n", encoding="utf-8")
            _git(repo, "add", "tracked.txt")
            _git(repo, "commit", "-m", "initial")
            tracked.write_text("second\n", encoding="utf-8")
            (repo / "untracked-a.txt").write_text("a\n", encoding="utf-8")
            (repo / "untracked-b.txt").write_text("b\n", encoding="utf-8")

            status = repository_status(repo)

            self.assertTrue(status["dirty"])
            self.assertEqual(status["unstaged_files"], 1)
            self.assertEqual(status["untracked_files"], 2)

    def test_policy_coverage_distinguishes_optional_generated_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            (workspace / "active").mkdir()
            policy = {
                "entries": {
                    "active": {"edit_policy": "active"},
                    "CURRENT_STATUS.md": {"edit_policy": "generated"},
                }
            }

            report = validate_policy_coverage(workspace, policy)

            self.assertTrue(report["valid"])
            self.assertEqual(report["optional_generated_absent"], ["CURRENT_STATUS.md"])

    def test_file_inventory_records_actual_purpose_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            runtime = workspace / "toy-apollo"
            runtime.mkdir()
            (runtime / "tool.py").write_text(
                '"""Explain the current workspace state."""\n\ndef main():\n    pass\n',
                encoding="utf-8",
            )
            (runtime / "thm_1_1.lean").write_text(
                "theorem t : True := by trivial\n", encoding="utf-8"
            )
            (runtime / "thm_1_1_support.lean").write_text(
                "theorem helper : True := by trivial\n", encoding="utf-8"
            )
            (runtime / "shared.lean").write_text(
                "theorem shared : True := by trivial\n", encoding="utf-8"
            )
            output = workspace / "inventory" / "files.jsonl.gz"
            policy = {
                "inventory": {
                    "exclude_directory_names": [],
                    "semantic_inspection_roots": ["toy-apollo"],
                },
                "entries": {
                    "toy-apollo": {
                        "role": "active_runtime_repository",
                        "description": "Active runtime.",
                        "authority": "runtime_source",
                        "edit_policy": "active",
                        "lifecycle": "current",
                    },
                    "inventory": {
                        "role": "generated_inventory",
                        "description": "Generated inventory.",
                        "authority": "report_only",
                        "edit_policy": "generated",
                        "lifecycle": "current",
                    },
                },
            }

            summary = write_file_inventory(
                workspace_root=workspace,
                output_path=output,
                policy=policy,
                catalog=_catalog(),
                repository_file_sets={},
            )
            with gzip.open(output, "rt", encoding="utf-8") as handle:
                rows = [json.loads(line) for line in handle]
            files = {row["path"]: row for row in rows if row["record_type"] == "file"}

            self.assertEqual(summary["files"], 4)
            self.assertEqual(files["toy-apollo/tool.py"]["purpose_source"], "module_docstring")
            self.assertEqual(files["toy-apollo/thm_1_1.lean"]["purpose_source"], "task_catalog")
            self.assertIn("Task Parent", files["toy-apollo/thm_1_1.lean"]["purpose"])
            self.assertIn(
                "Proof-Layer Support",
                files["toy-apollo/thm_1_1_support.lean"]["purpose"],
            )
            self.assertIn("Shared Support", files["toy-apollo/shared.lean"]["purpose"])

    def test_task_status_keeps_completion_and_current_coverage_separate(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            catalog = _catalog()
            store.persist_catalog(catalog)
            source = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={"review/thm_1_1.lean": "theorem t : True := by trivial\n"},
                primary_path="review/thm_1_1.lean",
                source_repo="toy_apollo",
                source_commit="toy",
                layout="toy",
            )
            current = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={
                    "ProbabilityTheory/chapter_01/thm_1_1.lean":
                        "theorem t : True := by trivial\n"
                },
                primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
                source_repo="mat",
                source_commit="mat",
                layout="mat",
            )
            store.upsert_subject(source)
            store.upsert_subject(current)
            store.record_review(
                task_id=source.task_id,
                subject_id=source.subject_id,
                verdict="pass",
                proof_class="textbook_proof_completed",
                completion_class="textbook_proof_completed",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review.json",
                evidence_hash="review-evidence",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.record_transformation(
                task_id=source.task_id,
                source_subject_id=source.subject_id,
                target_subject_id=current.subject_id,
                transformation_kind="path_relocation",
                mechanical_status="pass",
                build_status="pass",
            )
            store.set_task_head(
                task_id=current.task_id,
                role="mat_main",
                subject_id=current.subject_id,
                freshness="fresh",
            )

            row = task_status_rows(store, catalog)[0]

            self.assertTrue(row["compatible_pass"])
            self.assertTrue(row["authority_eligible_pass"])
            self.assertEqual(row["current_mat_coverage"], "validated_transformation")
            self.assertFalse(row["typed_authority"])


if __name__ == "__main__":
    unittest.main()
