from __future__ import annotations

import json
import shutil
import subprocess
import unittest
import uuid
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.toy_apollo.state_exact_build_batch import (
    EXACT_BUILD_SCHEMA,
    ExactBuildBatchError,
    collect_exact_build_selection,
    emit_current_exact_builds_batch,
)
from src.toy_apollo.state_store import SubjectBundle


class ExactBuildBatchTests(unittest.TestCase):
    commit = "3" * 40
    task_ids = ("thm_1_1", "thm_1_2", "thm_1_3")

    def setUp(self):
        scratch_root = (
            Path(__file__).resolve().parents[2]
            / "_analysis_tmp"
            / "test_state_exact_build_batch"
        )
        self.root = scratch_root / uuid.uuid4().hex
        self.root.mkdir(parents=True)
        self.addCleanup(shutil.rmtree, self.root)

    def _fixture(self, root: Path):
        workspace = root / "workspace"
        runtime = workspace / "toy-apollo"
        mat_repo = workspace / "MAT3280-formalization-output"
        checkout = root / "checkout"
        (mat_repo / ".git").mkdir(parents=True)
        (checkout / ".git").mkdir(parents=True)
        runtime.mkdir()
        subjects = {}
        modules = []
        for task_id in self.task_ids:
            module = f"ProbabilityTheory.chapter_01.{task_id}"
            path = module.replace(".", "/") + ".lean"
            files = {path: f"theorem {task_id} : True := by trivial\n"}
            if task_id == self.task_ids[0]:
                support_module = module + "_support"
                support_path = support_module.replace(".", "/") + ".lean"
                files[support_path] = f"theorem {task_id}_support : True := by trivial\n"
                modules.append(
                    SimpleNamespace(
                        owner_task_id=task_id,
                        module_role="owned_support",
                        module_name=support_module,
                    )
                )
            subjects[task_id] = SubjectBundle.from_files(
                task_id=task_id,
                files=files,
                primary_path=path,
                source_repo="mat",
                source_commit=self.commit,
                layout="mat",
                subject_kind="catalog_git_bundle",
            )
            modules.append(
                SimpleNamespace(
                    owner_task_id=task_id,
                    module_role="primary",
                    module_name=module,
                )
            )
        catalog = SimpleNamespace(
            mat_commit=self.commit,
            modules=modules,
            task_ids=lambda: list(self.task_ids),
            owned_paths=lambda task_id: tuple(
                item.path for item in subjects[task_id].files
            ),
        )
        return workspace, runtime, checkout, subjects, catalog

    def _command_text(self, _repo: Path, *args: str) -> str:
        if args[-1] in {"origin/main", "HEAD"}:
            return self.commit
        if "status" in args:
            return ""
        raise AssertionError(args)

    def test_selection_accepts_task_files_and_action_manifests(self):
        task_file = self.root / "tasks.txt"
        task_file.write_text("# comment\nthm_1_1, thm_1_2\n", encoding="utf-8")
        manifest = self.root / "actions.json"
        manifest.write_text(
            json.dumps(
                    {
                        "schema": "toy-apollo.resolved-invalidation-action-manifest.v1",
                        "mat_commit": self.commit,
                        "counts": {
                            "unique_exact_build_tasks": 2,
                            "unique_owned_modules": 2,
                            "unique_primary_build_modules": 2,
                        },
                        "unique_exact_builds": [
                            {
                                "task_id": "thm_1_2",
                                "owned_modules": ["ProbabilityTheory.chapter_01.thm_1_2"],
                                "primary_build_module": "ProbabilityTheory.chapter_01.thm_1_2",
                            },
                            {
                                "task_id": "thm_1_3",
                                "owned_modules": ["ProbabilityTheory.chapter_01.thm_1_3"],
                                "primary_build_module": "ProbabilityTheory.chapter_01.thm_1_3",
                            },
                    ],
                }
            ),
            encoding="utf-8",
        )
        selection = collect_exact_build_selection(
            task_files=[task_file], action_manifests=[manifest]
        )
        self.assertEqual(selection.task_ids, self.task_ids)
        self.assertEqual(selection.expected_commits, (self.commit,))
        self.assertEqual(len(selection.expected_task_modules), 2)

    def test_registered_boundary_action_manifest_schemas(self):
        ch34 = self.root / "ch34.json"
        ch34.write_text(
            json.dumps(
                {
                    "schema": "toy-apollo.ch3-4-boundary-delta-exact-build-action-manifest.v1",
                    "mat_commit": self.commit,
                    "counts": {
                        "unique_exact_build_tasks": 1,
                        "unique_owned_modules": 2,
                    },
                    "unique_exact_build_tasks": [
                        {
                            "task_id": "thm_1_1",
                            "owned_modules": ["P.thm_1_1", "P.thm_1_1_support"],
                            "primary_build_module": "P.thm_1_1",
                        }
                    ],
                    "unique_task_module_actions": [
                        {
                            "task_id": "thm_1_1",
                            "module": "P.thm_1_1",
                            "is_primary": True,
                        },
                        {
                            "task_id": "thm_1_1",
                            "module": "P.thm_1_1_support",
                            "is_primary": False,
                        },
                    ],
                }
            ),
            encoding="utf-8",
        )
        ch914 = self.root / "ch914.json"
        ch914.write_text(
            json.dumps(
                {
                    "schema": "ch9-14.boundary-delta-exact-build-action-manifest.v1",
                    "scope": {"target_commit": self.commit},
                    "counts": {"unique_combined_build_tasks": 1},
                    "unique_combined_build_tasks": [
                        {"task_id": "thm_1_2", "modules": ["P.thm_1_2"]}
                    ],
                }
            ),
            encoding="utf-8",
        )
        first = collect_exact_build_selection(action_manifests=[ch34])
        second = collect_exact_build_selection(action_manifests=[ch914])
        self.assertEqual(first.task_ids, ("thm_1_1",))
        self.assertEqual(
            dict(first.expected_task_modules)["thm_1_1"],
            ("P.thm_1_1", "P.thm_1_1_support"),
        )
        self.assertEqual(second.task_ids, ("thm_1_2",))
        self.assertEqual(second.expected_commits, (self.commit,))

    def test_unknown_action_manifest_schema_fails_closed(self):
        manifest = self.root / "unknown.json"
        manifest.write_text(
            json.dumps({"schema": "unknown.v1", "unique_exact_builds": []}),
            encoding="utf-8",
        )
        with self.assertRaisesRegex(ExactBuildBatchError, "Unsupported action manifest"):
            collect_exact_build_selection(action_manifests=[manifest])

    def test_batches_inventory_once_emit_and_strictly_skip(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        output = root / "evidence"
        completed = subprocess.CompletedProcess(
            args=["lake", "build"], returncode=0, stdout=b"ok", stderr=b""
        )
        expected_task_modules = {
            task_id: tuple(
                sorted(
                    module.module_name
                    for module in catalog.modules
                    if module.owner_task_id == task_id
                )
            )
            for task_id in self.task_ids
        }
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ) as load_mock,
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ) as discover_mock,
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._run", return_value=completed
            ) as run_mock,
            patch(
                "src.toy_apollo.state_exact_build_batch._forbidden_findings",
                return_value=[],
            ),
        ):
            result = emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=self.task_ids,
                checkout=checkout,
                output_root=output,
                batch_size=2,
                expected_commits=[self.commit],
                expected_task_modules=expected_task_modules,
            )
        load_mock.assert_called_once()
        discover_mock.assert_called_once()
        self.assertEqual(run_mock.call_count, 2)
        self.assertEqual(result["emitted"], 3)
        self.assertEqual(result["build_batches"], 2)
        for task_id in self.task_ids:
            receipt_path = output / task_id / "exact_mat_build_receipt_v1.json"
            payload = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(payload["schema"], EXACT_BUILD_SCHEMA)
            self.assertEqual(payload["commit"], self.commit)
            self.assertIn(
                payload["focused_build"]["task_module"],
                payload["focused_build"]["command"],
            )
            self.assertTrue(
                all(payload["focused_build"]["task_modules_in_combined_command"].values())
            )
            self.assertEqual(payload["forbidden_token_scan"]["findings"], {})
            self.assertEqual(payload["lean_tree_equivalence"]["changed_lean_files"], [])
        first = json.loads(
            (output / self.task_ids[0] / "exact_mat_build_receipt_v1.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(len(first["subject_files"]), 2)
        self.assertEqual(len(first["focused_build"]["task_modules"]), 2)
        self.assertIn(
            "ProbabilityTheory.chapter_01.thm_1_1_support",
            first["focused_build"]["command"],
        )

        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as second_run,
        ):
            skipped = emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=self.task_ids,
                checkout=checkout,
                output_root=output,
                batch_size=2,
            )
        second_run.assert_not_called()
        self.assertEqual(skipped["status"], "all_existing")
        self.assertEqual(skipped["skipped_existing"], 3)

    def test_partial_or_mismatched_evidence_fails_before_build(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        output = root / "evidence"
        (output / self.task_ids[0]).mkdir(parents=True)
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as run_mock,
            self.assertRaisesRegex(ExactBuildBatchError, "partial"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        run_mock.assert_not_called()

        receipt = output / self.task_ids[0] / "exact_mat_build_receipt_v1.json"
        receipt.write_text("{}\n", encoding="utf-8")
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as mismatch_run,
            self.assertRaisesRegex(ExactBuildBatchError, "mismatches current MAT"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        mismatch_run.assert_not_called()

    def test_extra_file_in_existing_evidence_is_rejected(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        output = root / "evidence"
        completed = subprocess.CompletedProcess(
            args=["lake", "build"], returncode=0, stdout=b"ok", stderr=b""
        )
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._run", return_value=completed
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._forbidden_findings",
                return_value=[],
            ),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        (output / self.task_ids[0] / "unexpected.json").write_text(
            "{}\n", encoding="utf-8"
        )
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as run_mock,
            self.assertRaisesRegex(ExactBuildBatchError, "unexpected files"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        run_mock.assert_not_called()

    def test_post_build_origin_drift_writes_no_receipts(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        origin_reads = 0

        def drifting_command_text(_repo: Path, *args: str) -> str:
            nonlocal origin_reads
            if args[-1] == "origin/main":
                origin_reads += 1
                return self.commit if origin_reads == 1 else "4" * 40
            if args[-1] == "HEAD":
                return self.commit
            if "status" in args:
                return ""
            raise AssertionError(args)

        completed = subprocess.CompletedProcess(
            args=["lake", "build"], returncode=0, stdout=b"ok", stderr=b""
        )
        output = root / "evidence"
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=drifting_command_text,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._run", return_value=completed
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._forbidden_findings",
                return_value=[],
            ),
            self.assertRaisesRegex(ExactBuildBatchError, "origin/main changed"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        self.assertFalse(output.exists())

    def test_post_build_checkout_drift_writes_no_receipts(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        head_reads = 0

        def drifting_command_text(_repo: Path, *args: str) -> str:
            nonlocal head_reads
            if args[-1] == "origin/main":
                return self.commit
            if args[-1] == "HEAD":
                head_reads += 1
                return self.commit if head_reads == 1 else "4" * 40
            if "status" in args:
                return ""
            raise AssertionError(args)

        completed = subprocess.CompletedProcess(
            args=["lake", "build"], returncode=0, stdout=b"ok", stderr=b""
        )
        output = root / "evidence"
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=drifting_command_text,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._run", return_value=completed
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._forbidden_findings",
                return_value=[],
            ),
            self.assertRaisesRegex(ExactBuildBatchError, "checkout HEAD changed"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=output,
            )
        self.assertFalse(output.exists())

    def test_action_manifest_commit_mismatch_fails_before_build(self):
        root = self.root
        workspace, runtime, checkout, _subjects, catalog = self._fixture(root)
        manifest = root / "actions.json"
        manifest.write_text(
            json.dumps(
                {
                    "schema": "toy-apollo.resolved-invalidation-action-manifest.v1",
                    "mat_commit": "4" * 40,
                    "counts": {
                        "unique_exact_build_tasks": 1,
                        "unique_owned_modules": 2,
                        "unique_primary_build_modules": 1,
                    },
                    "unique_exact_builds": [
                        {
                            "task_id": self.task_ids[0],
                            "owned_modules": [
                                "ProbabilityTheory.chapter_01.thm_1_1",
                                "ProbabilityTheory.chapter_01.thm_1_1_support",
                            ],
                            "primary_build_module": "ProbabilityTheory.chapter_01.thm_1_1",
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        selection = collect_exact_build_selection(action_manifests=[manifest])
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as run_mock,
            self.assertRaisesRegex(ExactBuildBatchError, "manifest commit"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=selection.task_ids,
                checkout=checkout,
                output_root=root / "evidence",
                expected_commits=selection.expected_commits,
            )
        run_mock.assert_not_called()

    def test_declared_owned_modules_must_match_catalog(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch("src.toy_apollo.state_exact_build_batch._run") as run_mock,
            self.assertRaisesRegex(ExactBuildBatchError, "owned modules"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=[self.task_ids[0]],
                checkout=checkout,
                output_root=root / "evidence",
                expected_task_modules={
                    self.task_ids[0]: ("ProbabilityTheory.chapter_01.thm_1_1",)
                },
            )
        run_mock.assert_not_called()

    def test_crlf_subject_identity_uses_catalog_canonicalization(self):
        path = "ProbabilityTheory/chapter_01/thm_1_1.lean"
        common = {
            "task_id": self.task_ids[0],
            "primary_path": path,
            "source_repo": "mat",
            "source_commit": self.commit,
            "layout": "mat",
            "subject_kind": "catalog_git_bundle",
        }
        lf = SubjectBundle.from_files(
            files={path: "theorem x : True := by\n  trivial\n"}, **common
        )
        crlf = SubjectBundle.from_files(
            files={path: b"theorem x : True := by\r\n  trivial\r\n"}, **common
        )
        self.assertEqual(crlf.subject_id, lf.subject_id)
        self.assertEqual(crlf.bundle_hash, lf.bundle_hash)
        self.assertEqual(crlf.primary_hash, lf.primary_hash)
        self.assertEqual(crlf.manifest(), lf.manifest())

    def test_failed_combined_build_writes_no_receipts(self):
        root = self.root
        workspace, runtime, checkout, subjects, catalog = self._fixture(root)
        output = root / "evidence"
        failed = subprocess.CompletedProcess(
            args=["lake", "build"], returncode=1, stdout=b"", stderr=b"boom"
        )
        with (
            patch(
                "src.toy_apollo.state_exact_build_batch.load_catalog",
                return_value=catalog,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch.discover_catalog_git_subjects",
                return_value=subjects,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._command_text",
                side_effect=self._command_text,
            ),
            patch(
                "src.toy_apollo.state_exact_build_batch._run", return_value=failed
            ),
            self.assertRaisesRegex(ExactBuildBatchError, "Combined exact build batch"),
        ):
            emit_current_exact_builds_batch(
                workspace_root=workspace,
                runtime_root=runtime,
                task_ids=self.task_ids,
                checkout=checkout,
                output_root=output,
                batch_size=2,
            )
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
