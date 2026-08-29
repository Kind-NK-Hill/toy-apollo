from __future__ import annotations

import json
import shutil
import subprocess
import unittest
import uuid
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from src.toy_apollo.state_store import SubjectBundle, sha256_file
from tools.mat_catalog_review_apply import (
    ApplyError,
    _revalidate_current_subject_before_state_mutation,
    _validate_build_receipt,
    _validate_build_receipt_provenance,
    apply_review,
)
from tools.mat_catalog_review_prepare import PrepareError, prepare_review


class PrebuiltExactBuildReceiptTests(unittest.TestCase):
    commit = "3" * 40
    task_id = "thm_1_1"
    primary_module = "ProbabilityTheory.chapter_01.thm_1_1"
    support_module = primary_module + "_support"

    def setUp(self):
        root = (
            Path(__file__).resolve().parents[2]
            / "_analysis_tmp"
            / "test_mat_catalog_review_prebuilt_receipt"
            / uuid.uuid4().hex
        )
        root.mkdir(parents=True)
        self.root = root
        self.addCleanup(shutil.rmtree, root)
        self.workspace = root / "workspace"
        self.runtime = self.workspace / "toy-apollo"
        self.build_root = root / "clean-checkout"
        self.pack = root / "pack"
        self.runtime.mkdir(parents=True)
        self.build_root.mkdir()
        primary_path = self.primary_module.replace(".", "/") + ".lean"
        support_path = self.support_module.replace(".", "/") + ".lean"
        self.primary_code = "theorem main_result : True := by trivial\n"
        self.subject = SubjectBundle.from_files(
            task_id=self.task_id,
            files={
                primary_path: self.primary_code,
                support_path: "theorem support_result : True := by trivial\n",
            },
            primary_path=primary_path,
            source_repo="mat",
            source_commit=self.commit,
            layout="mat",
            subject_kind="catalog_git_bundle",
        )
        exact_primary = self.build_root / primary_path
        exact_primary.parent.mkdir(parents=True)
        exact_primary.write_text(self.primary_code, encoding="utf-8", newline="")
        self.catalog = SimpleNamespace(
            mat_commit=self.commit,
            catalog_id="fixture-catalog",
            modules=[
                SimpleNamespace(
                    owner_task_id=self.task_id,
                    module_role="primary",
                    module_name=self.primary_module,
                ),
                SimpleNamespace(
                    owner_task_id=self.task_id,
                    module_role="owned_support",
                    module_name=self.support_module,
                ),
            ],
        )
        self.receipt_path = (root / "prebuilt" / "receipt.json").resolve()
        self.receipt_path.parent.mkdir()
        self.receipt_path.write_text(
            json.dumps(self._receipt(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def _receipt(self) -> dict:
        modules = [self.primary_module, self.support_module]
        return {
            "schema": "mat.catalog.exact-build.v1",
            "campaign_id": "fixture",
            "task_id": self.task_id,
            "commit": self.commit,
            "subject_id": self.subject.subject_id,
            "bundle_hash": self.subject.bundle_hash,
            "primary_hash": self.subject.primary_hash,
            "primary_path": self.subject.primary_path,
            "subject_files": self.subject.manifest(),
            "success": True,
            "exit_code": 0,
            "focused_build": {
                "command": ["lake", "build", *modules],
                "task_module": self.primary_module,
                "task_module_in_combined_command": True,
                "task_modules": modules,
                "task_modules_in_combined_command": {
                    module: True for module in modules
                },
                "batch_index": 1,
                "batch_size": 1,
                "cwd": str(self.build_root.resolve()),
                "exit_code": 0,
                "duration_seconds": 1.0,
                "stdout": "ok",
                "stderr": "",
            },
            "forbidden_token_scan": {
                "exit_code": 0,
                "findings": {},
                "tokens": ["admit", "axiom", "native_decide", "sorry"],
            },
            "lean_tree_equivalence": {
                "build_commit": self.commit,
                "target_commit": self.commit,
                "changed_lean_files": [],
                "build_checkout_clean": True,
            },
            "created_at": "2026-08-08T00:00:00+00:00",
        }

    def _artifact_result(self) -> dict[str, str]:
        paths = {
            "review_input_file": self.pack / "review_input.json",
            "review_request_file": self.pack / "review_request.json",
            "review_prompt_file": self.pack / "review_prompt.md",
            "review_context_file": self.pack / "review_context.md",
            "review_result_template_file": self.pack / "result_template.json",
            "expected_review_result_file": self.pack / "result.json",
        }
        self.pack.mkdir(parents=True, exist_ok=True)
        for key, path in paths.items():
            if key == "review_input_file":
                path.write_text("{}\n", encoding="utf-8")
            else:
                path.write_text("fixture\n", encoding="utf-8")
        return {key: str(path.resolve()) for key, path in paths.items()}

    def _git_text(self, _repo: Path, *args: str) -> str:
        if args[-1] in {"origin/main", "HEAD"}:
            return self.commit
        if "status" in args:
            return ""
        raise AssertionError(args)

    def test_prepare_reuses_absolute_receipt_without_build(self):
        artifacts = self._artifact_result()
        empty_diff = subprocess.CompletedProcess(
            args=["git", "diff"], returncode=0, stdout=b"", stderr=b""
        )
        with (
            patch("tools.mat_catalog_review_prepare.load_catalog", return_value=self.catalog),
            patch(
                "tools.mat_catalog_review_prepare._git_text", side_effect=self._git_text
            ),
            patch("tools.mat_catalog_review_prepare._git", return_value=empty_diff),
            patch(
                "tools.mat_catalog_review_prepare._catalog_subject",
                return_value=self.subject,
            ),
            patch(
                "tools.mat_catalog_review_prepare._pinned_task",
                return_value=SimpleNamespace(task_id=self.task_id),
            ),
            patch("tools.mat_catalog_review_prepare._focused_build") as focused_build,
            patch(
                "tools.mat_catalog_review_prepare._forbidden_findings", return_value={}
            ),
            patch("tools.mat_catalog_review_prepare._direct_consumers", return_value=[]),
            patch(
                "tools.mat_catalog_review_prepare.git_file_at_ref",
                return_value=self.primary_code.encode(),
            ),
            patch("tools.mat_catalog_review_prepare.get_settings", return_value=object()),
            patch(
                "tools.mat_catalog_review_prepare.open_runtime_ledger",
                return_value=object(),
            ),
            patch(
                "tools.mat_catalog_review_prepare._write_codex_handoff_review_artifacts",
                return_value=artifacts,
            ),
        ):
            result = prepare_review(
                task_id=self.task_id,
                attempt=1,
                pack_dir=self.pack,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                build_root=self.build_root,
                prebuilt_exact_build_receipt=self.receipt_path,
            )
        focused_build.assert_not_called()
        copied = self.pack / "exact_mat_build_receipt_v1.json"
        self.assertEqual(copied.read_bytes(), self.receipt_path.read_bytes())
        self.assertEqual(result["build_receipt_mode"], "reused_prebuilt")
        self.assertEqual(result["build_result_hash"], sha256_file(self.receipt_path))
        self.assertEqual(
            result["prebuilt_exact_build_receipt_source"], str(self.receipt_path)
        )
        self.assertEqual(
            result["prebuilt_exact_build_receipt_source_hash"],
            sha256_file(self.receipt_path),
        )

    def test_prepare_rejects_relative_prebuilt_path_without_build(self):
        with self.assertRaisesRegex(PrepareError, "must be absolute"):
            prepare_review(
                task_id=self.task_id,
                attempt=1,
                pack_dir=self.pack,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                build_root=self.build_root,
                prebuilt_exact_build_receipt=Path("relative.json"),
            )

    def test_prepare_rejects_prebuilt_receipt_for_candidate(self):
        with self.assertRaisesRegex(PrepareError, "cannot be used for candidates"):
            prepare_review(
                task_id=self.task_id,
                attempt=1,
                pack_dir=self.pack,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                build_root=self.build_root,
                candidate_root=self.build_root,
                prebuilt_exact_build_receipt=self.receipt_path,
            )

    def test_apply_provenance_binds_source_and_pack_copy_hash(self):
        receipt_hash = sha256_file(self.receipt_path)
        source = str(self.receipt_path.resolve())
        checkout = str(self.build_root.resolve())
        metadata = {
            "build_receipt_mode": "reused_prebuilt",
            "build_result_hash": receipt_hash,
            "build_result_file": "pack-receipt.json",
            "build_checkout": checkout,
            "prebuilt_exact_build_receipt_source": source,
            "prebuilt_exact_build_receipt_source_hash": receipt_hash,
        }
        review_input = {
            "review_basis": {
                "build_receipt_mode": "reused_prebuilt",
                "build_checkout": checkout,
                "external_subject": {
                    "focused_build_receipt": "pack-receipt.json",
                    "focused_build_receipt_hash": receipt_hash,
                },
                "prebuilt_exact_build_receipt_source": source,
                "prebuilt_exact_build_receipt_source_hash": receipt_hash,
            }
        }
        _validate_build_receipt_provenance(
            metadata=metadata,
            review_input=review_input,
            actual_build_hash=receipt_hash,
        )
        metadata["prebuilt_exact_build_receipt_source_hash"] = "0" * 64
        with self.assertRaisesRegex(ApplyError, "source/copy"):
            _validate_build_receipt_provenance(
                metadata=metadata,
                review_input=review_input,
                actual_build_hash=receipt_hash,
            )
        built_metadata = {
            "build_receipt_mode": "built_during_prepare",
            "build_result_hash": receipt_hash,
            "build_result_file": "pack-receipt.json",
            "build_checkout": checkout,
            "prebuilt_exact_build_receipt_source": source,
        }
        with self.assertRaisesRegex(ApplyError, "stray prebuilt"):
            _validate_build_receipt_provenance(
                metadata=built_metadata,
                review_input={
                    "review_basis": {
                        "build_receipt_mode": "built_during_prepare",
                        "build_checkout": checkout,
                        "external_subject": {
                            "focused_build_receipt": "pack-receipt.json",
                            "focused_build_receipt_hash": receipt_hash,
                        },
                    }
                },
                actual_build_hash=receipt_hash,
            )

    def test_apply_shared_validator_rechecks_support_and_forbidden_shape(self):
        metadata = {
            "schema": "mat.catalog.exact-review-pack.v1",
            "build_checkout": str(self.build_root.resolve()),
        }
        _validate_build_receipt(
            self.receipt_path,
            metadata=metadata,
            subject=self.subject,
            catalog=self.catalog,
        )
        with self.assertRaisesRegex(ApplyError, "build_checkout must be absolute"):
            _validate_build_receipt(
                self.receipt_path,
                metadata={
                    "schema": "mat.catalog.exact-review-pack.v1",
                    "build_checkout": "relative-checkout",
                },
                subject=self.subject,
                catalog=self.catalog,
            )
        receipt = self._receipt()
        receipt["focused_build"]["task_modules"] = [self.primary_module]
        self.receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        with self.assertRaisesRegex(ApplyError, "combined build binding"):
            _validate_build_receipt(
                self.receipt_path,
                metadata=metadata,
                subject=self.subject,
                catalog=self.catalog,
            )
        receipt = self._receipt()
        receipt["forbidden_token_scan"]["findings"] = []
        self.receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        with self.assertRaisesRegex(ApplyError, "forbidden scan"):
            _validate_build_receipt(
                self.receipt_path,
                metadata=metadata,
                subject=self.subject,
                catalog=self.catalog,
            )

    def test_ordinary_prepare_rejects_origin_head_or_dirty_during_build(self):
        focused = {
            "command": ["lake", "build", self.primary_module, self.support_module],
            "cwd": str(self.build_root.resolve()),
            "exit_code": 0,
            "duration_seconds": 1.0,
            "stdout": "ok",
            "stderr": "",
        }
        empty_diff = subprocess.CompletedProcess(
            args=["git", "diff"], returncode=0, stdout=b"", stderr=b""
        )
        for drift, message in (
            ("origin", "origin/main changed"),
            ("head", "checkout HEAD changed"),
            ("dirty", "checkout became dirty"),
        ):
            with self.subTest(drift=drift):
                reads = {"origin": 0, "head": 0, "status": 0}

                def git_text(_repo: Path, *args: str) -> str:
                    if args[-1] == "origin/main":
                        reads["origin"] += 1
                        if drift == "origin" and reads["origin"] > 1:
                            return "4" * 40
                        return self.commit
                    if args[-1] == "HEAD":
                        reads["head"] += 1
                        if drift == "head" and reads["head"] > 1:
                            return "4" * 40
                        return self.commit
                    if "status" in args:
                        reads["status"] += 1
                        if drift == "dirty" and reads["status"] > 1:
                            return "?? drift.lean"
                        return ""
                    raise AssertionError(args)

                with (
                    patch(
                        "tools.mat_catalog_review_prepare.load_catalog",
                        return_value=self.catalog,
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._git_text",
                        side_effect=git_text,
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._git", return_value=empty_diff
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._catalog_subject",
                        return_value=self.subject,
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._pinned_task",
                        return_value=SimpleNamespace(task_id=self.task_id),
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._focused_build",
                        return_value=focused,
                    ),
                    patch(
                        "tools.mat_catalog_review_prepare._forbidden_findings",
                        return_value={},
                    ),
                    self.assertRaisesRegex(PrepareError, message),
                ):
                    prepare_review(
                        task_id=self.task_id,
                        attempt=1,
                        pack_dir=self.root / f"pack-{drift}",
                        workspace_root=self.workspace,
                        runtime_root=self.runtime,
                        build_root=self.build_root,
                    )
                self.assertFalse(
                    (self.root / f"pack-{drift}" / "mat_exact_subject.json").exists()
                )

    def test_apply_origin_drift_causes_zero_state_writes(self):
        self.pack.mkdir(parents=True, exist_ok=True)
        (self.pack / "mat_exact_subject.json").write_text("{}\n", encoding="utf-8")
        input_path = self.root / "review_input.json"
        input_path.write_text("{}\n", encoding="utf-8")
        result_path = self.root / "semantic_review_result.json"
        result_path.write_text("{}\n", encoding="utf-8")
        review_input = {"task_id": self.task_id}
        decision = SimpleNamespace(
            is_semantic_verdict=True,
            task_status_projection=SimpleNamespace(task_status="pass"),
            is_clean_pass=True,
            result={
                "verdict": "pass",
                "proof_class": "direct",
                "completion_class": "complete",
                "reviewer_independence": {
                    "read_only": True,
                    "did_edit_candidate": False,
                },
            },
        )
        store = MagicMock()
        store.assert_integrity = MagicMock()
        store.task_report.return_value = {
            "heads": {
                "mat_main": {
                    "subject_id": self.subject.subject_id,
                    "bundle_hash": self.subject.bundle_hash,
                }
            }
        }
        origin_reads = 0

        def git_text(_repo: Path, *args: str) -> str:
            nonlocal origin_reads
            if args[-1] == "origin/main":
                origin_reads += 1
                return self.commit if origin_reads == 1 else "4" * 40
            raise AssertionError(args)

        with (
            patch("tools.mat_catalog_review_apply.load_catalog", return_value=self.catalog),
            patch("tools.mat_catalog_review_apply._git_text", side_effect=git_text),
            patch(
                "tools.mat_catalog_review_apply._catalog_subject",
                return_value=self.subject,
            ),
            patch(
                "tools.mat_catalog_review_apply._validate_pack",
                return_value=(review_input, input_path, result_path),
            ),
            patch(
                "tools.mat_catalog_review_apply.evaluate_semantic_review_result",
                return_value=decision,
            ),
            patch(
                "tools.mat_catalog_review_apply.render_semantic_review_report",
                return_value="report",
            ),
            patch(
                "tools.mat_catalog_review_apply.WorkspaceStateStore",
                return_value=store,
            ),
            self.assertRaisesRegex(ApplyError, "origin/main changed"),
        ):
            apply_review(
                task_id=self.task_id,
                pack_dir=self.pack,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                state_path=self.root / "state.sqlite3",
            )
        store.upsert_subject.assert_not_called()
        store.record_review.assert_not_called()

    def test_candidate_apply_freshness_rechecks_current_parent(self):
        with (
            patch(
                "tools.mat_catalog_review_apply._git_text", return_value=self.commit
            ),
            patch(
                "tools.mat_catalog_review_apply._catalog_subject",
                return_value=self.subject,
            ) as catalog_subject,
        ):
            _revalidate_current_subject_before_state_mutation(
                catalog=self.catalog,
                mat_repo=self.workspace / "MAT3280-formalization-output",
                task_id=self.task_id,
                expected_parent=self.subject,
            )
        catalog_subject.assert_called_once()

if __name__ == "__main__":
    unittest.main()
