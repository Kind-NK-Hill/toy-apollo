from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.toy_apollo.state_cli import _batch_task_ids, build_parser
from src.toy_apollo.state_migration import (
    MigrationReport,
    import_validated_transformation_receipt,
)
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore
from src.toy_apollo.state_transformation_receipt import (
    TransformationReceiptError,
    _revalidate_emit_heads,
    emit_validated_transformation,
    emit_validated_transformations_batch,
    inspect_validated_transformation,
)


class TransformationReceiptCliTests(unittest.TestCase):
    task_id = "thm_1_1"
    mat_commit = "b" * 40
    evidence_hash = "e" * 64

    def _subjects(self, *, changed: bool = False) -> tuple[SubjectBundle, SubjectBundle]:
        source_text = "theorem t : True := by trivial\n"
        source = SubjectBundle.from_files(
            task_id=self.task_id,
            files={"review/thm_1_1.lean": source_text},
            primary_path="review/thm_1_1.lean",
            source_repo="mat",
            source_commit="a" * 40,
            layout="review",
            subject_kind="review_input_bundle",
        )
        target = SubjectBundle.from_files(
            task_id=self.task_id,
            files={
                "chapter_01/thm_1_1.lean": (
                    "theorem t : True := by exact True.intro\n" if changed else source_text
                )
            },
            primary_path="chapter_01/thm_1_1.lean",
            source_repo="mat",
            source_commit=self.mat_commit,
            layout="mat",
            subject_kind="git_bundle",
        )
        return source, target

    def _seed(
        self,
        store: WorkspaceStateStore,
        source: SubjectBundle,
        target: SubjectBundle,
    ) -> str:
        store.initialize()
        with store._connection(write=True) as connection:
            connection.execute(
                """
                INSERT INTO catalog_versions(
                    catalog_id, schema_version, catalog_name, toy_commit, mat_commit,
                    manifest_sha256, plan_set_sha256, policy_sha256, counts_json,
                    payload_json, imported_at
                ) VALUES ('catalog', 'test', 'test', ?, ?, ?, ?, ?, '{}', '{}', ?)
                """,
                (
                    "a" * 40,
                    self.mat_commit,
                    "1" * 64,
                    "2" * 64,
                    "3" * 64,
                    "2026-08-08T00:00:00+00:00",
                ),
            )
            connection.execute(
                "INSERT INTO meta(key, value) VALUES('active_catalog_id', 'catalog')"
            )
        store.upsert_subject(source)
        store.upsert_subject(target)
        review_id = store.record_review(
            task_id=self.task_id,
            subject_id=source.subject_id,
            verdict="pass",
            proof_class="faithful",
            completion_class="complete",
            phase2_status="pass",
            evidence_path="review.json",
            evidence_hash=self.evidence_hash,
            authority_eligible=True,
            prompt_version=11,
            rubric_version=9,
            reviewed_at="2026-08-07T00:00:00+00:00",
        )
        store.set_task_head(
            task_id=self.task_id,
            role="mat_main",
            subject_id=target.subject_id,
            freshness="fresh",
        )
        return review_id

    def _catalog(self):
        return SimpleNamespace(
            catalog_id="catalog",
            mat_commit=self.mat_commit,
            task_ids=lambda: (self.task_id,),
            modules=(
                SimpleNamespace(
                    owner_task_id=self.task_id,
                    module_role="primary",
                    module_name="ProbabilityTheory.chapter_01.thm_1_1",
                ),
            ),
        )

    def test_parser_exposes_inspect_and_emit(self):
        parser = build_parser()
        inspected = parser.parse_args(
            ["state", "transformation", "inspect", "--task", self.task_id]
        )
        emitted = parser.parse_args(
            [
                "state",
                "transformation",
                "emit",
                "--task",
                self.task_id,
                "--output-dir",
                "evidence",
            ]
        )
        batch = parser.parse_args(
            [
                "state",
                "transformation",
                "emit-batch",
                "--task",
                self.task_id,
                "--output-dir",
                "evidence",
            ]
        )
        self.assertEqual(inspected.transformation_command, "inspect")
        self.assertEqual(emitted.transformation_command, "emit")
        self.assertEqual(batch.transformation_command, "emit-batch")

    def test_batch_task_file_accepts_json_and_lines(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            json_path = root / "tasks.json"
            text_path = root / "tasks.txt"
            json_path.write_text(json.dumps(["thm_1_2", "thm_1_1"]), encoding="utf-8")
            text_path.write_text("# tasks\nthm_1_2, thm_1_1\n", encoding="utf-8")
            self.assertEqual(
                _batch_task_ids([], json_path), ["thm_1_1", "thm_1_2"]
            )
            self.assertEqual(
                _batch_task_ids([], text_path), ["thm_1_1", "thm_1_2"]
            )

    def test_inspect_binds_catalog_origin_main_and_path_only_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MAT3280-formalization-output" / ".git").mkdir(parents=True)
            source, target = self._subjects()
            store = WorkspaceStateStore(root / "state.sqlite3")
            review_id = self._seed(store, source, target)

            def git_text(_repo, *argv):
                if argv[-1] == "origin/main" or argv[-1] == "HEAD":
                    return self.mat_commit
                return ""

            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt.load_catalog",
                    return_value=self._catalog(),
                ),
                patch(
                    "src.toy_apollo.state_transformation_receipt._command_text",
                    side_effect=git_text,
                ),
                patch(
                    "src.toy_apollo.state_transformation_receipt.discover_catalog_git_subjects",
                    return_value={self.task_id: target},
                ),
            ):
                result = inspect_validated_transformation(
                    store=store,
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_id=self.task_id,
                )

            self.assertEqual(result["status"], "eligible")
            self.assertEqual(result["catalog_mat_commit"], self.mat_commit)
            self.assertEqual(result["source_review"]["review_id"], review_id)
            self.assertEqual(result["comparison"]["classification"], "path_only_relocation")

    def test_inspect_rejects_primary_delta_and_stale_origin(self):
        for case in ("primary_delta", "stale_origin"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "MAT3280-formalization-output" / ".git").mkdir(parents=True)
                source, target = self._subjects(changed=case == "primary_delta")
                store = WorkspaceStateStore(root / "state.sqlite3")
                self._seed(store, source, target)

                def git_text(_repo, *argv):
                    if argv[-1] == "origin/main":
                        return "c" * 40 if case == "stale_origin" else self.mat_commit
                    if argv[-1] == "HEAD":
                        return self.mat_commit
                    return ""

                with (
                    patch(
                        "src.toy_apollo.state_transformation_receipt.load_catalog",
                        return_value=self._catalog(),
                    ),
                    patch(
                        "src.toy_apollo.state_transformation_receipt._command_text",
                        side_effect=git_text,
                    ),
                    patch(
                        "src.toy_apollo.state_transformation_receipt.discover_catalog_git_subjects",
                        return_value={self.task_id: target},
                    ),
                    self.assertRaises(TransformationReceiptError),
                ):
                    inspect_validated_transformation(
                        store=store,
                        workspace_root=root,
                        runtime_root=root / "toy-apollo",
                        task_id=self.task_id,
                    )

    def test_emit_writes_importable_immutable_evidence_without_sqlite_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, target = self._subjects()
            store = WorkspaceStateStore(root / "state.sqlite3")
            review_id = self._seed(store, source, target)
            inspection = {
                "schema": "toy-apollo.validated-transformation-inspection.v1",
                "status": "eligible",
                "task_id": self.task_id,
                "catalog_id": "catalog",
                "catalog_mat_commit": self.mat_commit,
                "mat_origin_main": self.mat_commit,
                "mat_head": self.mat_commit,
                "mat_repo": str(root / "MAT3280-formalization-output"),
                "build_checkout": str(root / "MAT3280-formalization-output"),
                "source_review": {
                    "review_id": review_id,
                    "evidence_hash": self.evidence_hash,
                    "prompt_version": 11,
                    "rubric_version": 9,
                    "reviewed_at": "2026-08-07T00:00:00+00:00",
                },
                "source_subject": {
                    "task_id": source.task_id,
                    "subject_id": source.subject_id,
                    "subject_kind": source.subject_kind,
                    "source_repo": source.source_repo,
                    "source_commit": source.source_commit,
                    "layout": source.layout,
                    "bundle_hash": source.bundle_hash,
                    "primary_hash": source.primary_hash,
                    "primary_path": source.primary_path,
                    "files": source.manifest(),
                },
                "target_subject": {
                    "task_id": target.task_id,
                    "subject_id": target.subject_id,
                    "subject_kind": target.subject_kind,
                    "source_repo": target.source_repo,
                    "source_commit": target.source_commit,
                    "layout": target.layout,
                    "bundle_hash": target.bundle_hash,
                    "primary_hash": target.primary_hash,
                    "primary_path": target.primary_path,
                    "files": target.manifest(),
                },
                "comparison": {
                    "classification": "path_only_relocation",
                    "primary_equal": True,
                    "content_multiset_equal": True,
                },
                "focused_build": {"command": ["lake", "build", "ProbabilityTheory.thm_1_1"]},
                "forbidden_tokens": ["admit", "axiom", "native_decide", "sorry"],
            }
            before = store.path.read_bytes()
            output = root / "evidence"
            completed = subprocess.CompletedProcess(
                args=["lake", "build"], returncode=0, stdout=b"ok\n", stderr=b""
            )
            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt.inspect_validated_transformation",
                    return_value=inspection,
                ),
                patch("src.toy_apollo.state_transformation_receipt._run", return_value=completed),
                patch(
                    "src.toy_apollo.state_transformation_receipt._forbidden_findings",
                    return_value=[],
                ),
                patch("src.toy_apollo.state_transformation_receipt._revalidate_emit_heads"),
            ):
                result = emit_validated_transformation(
                    store=store,
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_id=self.task_id,
                    output_dir=output,
                )
            self.assertEqual(store.path.read_bytes(), before)
            receipt_path = Path(result["receipt"])
            import_validated_transformation_receipt(
                store,
                receipt_path,
                MigrationReport(database=str(store.path)),
            )
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM transformations").fetchone()[0], 1)

            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt.inspect_validated_transformation",
                    return_value=inspection,
                ),
                patch("src.toy_apollo.state_transformation_receipt._run", return_value=completed),
                patch(
                    "src.toy_apollo.state_transformation_receipt._forbidden_findings",
                    return_value=[],
                ),
                patch("src.toy_apollo.state_transformation_receipt._revalidate_emit_heads"),
                self.assertRaises(TransformationReceiptError),
            ):
                emit_validated_transformation(
                    store=store,
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_id=self.task_id,
                    output_dir=output,
                )
            self.assertTrue(receipt_path.is_file())

    def test_failed_build_emits_no_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "evidence"
            inspection = {
                "task_id": self.task_id,
                "mat_repo": str(root / "MAT3280-formalization-output"),
                "build_checkout": str(root / "MAT3280-formalization-output"),
                "target_subject": {},
                "focused_build": {"command": ["lake", "build", "ProbabilityTheory.thm_1_1"]},
            }
            failed = subprocess.CompletedProcess(
                args=["lake", "build"], returncode=1, stdout=b"", stderr=b"failure"
            )
            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt.inspect_validated_transformation",
                    return_value=inspection,
                ),
                patch("src.toy_apollo.state_transformation_receipt._run", return_value=failed),
                self.assertRaises(TransformationReceiptError),
            ):
                emit_validated_transformation(
                    store=WorkspaceStateStore(root / "unused.sqlite3"),
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_id=self.task_id,
                    output_dir=output,
                )
            self.assertFalse(output.exists())

    def test_emit_head_revalidation_rejects_concurrent_origin_change(self):
        inspection = {
            "mat_repo": "mat",
            "build_checkout": "checkout",
            "catalog_mat_commit": self.mat_commit,
        }
        with (
            patch(
                "src.toy_apollo.state_transformation_receipt._command_text",
                return_value="c" * 40,
            ),
            self.assertRaisesRegex(TransformationReceiptError, "origin/main changed"),
        ):
            _revalidate_emit_heads(inspection)

    def test_emit_batch_builds_once_and_skips_valid_existing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "evidence"
            inspections = []
            for index, task_id in enumerate(("thm_1_1", "thm_1_2"), start=1):
                content_hash = f"{index}" * 64
                git_hash = f"{index}" * 40
                source_path = f"old/{task_id}.lean"
                target_path = f"ProbabilityTheory/chapter_01/{task_id}.lean"
                source_files = [
                    {
                        "path": source_path,
                        "content_sha256": content_hash,
                        "git_blob_sha": git_hash,
                        "size": 10,
                    }
                ]
                target_files = [dict(source_files[0], path=target_path)]
                source_subject = {
                    "task_id": task_id,
                    "subject_id": f"{index + 2}" * 64,
                    "subject_kind": "review_input_bundle",
                    "source_repo": "mat",
                    "source_commit": "a" * 40,
                    "layout": "review",
                    "bundle_hash": f"{index + 4}" * 64,
                    "primary_hash": content_hash,
                    "primary_path": source_path,
                    "files": source_files,
                }
                target_subject = {
                    "task_id": task_id,
                    "subject_id": f"{index + 6}" * 64,
                    "subject_kind": "catalog_git_bundle",
                    "source_repo": "mat",
                    "source_commit": self.mat_commit,
                    "layout": "mat",
                    "bundle_hash": f"{index + 8}" * 64,
                    "primary_hash": content_hash,
                    "primary_path": target_path,
                    "files": target_files,
                }
                inspections.append(
                    {
                        "task_id": task_id,
                        "catalog_id": "catalog",
                        "catalog_mat_commit": self.mat_commit,
                        "mat_repo": str(root / "MAT3280-formalization-output"),
                        "build_checkout": str(root / "checkout"),
                        "source_review": {
                            "review_id": f"{index + 1}" * 64,
                            "evidence_hash": f"{index + 3}" * 64,
                            "prompt_version": 11,
                            "rubric_version": 9,
                            "reviewed_at": "2026-08-08T00:00:00+00:00",
                        },
                        "source_subject": source_subject,
                        "target_subject": target_subject,
                        "focused_build": {
                            "command": ["lake", "build", f"ProbabilityTheory.chapter_01.{task_id}"]
                        },
                    }
                )
            completed = subprocess.CompletedProcess(
                args=["lake", "build"], returncode=0, stdout=b"ok", stderr=b""
            )
            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt._inspect_validated_transformations",
                    return_value=inspections,
                ) as inspect_mock,
                patch(
                    "src.toy_apollo.state_transformation_receipt._run", return_value=completed
                ) as run_mock,
                patch(
                    "src.toy_apollo.state_transformation_receipt._forbidden_findings",
                    return_value=[],
                ),
                patch("src.toy_apollo.state_transformation_receipt._revalidate_emit_heads"),
            ):
                result = emit_validated_transformations_batch(
                    store=WorkspaceStateStore(root / "unused.sqlite3"),
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_ids=["thm_1_1", "thm_1_2"],
                    output_dir=output,
                )
            inspect_mock.assert_called_once()
            run_mock.assert_called_once()
            self.assertEqual(result["emitted"], 2)
            self.assertEqual(result["skipped_existing"], 0)
            self.assertEqual(len(list(output.rglob("*.json"))), 6)
            for task_id in ("thm_1_1", "thm_1_2"):
                build = json.loads(
                    (
                        output
                        / task_id
                        / f"validated_transformation_build_{task_id}.json"
                    ).read_text(
                        encoding="utf-8"
                    )
                )
                self.assertIn(f"ProbabilityTheory.chapter_01.{task_id}", build["command"])

            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt._inspect_validated_transformations",
                    return_value=inspections,
                ),
                patch("src.toy_apollo.state_transformation_receipt._run") as second_run,
            ):
                skipped = emit_validated_transformations_batch(
                    store=WorkspaceStateStore(root / "unused.sqlite3"),
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_ids=["thm_1_1", "thm_1_2"],
                    output_dir=output,
                )
            second_run.assert_not_called()
            self.assertEqual(skipped["status"], "all_existing")
            self.assertEqual(skipped["skipped_existing"], 2)

            (
                output
                / "thm_1_1"
                / "validated_transformation_forbidden_scan_thm_1_1.json"
            ).unlink()
            with (
                patch(
                    "src.toy_apollo.state_transformation_receipt._inspect_validated_transformations",
                    return_value=inspections,
                ),
                patch("src.toy_apollo.state_transformation_receipt._run") as partial_run,
                self.assertRaisesRegex(TransformationReceiptError, "partial"),
            ):
                emit_validated_transformations_batch(
                    store=WorkspaceStateStore(root / "unused.sqlite3"),
                    workspace_root=root,
                    runtime_root=root / "toy-apollo",
                    task_ids=["thm_1_1", "thm_1_2"],
                    output_dir=output,
                )
            partial_run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
