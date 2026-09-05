from __future__ import annotations

import json
import sqlite3
import tempfile
import unittest
from contextlib import closing
from pathlib import Path
from unittest.mock import patch

from formalization_engine.state_bundle_delta import analyze_current_mat_bundles
from formalization_engine.state_migration import (
    MigrationReport,
    import_validated_transformation_receipt,
    rebuild_workspace_database,
)
from formalization_engine.state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
)


class ValidatedTransformationReceiptTests(unittest.TestCase):
    task_id = "thm_1_1"
    mat_commit = "b" * 40
    review_evidence_hash = "e" * 64

    @staticmethod
    def _subject_payload(subject: SubjectBundle) -> dict[str, object]:
        return {
            "task_id": subject.task_id,
            "subject_id": subject.subject_id,
            "subject_kind": subject.subject_kind,
            "source_repo": subject.source_repo,
            "source_commit": subject.source_commit,
            "layout": subject.layout,
            "bundle_hash": subject.bundle_hash,
            "primary_hash": subject.primary_hash,
            "primary_path": subject.primary_path,
            "files": subject.manifest(),
        }

    def _subjects(self, *, target_content: str | None = None) -> tuple[SubjectBundle, SubjectBundle]:
        source_content = "theorem t : True := by trivial\n"
        source = SubjectBundle.from_files(
            task_id=self.task_id,
            files={"review/thm_1_1.lean": source_content},
            primary_path="review/thm_1_1.lean",
            source_repo="mat",
            source_commit="a" * 40,
            layout="review",
            subject_kind="review_input_bundle",
        )
        target = SubjectBundle.from_files(
            task_id=self.task_id,
            files={"chapter_01/thm_1_1.lean": target_content or source_content},
            primary_path="chapter_01/thm_1_1.lean",
            source_repo="mat",
            source_commit=self.mat_commit,
            layout="mat_main",
            subject_kind="mat_main",
        )
        return source, target

    def _install_active_catalog(self, store: WorkspaceStateStore) -> None:
        store.initialize()
        with store._connection(write=True) as connection:
            connection.execute(
                """
                INSERT OR REPLACE INTO catalog_versions(
                    catalog_id, schema_version, catalog_name, toy_commit, mat_commit,
                    manifest_sha256, plan_set_sha256, policy_sha256, counts_json,
                    payload_json, imported_at
                ) VALUES (?, 'test', 'test', ?, ?, ?, ?, ?, '{}', '{}', ?)
                """,
                (
                    "catalog-test",
                    "a" * 40,
                    self.mat_commit,
                    "1" * 64,
                    "2" * 64,
                    "3" * 64,
                    "2026-08-08T00:00:00+00:00",
                ),
            )
            connection.execute(
                "INSERT OR REPLACE INTO meta(key, value) VALUES('active_catalog_id', 'catalog-test')"
            )

    def _seed_authority(
        self,
        store: WorkspaceStateStore,
        source: SubjectBundle,
        target: SubjectBundle,
        *,
        authority_eligible: bool = True,
        rubric_version: int = 9,
    ) -> str:
        self._install_active_catalog(store)
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
            evidence_hash=self.review_evidence_hash,
            authority_eligible=authority_eligible,
            prompt_version=11,
            rubric_version=rubric_version,
        )
        store.set_task_head(
            task_id=self.task_id,
            role="mat_main",
            subject_id=target.subject_id,
            freshness="fresh",
        )
        return review_id

    def _write_receipt(
        self,
        root: Path,
        source: SubjectBundle,
        target: SubjectBundle,
        review_id: str,
        *,
        build_status: str = "pass",
    ) -> Path:
        build = {
            "schema": "toy-apollo.mechanical-build-evidence.v1",
            "task_id": self.task_id,
            "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash,
            "primary_hash": target.primary_hash,
            "commit": target.source_commit,
            "status": build_status,
            "success": build_status == "pass",
            "exit_code": 0 if build_status == "pass" else 1,
        }
        forbidden = {
            "schema": "toy-apollo.forbidden-scan-evidence.v1",
            "task_id": self.task_id,
            "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash,
            "primary_hash": target.primary_hash,
            "commit": target.source_commit,
            "status": "pass",
            "matches": [],
        }
        build_path = root / "build_evidence.json"
        forbidden_path = root / "forbidden_evidence.json"
        build_path.write_text(json.dumps(build, indent=2), encoding="utf-8")
        forbidden_path.write_text(json.dumps(forbidden, indent=2), encoding="utf-8")
        receipt = {
            "schema": "toy-apollo.validated-transformation-receipt.v1",
            "task_id": self.task_id,
            "created_at": "2026-08-08T00:00:00+00:00",
            "transformation_kind": "path_relocation",
            "mechanical_status": "pass",
            "source_review": {
                "review_id": review_id,
                "evidence_hash": self.review_evidence_hash,
                "prompt_version": 11,
                "rubric_version": 9,
            },
            "source_subject": self._subject_payload(source),
            "target_subject": self._subject_payload(target),
            "comparison": {
                "classification": "path_only_relocation",
                "primary_equal": True,
                "content_multiset_equal": True,
            },
            "checks": {
                "build": {
                    "status": "pass",
                    "artifact": {"path": build_path.name, "sha256": sha256_file(build_path)},
                },
                "forbidden_scan": {
                    "status": "pass",
                    "artifact": {
                        "path": forbidden_path.name,
                        "sha256": sha256_file(forbidden_path),
                    },
                },
            },
        }
        receipt_path = root / "validated_transformation_receipt_thm_1_1.json"
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        return receipt_path

    def test_valid_receipt_is_idempotent_and_marks_bundle_validated(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, target = self._subjects()
            store = WorkspaceStateStore(root / "state.sqlite3")
            review_id = self._seed_authority(store, source, target)
            receipt_path = self._write_receipt(root, source, target, review_id)
            report = MigrationReport(database=str(store.path))

            import_validated_transformation_receipt(store, receipt_path, report)
            import_validated_transformation_receipt(store, receipt_path, report)

            self.assertEqual(report.validated_transformation_receipts, 1)
            self.assertEqual(report.skipped, 1)
            self.assertEqual(
                analyze_current_mat_bundles(store)["tasks"][0]["status"],
                "validated_rebind",
            )
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM transformations").fetchone()[0], 1)

    def test_receipt_validation_fails_closed(self):
        cases = ("tampered_subject_hash", "primary_delta", "old_rubric", "no_authority", "failed_build")
        for case in cases:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                target_content = "theorem t : True := by exact True.intro\n" if case == "primary_delta" else None
                source, target = self._subjects(target_content=target_content)
                store = WorkspaceStateStore(root / "state.sqlite3")
                review_id = self._seed_authority(
                    store,
                    source,
                    target,
                    authority_eligible=case != "no_authority",
                    rubric_version=8 if case == "old_rubric" else 9,
                )
                receipt_path = self._write_receipt(
                    root,
                    source,
                    target,
                    review_id,
                    build_status="fail" if case == "failed_build" else "pass",
                )
                if case == "tampered_subject_hash":
                    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
                    receipt["target_subject"]["bundle_hash"] = "0" * 64
                    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

                with self.assertRaises(ValueError):
                    import_validated_transformation_receipt(
                        store,
                        receipt_path,
                        MigrationReport(database=str(store.path)),
                    )
                with store._connection(write=False) as connection:
                    self.assertEqual(connection.execute("SELECT COUNT(*) FROM transformations").fetchone()[0], 0)

    def test_valid_receipt_survives_clean_database_rebuild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            evidence = root / "evidence"
            evidence.mkdir()
            source, target = self._subjects()
            review_id = sha256_json(
                {
                    "schema": "toy-apollo.review.v1",
                    "task_id": self.task_id,
                    "subject_id": source.subject_id,
                    "evidence_hash": self.review_evidence_hash,
                    "authority_scope": "phase2_review_apply",
                }
            )
            self._write_receipt(evidence, source, target, review_id)
            state_path = root / "state.sqlite3"

            def refresh(store, **_kwargs):
                self._seed_authority(store, source, target)
                return {
                    "local": {"mat_main": 1, "mat_candidate": 0, "toy_current": 0, "errors": []},
                    "remote": {"subjects": 0, "errors": []},
                }

            with patch("formalization_engine.state_migration.refresh_workspace_state", side_effect=refresh):
                report = rebuild_workspace_database(
                    state_path=state_path,
                    workspace_root=root,
                    runtime_root=root / "runtime",
                    roots=[evidence],
                    refresh_remote=False,
                )

            self.assertEqual(report.validated_transformation_receipts, 1)
            rebuilt = WorkspaceStateStore(state_path)
            self.assertEqual(
                analyze_current_mat_bundles(rebuilt)["tasks"][0]["status"],
                "validated_rebind",
            )

    def test_rebuild_preserves_transformation_rejection_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            evidence = root / "evidence"
            evidence.mkdir()
            source, target = self._subjects()
            review_id = sha256_json(
                {
                    "schema": "toy-apollo.review.v1",
                    "task_id": self.task_id,
                    "subject_id": source.subject_id,
                    "evidence_hash": self.review_evidence_hash,
                    "authority_scope": "phase2_review_apply",
                }
            )
            receipt_path = self._write_receipt(evidence, source, target, review_id)
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["checks"]["build"]["artifact"]["sha256"] = "0" * 64
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            state_path = root / "state.sqlite3"

            def refresh(store, **_kwargs):
                self._seed_authority(store, source, target)
                return {
                    "local": {"mat_main": 1, "mat_candidate": 0, "toy_current": 0, "errors": []},
                    "remote": {"subjects": 0, "errors": []},
                }

            with patch("formalization_engine.state_migration.refresh_workspace_state", side_effect=refresh):
                report = rebuild_workspace_database(
                    state_path=state_path,
                    workspace_root=root,
                    runtime_root=root / "runtime",
                    roots=[evidence],
                    refresh_remote=False,
                )

            self.assertEqual(report.rejected_transformation_receipts, 1)
            with closing(sqlite3.connect(state_path)) as connection:
                row = connection.execute(
                    "SELECT payload_json FROM state_events "
                    "WHERE event_type = 'validated_transformation_receipt_rejected'"
                ).fetchone()
            self.assertIsNotNone(row)
            self.assertIn("evidence hash mismatch", json.loads(row[0])["validation_error"])


if __name__ == "__main__":
    unittest.main()
