from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.state_invalidation_recovery import (
    ResolvedInvalidationRecoveryError,
    build_resolved_invalidation_recovery,
    validate_resolved_invalidation_recovery,
)
from src.toy_apollo.state_migration import (
    MigrationReport,
    import_resolved_invalidation_recovery_receipt,
)
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore
from tests.test_state_review_apply_recovery import HistoricalReviewApplyRecoveryTests


class ResolvedInvalidationRecoveryTests(unittest.TestCase):
    def _build(self, path: Path, subject: SubjectBundle) -> Path:
        payload = {
            "schema": "mat.catalog.exact-build.v1", "task_id": subject.task_id,
            "commit": subject.source_commit, "subject_id": subject.subject_id,
            "bundle_hash": subject.bundle_hash, "primary_hash": subject.primary_hash,
            "primary_path": subject.primary_path, "subject_files": subject.manifest(),
            "success": True, "exit_code": 0,
            "focused_build": {"command": "lake build fixture", "exit_code": 0},
            "forbidden_token_scan": {"exit_code": 0, "findings": {}},
            "lean_tree_equivalence": {"target_commit": subject.source_commit, "build_checkout_clean": True, "changed_lean_files": []},
        }
        path.write_text(json.dumps(payload), encoding="utf-8")
        return path

    def _fixture(self, root: Path) -> tuple[dict, Path, Path, Path, Path]:
        source_test = HistoricalReviewApplyRecoveryTests()
        paths = source_test._write_pack(root)
        review_input = json.loads(paths["input"].read_text(encoding="utf-8"))
        old = review_input["subject_bundle"]
        stale = {
            "schema": "mat.rubric78.review-apply-receipt.v1", "task_id": "thm_5_1",
            "review_id": "a" * 64, "review_result_file": str(paths["result"]),
            "review_result_hash": __import__("hashlib").sha256(paths["result"].read_bytes()).hexdigest(),
            "review_input_hash": review_input and __import__("src.toy_apollo.state_store", fromlist=["sha256_json"]).sha256_json(review_input),
            "bundle_hash": old["bundle_hash"], "primary_hash": old["primary_hash"],
            "clean_pass": True, "exact_bundle_covered": True, "verdict": "pass",
            "phase2_status": "pass", "invalidated_by": "thm_5_2",
        }
        stale_path = paths["pack"] / "review_apply_receipt_v1.json"
        stale_path.write_text(json.dumps(stale), encoding="utf-8")
        target = SubjectBundle.from_manifest(task_id="thm_5_1", files=old["files"], primary_path=old["primary_path"], source_repo="mat", source_commit="b" * 40, layout="mat", subject_kind="catalog_git_bundle")
        invalidator = SubjectBundle.from_manifest(task_id="thm_5_2", files=old["files"], primary_path=old["primary_path"], source_repo="mat", source_commit="b" * 40, layout="mat", subject_kind="catalog_git_bundle")
        target_build = self._build(root / "target_build.json", target)
        invalidator_build = self._build(root / "invalidator_build.json", invalidator)
        consumers = root / "consumers.json"
        consumers.write_text(json.dumps({"schema": "mat.catalog.direct-consumer-manifest.v1", "task_id": "thm_5_1", "commit": "b" * 40, "subject_id": target.subject_id, "bundle_hash": target.bundle_hash, "consumers": []}), encoding="utf-8")
        return paths, stale_path, target_build, invalidator_build, consumers

    def test_valid_exact_recovery_and_receipt_tamper_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths, stale, target, invalidator, consumers = self._fixture(Path(tmp))
            receipt = build_resolved_invalidation_recovery(stale_receipt_path=stale, target_build_path=target, invalidator_build_paths=[invalidator], consumer_manifest_path=consumers, consumer_build_paths=[], created_at="2026-08-08T00:00:00+00:00")
            receipt_path = paths["pack"] / "resolved_invalidation_recovery_receipt_v1.json"
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            validated, target_subject, _, _ = validate_resolved_invalidation_recovery(receipt_path)
            self.assertEqual(validated["task_id"], "thm_5_1")
            self.assertEqual(target_subject.bundle_hash, receipt["source_subject"]["bundle_hash"])
            receipt["resolution"]["invalidated_by"] = "thm_5_3"
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            with self.assertRaises(ResolvedInvalidationRecoveryError):
                validate_resolved_invalidation_recovery(receipt_path)

    def test_missing_consumer_build_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            _, stale, target, invalidator, consumers = self._fixture(Path(tmp))
            data = json.loads(consumers.read_text(encoding="utf-8"))
            data["consumers"] = [{"task_id": "thm_5_3", "paths": ["fixture.lean"]}]
            consumers.write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaises(ResolvedInvalidationRecoveryError):
                build_resolved_invalidation_recovery(stale_receipt_path=stale, target_build_path=target, invalidator_build_paths=[invalidator], consumer_manifest_path=consumers, consumer_build_paths=[])

    def test_import_sees_current_mat_head_created_in_same_bulk_rebuild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths, stale, target_build, invalidator, consumers = self._fixture(root)
            receipt = build_resolved_invalidation_recovery(
                stale_receipt_path=stale,
                target_build_path=target_build,
                invalidator_build_paths=[invalidator],
                consumer_manifest_path=consumers,
                consumer_build_paths=[],
                created_at="2026-08-08T00:00:00+00:00",
            )
            receipt_path = paths["pack"] / "resolved_invalidation_recovery_receipt_v1.json"
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            _, target, _, _ = validate_resolved_invalidation_recovery(receipt_path)
            store = WorkspaceStateStore(root / "state.sqlite3")
            report = MigrationReport(database=str(store.path))

            with store.bulk_write():
                with store._connection(write=True) as connection:
                    connection.execute(
                        """
                        INSERT INTO catalog_versions(
                            catalog_id, schema_version, catalog_name, toy_commit,
                            mat_commit, manifest_sha256, plan_set_sha256,
                            policy_sha256, counts_json, payload_json, imported_at
                        ) VALUES (?, 'test', 'test', ?, ?, ?, ?, ?, '{}', '{}', ?)
                        """,
                        (
                            "catalog-test",
                            "a" * 40,
                            target.source_commit,
                            "1" * 64,
                            "2" * 64,
                            "3" * 64,
                            "2026-08-08T00:00:00+00:00",
                        ),
                    )
                    connection.execute(
                        "INSERT INTO meta(key, value) VALUES('active_catalog_id', 'catalog-test')"
                    )
                store.upsert_subject(target)
                store.set_task_head(
                    task_id=target.task_id,
                    role="mat_main",
                    subject_id=target.subject_id,
                    freshness="fresh",
                )

                import_resolved_invalidation_recovery_receipt(store, receipt_path, report)

            self.assertEqual(report.resolved_invalidation_recovery_receipts, 1)
            with store._connection(write=False) as connection:
                row = connection.execute(
                    "SELECT authority_scope, authority_eligible FROM reviews WHERE task_id = ?",
                    (target.task_id,),
                ).fetchone()
            self.assertIsNotNone(row)
            self.assertEqual(row["authority_scope"], "resolved_invalidation_current_exact_recovery")
            self.assertEqual(row["authority_eligible"], 1)
