import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from formalization_engine.authority_relocation import (
    BATCH_SCHEMA,
    BUILD_SCHEMA,
    AuthorityRoute,
    AuthorityRelocationError,
    _assert_exact_subject_move,
    _receipt_payload,
    _validate_build_evidence,
    replay_authority_relocation_batch,
)
from formalization_engine.state_store import SubjectBundle, WorkspaceStateStore, sha256_file
from formalization_engine.task_catalog import build_catalog


class AuthorityRelocationTests(unittest.TestCase):
    def _subject(self, *, repository: str, layout: str, content_hash: str = "a" * 64):
        manifest = json.dumps(
            [
                {
                    "path": "ProbabilityTheory/chapter_01/thm_1_1.lean",
                    "content_sha256": content_hash,
                    "git_blob_sha": "b" * 40,
                    "size": 12,
                }
            ],
            sort_keys=True,
        )
        return {
            "subject_id": content_hash,
            "task_id": "thm_1_1",
            "source_repo": repository,
            "source_commit": "target",
            "layout": layout,
            "bundle_hash": "c" * 64,
            "primary_hash": content_hash,
            "primary_path": "ProbabilityTheory/chapter_01/thm_1_1.lean",
            "manifest_json": manifest,
        }

    def test_exact_move_accepts_identity_change_but_rejects_byte_change(self):
        old = self._subject(repository="mat", layout="mat")
        new = self._subject(repository="ProbabilityTheoryFormalization", layout="unified")
        _assert_exact_subject_move(old, new)
        changed = self._subject(
            repository="ProbabilityTheoryFormalization", layout="unified", content_hash="d" * 64
        )
        with self.assertRaisesRegex(AuthorityRelocationError, "not a byte-exact"):
            _assert_exact_subject_move(old, changed)

    def test_build_evidence_is_bound_to_immutable_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            logs = {}
            for name in ("formal_corpus", "lake_build"):
                path = root / f"{name}.log"
                path.write_text("pass\n", encoding="utf-8")
                logs[name] = {
                    "exit_code": 0,
                    "log_path": str(path.resolve()),
                    "log_sha256": sha256_file(path),
                }
            evidence = root / "build.json"
            evidence.write_text(
                json.dumps(
                    {
                        "schema": BUILD_SCHEMA,
                        "target_commit": "target",
                        "target_tree_equals_observed_head_tree": True,
                        "worktree_corpus_clean": True,
                        "checks": logs,
                    }
                ),
                encoding="utf-8",
            )
            _validate_build_evidence(evidence, "target")
            Path(logs["lake_build"]["log_path"]).write_text("tampered\n", encoding="utf-8")
            with self.assertRaisesRegex(AuthorityRelocationError, "path/hash mismatch"):
                _validate_build_evidence(evidence, "target")

    def test_batch_replay_sees_rows_created_in_outer_bulk_transaction(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            task_path = "ProbabilityTheory/chapter_01/thm_1_1.lean"
            content = b"theorem fixture : True := by trivial\n"
            old = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={task_path: content},
                primary_path=task_path,
                source_repo="mat",
                source_commit="old",
                layout="mat",
                subject_kind="catalog_git_bundle",
            )
            new = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={task_path: content},
                primary_path=task_path,
                source_repo="ProbabilityTheoryFormalization",
                source_commit="target",
                layout="unified",
                subject_kind="catalog_git_bundle",
            )
            route = AuthorityRoute(
                task_id="thm_1_1",
                route="direct_review",
                old_subject={**old.__dict__, "manifest_json": json.dumps(old.manifest())},
                new_subject={**new.__dict__, "manifest_json": json.dumps(new.manifest())},
                relocation_source={**old.__dict__, "manifest_json": json.dumps(old.manifest())},
                authority={},
            )
            logs = {}
            for name in ("formal_corpus", "lake_build"):
                path = root / f"{name}.log"
                path.write_text("pass\n", encoding="utf-8")
                logs[name] = {
                    "exit_code": 0,
                    "log_path": str(path.resolve()),
                    "log_sha256": sha256_file(path),
                }
            build_path = root / "build.json"
            build_path.write_text(
                json.dumps(
                    {
                        "schema": BUILD_SCHEMA,
                        "target_commit": "target",
                        "target_tree_equals_observed_head_tree": True,
                        "worktree_corpus_clean": True,
                        "checks": logs,
                    }
                ),
                encoding="utf-8",
            )
            plan = json.dumps(
                [
                    {
                        "block_id": "thm_1_1",
                        "type": "Theorem_with_Proof",
                        "title": "Fixture",
                        "content": "Fixture",
                        "dependencies": [],
                        "source_plan": "fixture",
                    }
                ]
            ).encode()
            manifest = (
                "group,chapter,file_path,basename,module_name,ledger_task_match,"
                "ledger_status,phase2_status,classification,axiom_count,sorry_or_admit_in_code\n"
                "ProbabilityTheory/chapter_01,1,ProbabilityTheory/chapter_01/thm_1_1.lean,"
                "thm_1_1,ProbabilityTheory.chapter_01.thm_1_1,yes,COMPLETED,pass,"
                "ledger_task_module,0,no\n"
            ).encode()
            catalog = build_catalog(
                catalog_name="fixture",
                toy_commit="toy",
                mat_commit="old",
                plan_documents={"plans/fixture_plan.json": plan},
                manifest_bytes=manifest,
                family_overrides=[],
                restored_task_ids=[],
                legacy_cohort_id="legacy",
                mat_tree_paths=[task_path],
            )
            catalogs = {"legacy": "legacy", "target": catalog.catalog_id}
            receipt = _receipt_payload(
                route, catalogs, build_path, sha256_file(build_path), "2026-09-01T00:00:00Z"
            )
            receipt_path = root / "thm_1_1.json"
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            record = {
                "task_id": "thm_1_1",
                "route": "direct_review",
                "path": str(receipt_path.resolve()),
                "sha256": sha256_file(receipt_path),
                "transformation_id": receipt["result"]["transformation_id"],
            }
            batch_path = root / "authority-relocation-batch-v2.json"
            batch_path.write_text(
                json.dumps(
                    {
                        "schema": BATCH_SCHEMA,
                        "catalogs": catalogs,
                        "route_counts": {"direct_review": 1},
                        "build_evidence": {
                            "path": str(build_path.resolve()),
                            "sha256": sha256_file(build_path),
                        },
                        "items": [record],
                    }
                ),
                encoding="utf-8",
            )
            store = WorkspaceStateStore(root / "state.sqlite3")
            with patch(
                "formalization_engine.authority_relocation.EXPECTED_ROUTE_COUNTS",
                {"direct_review": 1},
            ), patch(
                "formalization_engine.authority_relocation._apply_validated_relocation_receipts",
                return_value={"applied": 1},
            ):
                with store.bulk_write():
                    store.persist_catalog(catalog)
                    store.upsert_subject(old)
                    store.upsert_subject(new)
                    store.set_task_head(
                        task_id="thm_1_1",
                        role="unified_main",
                        subject_id=new.subject_id,
                    )
                    result = replay_authority_relocation_batch(store, batch_path)

            self.assertEqual(result["applied"], 1)


if __name__ == "__main__":
    unittest.main()
