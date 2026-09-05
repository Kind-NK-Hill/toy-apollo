from __future__ import annotations

import json
import sqlite3
import tempfile
import unittest
from contextlib import closing
from pathlib import Path
from unittest.mock import patch

from formalization_engine.ledger_manager import LedgerDangerousStateError, LedgerManager, TaskStatus
from formalization_engine.core.sqlite_ledger import SQLiteLedgerManager
from formalization_engine.state_migration import (
    MigrationReport,
    import_workspace_review_binding,
    rebuild_workspace_database,
)
from formalization_engine.state_review import record_review_apply_state
from formalization_engine.state_reconcile import (
    discover_formal_plan_task_ids,
    discover_runtime_support_files,
    is_task_owned_path,
    task_id_from_path,
)
from formalization_engine.state_store import (
    StateIntegrityError,
    StateDatabaseMissingError,
    StateStoreError,
    SubjectBundle,
    WorkspaceStateStore,
    canonical_state_path,
    refuse_legacy_ledger_write,
    sha256_json,
)


class WorkspaceStateStoreTests(unittest.TestCase):
    def _bundle(
        self,
        *,
        task_id: str = "thm_1_1",
        content: str = "theorem t : True := by trivial\n",
        path: str = "ToyApollo/Output/thm_1_1.lean",
        commit: str = "a",
        repo: str = "mat",
    ) -> SubjectBundle:
        return SubjectBundle.from_files(
            task_id=task_id,
            files={path: content},
            primary_path=path,
            source_repo=repo,
            source_commit=commit,
            layout=repo,
        )

    def test_read_only_missing_database_does_not_create_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.sqlite3"
            store = WorkspaceStateStore(path)
            self.assertFalse(store.exists)
            with self.assertRaises(Exception):
                store.summary()
            self.assertFalse(path.exists())

    def test_task_bundle_owns_runtime_support_but_not_tests_or_review_contracts(self):
        toy_primary = "ToyApollo/Output/thm_1_1.lean"
        self.assertTrue(
            is_task_owned_path(
                "ToyApollo/Output/thm_1_1_support/thm_1_1_basic.lean",
                "thm_1_1",
                toy_primary,
            )
        )
        self.assertFalse(
            is_task_owned_path(
                "tests/lean/thm_1_1_contract.lean",
                "thm_1_1",
                toy_primary,
            )
        )

    def test_subject_support_projection_binds_exact_shared_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            support_path = root / "ToyApollo" / "Output" / "shared_core.lean"
            support_path.parent.mkdir(parents=True)
            support_path.write_text("theorem sharedCore : True := by trivial\n", encoding="utf-8")
            support_hash = SubjectBundle.from_files(
                task_id="thm_8_6",
                files={"ToyApollo/Output/shared_core.lean": support_path.read_bytes()},
                primary_path="ToyApollo/Output/shared_core.lean",
                source_repo="formalization_engine",
            ).primary_hash
            projection_path = root / "phase2_prompt_packs" / "thm_8_6" / "subject_support_projection.json"
            projection_path.parent.mkdir(parents=True)
            projection_path.write_text(
                json.dumps(
                    {
                        "schema_version": "toy-apollo.subject-support-projection.v1",
                        "task_id": "thm_8_6",
                        "files": [
                            {
                                "path": "ToyApollo/Output/shared_core.lean",
                                "content_sha256": support_hash,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            support = discover_runtime_support_files(root, "thm_8_6", formal_task_ids=set())

            self.assertEqual(support, {"ToyApollo/Output/shared_core.lean": support_path.read_bytes()})

        mat_primary = "chapter_01/def_1_3.lean"
        self.assertTrue(
            is_task_owned_path(
                "chapter_01/def_1_3_probability_cdf_bridge.lean",
                "def_1_3",
                mat_primary,
            )
        )
        self.assertFalse(
            is_task_owned_path(
                "chapter_01/review_contracts/def_1_3_probability_cdf_contract.lean",
                "def_1_3",
                mat_primary,
            )
        )

    def test_kenneth_thm_1_2_part_four_filename_belongs_to_parent_task(self):
        self.assertEqual(
            task_id_from_path("ProbabilityTheory/chapter_01/thm_1_2_4.lean"),
            "thm_1_2",
        )
        self.assertTrue(
            is_task_owned_path(
                "ProbabilityTheory/chapter_01/thm_1_2_4.lean",
                "thm_1_2",
                "ProbabilityTheory/chapter_01/thm_1_2.lean",
            )
        )

    def test_chapters_two_to_four_formal_plan_catalog_is_exact(self):
        plans_dir = Path(__file__).resolve().parents[1] / "plans"
        if not plans_dir.is_dir():
            self.skipTest("requires private formal-plan corpus fixture")
        task_ids = discover_formal_plan_task_ids(plans_dir, chapters=(2, 3, 4))
        counts = {
            chapter: sum(1 for task_id in task_ids if task_id.split("_", 2)[1] == str(chapter))
            for chapter in (2, 3, 4)
        }
        self.assertEqual(counts, {2: 36, 3: 39, 4: 39})
        self.assertEqual(len(task_ids), 114)
        self.assertTrue(
            {
                "def_4_2_inverse_image",
                "def_4_3_limsup_liminf",
                "def_4_3_sup_inf",
                "def_4_4_complex_number",
                "def_4_4_complex_operations",
                "def_4_4_complex_random_variable",
                "def_4_4_polar_form",
                "ex_4_1_indicator_examples",
                "ex_4_2_lebesgue_borel",
            }.issubset(task_ids)
        )
        self.assertFalse(any(task_id.startswith(("rem_", "intro_")) for task_id in task_ids))

    def test_named_formal_primary_is_not_support_of_shorter_task_id(self):
        formal_task_ids = {"def_4_2", "def_4_2_inverse_image"}
        primary = "ToyApollo/Output/def_4_2.lean"
        named_primary = "ToyApollo/Output/def_4_2_inverse_image.lean"
        ordinary_support = "ToyApollo/Output/def_4_2_helper.lean"

        self.assertEqual(
            task_id_from_path(named_primary, formal_task_ids=formal_task_ids),
            "def_4_2_inverse_image",
        )
        self.assertFalse(
            is_task_owned_path(
                named_primary,
                "def_4_2",
                primary,
                formal_task_ids=formal_task_ids,
            )
        )
        self.assertTrue(
            is_task_owned_path(
                ordinary_support,
                "def_4_2",
                primary,
                formal_task_ids=formal_task_ids,
            )
        )
    def test_workspace_review_binding_reuses_only_an_eligible_applied_basis(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = WorkspaceStateStore(root / "state.sqlite3")
            basis = self._bundle(path="phase2_prompt_packs/thm_1_1/official_snapshot.lean")
            target = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={"chapter_01/thm_1_1.lean": "theorem t : True := by trivial\n"},
                primary_path="chapter_01/thm_1_1.lean",
                source_repo="mat",
                source_commit="candidate",
                layout="mat",
            )
            store.upsert_subject(basis)
            store.record_review(
                task_id=basis.task_id,
                subject_id=basis.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=root / "basis.json",
                evidence_hash="basis-evidence",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            binding_path = root / "workspace_review_binding_test.json"
            binding_path.write_text(
                json.dumps(
                    {
                        "schema_version": "toy-apollo.workspace-review-binding.v1",
                        "created_at": "2026-07-17T00:00:00+00:00",
                        "reviewer_independence": {"scope": "mechanical_rebind"},
                        "tasks": [
                            {
                                "task_id": "thm_1_1",
                                "binding_kind": "legacy_primary_scope_rebind",
                                "basis_review": {
                                    "evidence_hash": "basis-evidence",
                                    "primary_hash": basis.primary_hash,
                                },
                                "checks": {
                                    "build_status": "pass",
                                    "forbidden_scan_status": "pass",
                                    "support_scope_status": "pass",
                                    "mat_relocation_status": "pass",
                                },
                                "subjects": [
                                    {
                                        "source_repo": target.source_repo,
                                        "source_commit": target.source_commit,
                                        "layout": target.layout,
                                        "primary_path": target.primary_path,
                                        "primary_hash": target.primary_hash,
                                        "bundle_hash": target.bundle_hash,
                                        "files": [item.as_dict() for item in target.files],
                                    }
                                ],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            report = MigrationReport(database=str(store.path))
            with store.bulk_write():
                import_workspace_review_binding(store, binding_path, report)

            self.assertEqual(report.review_bindings, 1)
            store.upsert_subject(target)
            coverage = store.review_coverage(target.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(
                coverage["authority_scope"],
                "workspace_bundle_rebind:legacy_primary_scope_rebind",
            )

    def test_summary_is_byte_for_byte_read_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.sqlite3"
            store = WorkspaceStateStore(path)
            store.initialize()
            before = path.read_bytes()
            before_mtime = path.stat().st_mtime_ns
            store.summary()
            self.assertEqual(path.read_bytes(), before)
            self.assertEqual(path.stat().st_mtime_ns, before_mtime)

    def test_legacy_json_writer_is_blocked_after_sqlite_activation(self):
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp) / "runtime"
            runtime.mkdir()
            state_path = canonical_state_path(runtime.parent / "ProbabilityTheoryFormalization-artifacts")
            WorkspaceStateStore(state_path).initialize()
            with self.assertRaises(StateStoreError):
                refuse_legacy_ledger_write(runtime, operation="test legacy write")

    def test_review_coverage_follows_task_and_bundle_not_commit_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            reviewed = self._bundle(commit="old")
            same_bundle_new_commit = self._bundle(commit="new")
            self.assertNotEqual(reviewed.subject_id, same_bundle_new_commit.subject_id)
            self.assertEqual(reviewed.bundle_hash, same_bundle_new_commit.bundle_hash)
            store.upsert_subject(reviewed)
            store.upsert_subject(same_bundle_new_commit)
            evidence = Path(tmp) / "review.json"
            evidence.write_text("{}\n", encoding="utf-8")
            store.record_review(
                task_id=reviewed.task_id,
                subject_id=reviewed.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=evidence,
                evidence_hash="evidence",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )

            coverage = store.review_coverage(same_bundle_new_commit.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(coverage["coverage_kind"], "exact_bundle")

    def test_old_pass_is_not_current_after_bundle_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            reviewed = self._bundle(content="theorem t : True := by trivial\n")
            changed = self._bundle(content="theorem t : True := by exact True.intro\n", commit="b")
            store.upsert_subject(reviewed)
            store.upsert_subject(changed)
            store.record_review(
                task_id=reviewed.task_id,
                subject_id=reviewed.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review.json",
                evidence_hash="review-a",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.set_task_head(task_id=changed.task_id, role="mat_candidate", subject_id=changed.subject_id)

            report = store.task_report(changed.task_id)
            self.assertIsNone(report["candidate_review_coverage"])
            self.assertIn("needs_review", report["actions"])
            self.assertIsNone(report["latest_current_review"])

    def test_applied_version_upgrades_duplicate_unapplied_review_alias(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            subject = self._bundle()
            store.upsert_subject(subject)
            common = {
                "task_id": subject.task_id,
                "subject_id": subject.subject_id,
                "verdict": "pass",
                "proof_class": "faithful",
                "completion_class": "complete",
                "phase2_status": "pass",
                "evidence_hash": "same-review-bytes",
                "authority_scope": "phase2_review_artifact",
                "prompt_version": 11,
                "rubric_version": 9,
            }
            first_id = store.record_review(
                **common,
                evidence_path=Path(tmp) / "semantic_review_result.json",
                authority_eligible=False,
            )
            second_id = store.record_review(
                **common,
                evidence_path=Path(tmp) / "semantic_review_result_v8.json",
                authority_eligible=True,
            )

            self.assertEqual(first_id, second_id)
            coverage = store.review_coverage(subject.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(coverage["authority_eligible"], 1)
            self.assertTrue(str(coverage["evidence_path"]).endswith("semantic_review_result_v8.json"))

    def test_primary_only_legacy_review_is_visible_but_cannot_cover_bundle(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            legacy = self._bundle(path="review/official_snapshot.lean")
            current = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={
                    "ToyApollo/Output/thm_1_1.lean": "theorem t : True := by trivial\n",
                    "ToyApollo/Output/thm_1_1_support/core.lean": "theorem helper : True := by trivial\n",
                },
                primary_path="ToyApollo/Output/thm_1_1.lean",
                source_repo="mat",
                source_commit="current",
                layout="mat",
            )
            store.upsert_subject(legacy)
            store.upsert_subject(current)
            store.record_review(
                task_id=legacy.task_id,
                subject_id=legacy.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "semantic_review_result_v8.json",
                evidence_hash="legacy-applied-review",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.set_task_head(task_id=current.task_id, role="mat_candidate", subject_id=current.subject_id)

            self.assertIsNone(store.review_coverage(current.subject_id))
            partial = store.partial_review_coverage(current.subject_id)
            self.assertIsNotNone(partial)
            report = store.task_report(current.task_id)
            self.assertIn("review_scope_rebind_required", report["actions"])
            self.assertNotIn("needs_review", report["actions"])

    def test_verified_mechanical_relocation_inherits_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            source = self._bundle(path="phase2_prompt_packs/thm_1_1/candidate_v1.lean")
            target = self._bundle(path="ProbabilityTheory/chapter_01/thm_1_1.lean", repo="kenneth")
            store.upsert_subject(source)
            store.upsert_subject(target)
            store.record_review(
                task_id=source.task_id,
                subject_id=source.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review.json",
                evidence_hash="review-b",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.record_transformation(
                task_id=source.task_id,
                source_subject_id=source.subject_id,
                target_subject_id=target.subject_id,
                transformation_kind="path_relocation",
                mechanical_status="pass",
                build_status="pass",
            )

            coverage = store.review_coverage(target.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(coverage["coverage_kind"], "path_relocation")

    def test_reviewed_mat_change_without_pr_is_reported_ready_for_pr(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            reviewed = self._bundle(content="theorem t : True := by trivial\n", commit="reviewed")
            kenneth = self._bundle(
                content="theorem t : True := by exact True.intro\n",
                path="ProbabilityTheory/chapter_01/thm_1_1.lean",
                commit="kenneth",
                repo="kenneth",
            )
            for subject in (reviewed, kenneth):
                store.upsert_subject(subject)
            store.record_review(
                task_id=reviewed.task_id,
                subject_id=reviewed.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review.json",
                evidence_hash="reviewed-change",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.set_task_head(task_id=reviewed.task_id, role="mat_candidate", subject_id=reviewed.subject_id)
            store.set_task_head(task_id=kenneth.task_id, role="kenneth_main", subject_id=kenneth.subject_id)

            self.assertIn("reviewed_ready_for_pr", store.task_report(reviewed.task_id)["actions"])

    def test_new_review_after_open_pr_reports_pr_behind_without_second_pr(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            old_pr = self._bundle(content="theorem t : True := by trivial\n", commit="old-pr")
            reviewed = self._bundle(
                content="theorem t : True := by exact True.intro\n", commit="reviewed-again"
            )
            kenneth = self._bundle(
                content="theorem t : True := by decide\n",
                path="ProbabilityTheory/chapter_01/thm_1_1.lean",
                commit="kenneth",
                repo="kenneth",
            )
            for subject in (old_pr, reviewed, kenneth):
                store.upsert_subject(subject)
            store.record_review(
                task_id=reviewed.task_id,
                subject_id=reviewed.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review-v2.json",
                evidence_hash="reviewed-again",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.set_task_head(task_id=reviewed.task_id, role="mat_candidate", subject_id=reviewed.subject_id)
            store.set_task_head(task_id=kenneth.task_id, role="kenneth_main", subject_id=kenneth.subject_id)
            store.record_integration(
                task_id=reviewed.task_id,
                target_repo="kenneth",
                integration_kind="pull_request",
                state="open",
                pr_number=99,
                head_sha="old-pr-sha",
                head_subject_id=old_pr.subject_id,
                remote_freshness="fresh",
            )

            actions = store.task_report(reviewed.task_id)["actions"]
            self.assertIn("pr_behind_reviewed_local", actions)
            self.assertNotIn("reviewed_ready_for_pr", actions)

    def test_promotion_queue_claim_is_serialized(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            for task_id in ("thm_1_1", "thm_1_2"):
                subject = self._bundle(task_id=task_id, path=f"ToyApollo/Output/{task_id}.lean")
                store.upsert_subject(subject)
                store.record_integration(
                    task_id=task_id,
                    subject_id=subject.subject_id,
                    target_repo="mat",
                    integration_kind="mat_promotion",
                    state="ready",
                )

            first = store.claim_next_integration(
                integration_kind="mat_promotion", target_repo="mat", worker_id="worker-a"
            )
            second = store.claim_next_integration(
                integration_kind="mat_promotion", target_repo="mat", worker_id="worker-b"
            )
            third = store.claim_next_integration(
                integration_kind="mat_promotion", target_repo="mat", worker_id="worker-c"
            )
            self.assertIsNotNone(first)
            self.assertIsNotNone(second)
            self.assertNotEqual(first["integration_id"], second["integration_id"])
            self.assertIsNone(third)

    def test_dependency_pin_blocks_promotion_until_dependency_lands_exact_bundle(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            dependency_candidate = self._bundle(task_id="thm_5_7", path="candidate/thm_5_7.lean")
            consumer = self._bundle(task_id="thm_6_2", path="candidate/thm_6_2.lean")
            store.upsert_subject(dependency_candidate)
            store.upsert_subject(consumer)
            store.pin_dependency_candidate(
                consumer_task_id="thm_6_2",
                dependency_task_id="thm_5_7",
                subject_id=dependency_candidate.subject_id,
                required_role="mat_main",
            )
            store.record_integration(
                task_id="thm_6_2",
                subject_id=consumer.subject_id,
                target_repo="mat",
                integration_kind="mat_promotion",
                state="ready",
            )
            self.assertIsNone(
                store.claim_next_integration(
                    integration_kind="mat_promotion", target_repo="mat", worker_id="worker-a"
                )
            )

            landed = self._bundle(
                task_id="thm_5_7",
                path="candidate/thm_5_7.lean",
                commit="landed",
            )
            store.upsert_subject(landed)
            store.set_task_head(task_id="thm_5_7", role="mat_main", subject_id=landed.subject_id)
            pins = store.revalidate_dependency_pins(consumer_task_id="thm_6_2")
            self.assertEqual(pins[0]["state"], "validated")
            claimed = store.claim_next_integration(
                integration_kind="mat_promotion", target_repo="mat", worker_id="worker-b"
            )
            self.assertIsNotNone(claimed)

    def test_sqlite_ledger_preserves_legacy_file_and_parallel_task_updates(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            legacy = root / "project_ledger.json"
            legacy.write_text(json.dumps({"tasks": {}, "symbols": {}}, indent=2), encoding="utf-8")
            original = legacy.read_bytes()
            store = WorkspaceStateStore(Path(tmp) / "runtime-artifacts" / "state.sqlite3")
            writer_a = SQLiteLedgerManager(state_store=store, artifact_root=root, legacy_ledger_path=legacy)
            writer_a.add_or_update_task(
                {
                    "block_id": "thm_1_1",
                    "type": "Theorem",
                    "title": "A",
                    "content": "A",
                    "source_plan": "chapter1",
                    "dependencies": [],
                }
            )
            writer_b = SQLiteLedgerManager(state_store=store, artifact_root=root, legacy_ledger_path=legacy)
            writer_b.add_or_update_task(
                {
                    "block_id": "thm_1_2",
                    "type": "Theorem",
                    "title": "B",
                    "content": "B",
                    "source_plan": "chapter1",
                    "dependencies": [],
                }
            )
            writer_a.update_status("thm_1_1", TaskStatus.LOCAL_FIXING)

            persisted = SQLiteLedgerManager(state_store=store, artifact_root=root, legacy_ledger_path=legacy).ledger
            self.assertEqual(persisted["tasks"]["thm_1_1"]["status"], TaskStatus.LOCAL_FIXING.value)
            self.assertIn("thm_1_2", persisted["tasks"])
            self.assertEqual(legacy.read_bytes(), original)

            writer_a.ledger = {"tasks": {}, "symbols": {}}
            with self.assertRaises(LedgerDangerousStateError):
                writer_a.save()

    def test_atomic_normalized_mutation_rolls_back_ledger_and_subject_together(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            legacy = root / "project_ledger.json"
            legacy.write_text(json.dumps({"tasks": {}, "symbols": {}}), encoding="utf-8")
            store = WorkspaceStateStore(Path(tmp) / "runtime-artifacts" / "state.sqlite3")
            writer = SQLiteLedgerManager(
                state_store=store,
                artifact_root=root,
                legacy_ledger_path=legacy,
            )
            writer.add_or_update_task(
                {
                    "block_id": "thm_1_1",
                    "type": "Theorem",
                    "title": "Atomic",
                    "content": "A",
                    "source_plan": "chapter1",
                    "dependencies": [],
                }
            )
            subject = self._bundle()
            before_ledger, before_revision = store.load_campaign_ledger(writer.campaign_id)

            def mutate_ledger():
                writer.update_runtime_metadata("thm_1_1", atomic_marker="staged")
                writer.update_status("thm_1_1", TaskStatus.COMPLETED)

            def fail_normalized(state_store, _result):
                state_store.upsert_subject(subject)
                raise RuntimeError("force rollback")

            with self.assertRaisesRegex(RuntimeError, "force rollback"):
                writer.mutate_with_normalized_state(mutate_ledger, fail_normalized)

            rolled_back, rolled_back_revision = store.load_campaign_ledger(writer.campaign_id)
            self.assertEqual(rolled_back_revision, before_revision)
            self.assertEqual(rolled_back, before_ledger)
            self.assertNotIn("atomic_marker", writer.ledger["tasks"]["thm_1_1"])
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM subjects").fetchone()[0], 0)

            writer.mutate_with_normalized_state(
                mutate_ledger,
                lambda state_store, _result: state_store.upsert_subject(subject),
            )
            committed, committed_revision = store.load_campaign_ledger(writer.campaign_id)
            self.assertEqual(committed_revision, before_revision + 1)
            self.assertEqual(committed["tasks"]["thm_1_1"]["atomic_marker"], "staged")
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM subjects").fetchone()[0], 1)

    def test_sqlite_ledger_missing_all_state_requires_explicit_rebuild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            state_path = Path(tmp) / "runtime-artifacts" / "state.sqlite3"
            with self.assertRaises(LedgerDangerousStateError):
                SQLiteLedgerManager(
                    state_store=WorkspaceStateStore(state_path),
                    artifact_root=root,
                    legacy_ledger_path=root / "project_ledger.json",
                )
            self.assertFalse(state_path.exists())

    def test_existing_sqlite_campaign_never_loads_legacy_json(self):
        for read_only in (False, True):
            for legacy_state in ("missing", "corrupt"):
                with self.subTest(read_only=read_only, legacy_state=legacy_state), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    legacy = root / "project_ledger.json"
                    if legacy_state == "corrupt":
                        legacy.write_bytes(b"{corrupt historical evidence")
                    store = WorkspaceStateStore(root / "state.sqlite3")
                    store.import_campaign_ledger(
                        campaign_id="workspace:active", artifact_root=root,
                        ledger={"tasks": {}, "symbols": {}, "marker": "sqlite authority"},
                    )
                    before = store.path.read_bytes()
                    with patch.object(
                        LedgerManager, "_load_ledger",
                        side_effect=AssertionError("existing campaign must not read legacy JSON"),
                    ):
                        ledger = SQLiteLedgerManager(
                            state_store=store, artifact_root=root, legacy_ledger_path=legacy,
                            campaign_id="workspace:active", read_only=read_only,
                        )
                    self.assertEqual(ledger.ledger["marker"], "sqlite authority")
                    self.assertEqual(store.path.read_bytes(), before)
                    if legacy_state == "corrupt":
                        self.assertEqual(legacy.read_bytes(), b"{corrupt historical evidence")
                    else:
                        self.assertFalse(legacy.exists())

    def test_missing_campaign_rejects_corrupt_legacy_without_import(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            legacy = root / "project_ledger.json"
            legacy.write_bytes(b"{corrupt historical evidence")
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.initialize()
            with self.assertRaises(LedgerDangerousStateError):
                SQLiteLedgerManager(
                    state_store=store, artifact_root=root, legacy_ledger_path=legacy,
                    campaign_id="workspace:active",
                )
            self.assertIsNone(store.load_campaign_ledger("workspace:active"))
            self.assertEqual(legacy.read_bytes(), b"{corrupt historical evidence")

    def test_sqlite_ledger_import_race_uses_persisted_payload_and_revision(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            legacy = root / "project_ledger.json"
            legacy.write_text(json.dumps({"tasks": {}, "symbols": {}, "marker": "old JSON"}), encoding="utf-8")
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.initialize()
            original_import = store.import_campaign_ledger

            def competing_import(**kwargs):
                original_import(**{**kwargs, "ledger": {"tasks": {}, "symbols": {}, "marker": "concurrent import"}})
                return original_import(**kwargs)

            with patch.object(store, "import_campaign_ledger", side_effect=competing_import):
                ledger = SQLiteLedgerManager(
                    state_store=store, artifact_root=root, legacy_ledger_path=legacy,
                    campaign_id="workspace:active",
                )
            self.assertEqual(ledger.ledger["marker"], "concurrent import")
            persisted, revision = store.load_campaign_ledger("workspace:active")
            self.assertEqual(ledger._db_revision, revision)
            ledger.save(force_empty_save=True)
            self.assertEqual(store.load_campaign_ledger("workspace:active")[0]["marker"], persisted["marker"])

    def test_existing_sqlite_ledger_rejects_incompatible_schema_without_legacy_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.import_campaign_ledger(
                campaign_id="workspace:active", artifact_root=root,
                ledger={"tasks": {}, "symbols": {}},
            )
            with store._connection(write=True) as connection:
                connection.execute("UPDATE meta SET value = '999' WHERE key = 'schema_version'")
            with patch.object(LedgerManager, "_load_ledger", side_effect=AssertionError("no legacy fallback")):
                with self.assertRaisesRegex(StateIntegrityError, "newer than supported"):
                    SQLiteLedgerManager(
                        state_store=WorkspaceStateStore(store.path), artifact_root=root,
                        legacy_ledger_path=root / "project_ledger.json", campaign_id="workspace:active",
                    )

    def test_read_only_missing_campaign_does_not_import_legacy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.initialize()
            before = store.path.read_bytes()
            with patch.object(LedgerManager, "_load_ledger", side_effect=AssertionError("no legacy fallback")):
                with self.assertRaises(LedgerDangerousStateError):
                    SQLiteLedgerManager(
                        state_store=store, artifact_root=root, legacy_ledger_path=root / "project_ledger.json",
                        campaign_id="workspace:active", read_only=True,
                    )
            self.assertEqual(store.path.read_bytes(), before)
            self.assertIsNone(store.load_campaign_ledger("workspace:active"))

    def test_sqlite_ledger_read_only_loads_without_initialize_and_rejects_writes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            legacy = root / "project_ledger.json"
            legacy.write_text(json.dumps({"tasks": {}, "symbols": {}}), encoding="utf-8")
            state_path = Path(tmp) / "runtime-artifacts" / "state.sqlite3"
            writer = SQLiteLedgerManager(
                state_store=WorkspaceStateStore(state_path),
                artifact_root=root,
                legacy_ledger_path=legacy,
            )
            writer.add_or_update_task(
                {
                    "block_id": "thm_5_1",
                    "type": "Theorem",
                    "title": "Read-only fixture",
                    "content": "A",
                    "source_plan": "chapter5",
                    "dependencies": [],
                }
            )
            before = state_path.read_bytes()
            read_store = WorkspaceStateStore(state_path)

            with patch.object(
                read_store,
                "initialize",
                side_effect=AssertionError("read-only ledger must not initialize state"),
            ):
                reader = SQLiteLedgerManager(
                    state_store=read_store,
                    artifact_root=root,
                    legacy_ledger_path=legacy,
                    read_only=True,
                )

            self.assertIn("thm_5_1", reader.ledger["tasks"])
            self.assertEqual(state_path.read_bytes(), before)
            with self.assertRaises(LedgerDangerousStateError):
                reader.save()
            with self.assertRaises(LedgerDangerousStateError):
                reader.update_status("thm_5_1", TaskStatus.LOCAL_FIXING)

    def test_sqlite_ledger_read_only_missing_database_does_not_create_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            state_path = Path(tmp) / "runtime-artifacts" / "state.sqlite3"

            with self.assertRaises(LedgerDangerousStateError):
                SQLiteLedgerManager(
                    state_store=WorkspaceStateStore(state_path),
                    artifact_root=root,
                    legacy_ledger_path=root / "project_ledger.json",
                    read_only=True,
                )

            self.assertFalse(state_path.exists())
            self.assertFalse(state_path.parent.exists())

    def test_corrupt_database_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.sqlite3"
            path.write_bytes(b"not sqlite")
            with self.assertRaises(StateIntegrityError):
                WorkspaceStateStore(path).summary()

    def test_review_apply_projection_queues_mat_without_touching_git(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            output = root / "ToyApollo" / "Output" / "thm_1_1.lean"
            pack = root / "phase2_prompt_packs" / "thm_1_1"
            output.parent.mkdir(parents=True)
            pack.mkdir(parents=True)
            code = "theorem t : True := by trivial\n"
            support_path = output.parent / "thm_1_1_support" / "core.lean"
            support_path.parent.mkdir()
            support_code = "theorem helper : True := by trivial\n"
            support_path.write_text(support_code, encoding="utf-8")
            output.write_text(code, encoding="utf-8")
            evidence = pack / "semantic_review_result_v1.json"
            evidence.write_text("{}\n", encoding="utf-8")

            class Settings:
                runtime_root = root
                phase2_prompt_packs_dir = root / "phase2_prompt_packs"
                state_db_file = Path(tmp) / "runtime-artifacts" / "state.sqlite3"

            WorkspaceStateStore(Settings.state_db_file).initialize()

            candidate = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={
                    str(pack / "candidate_v1.lean"): code,
                    "ToyApollo/Output/thm_1_1_support/core.lean": support_code,
                },
                primary_path=str(pack / "candidate_v1.lean"),
                source_repo="formalization_engine",
                layout="review_candidate",
            )
            review_input = {
                "prompt_version": 11,
                "rubric_version": 9,
                "review_subject_kind": "candidate",
                "subject_bundle": {
                    "task_id": "thm_1_1",
                    "primary_path": candidate.primary_path,
                    "primary_hash": candidate.primary_hash,
                    "bundle_hash": candidate.bundle_hash,
                    "files": candidate.manifest(),
                },
            }
            record_review_apply_state(
                settings=Settings,
                task_id="thm_1_1",
                review_input=review_input,
                semantic_review={
                    "verdict": "pass",
                    "phase2_status": "pass",
                    "proof_class": "faithful",
                    "completion_class": "complete",
                    "review_result_file": str(evidence),
                },
                candidate_path=pack / "candidate_v1.lean",
                candidate_code=code,
                success=True,
                final_build_success=True,
                disposition="promoted",
                output_path=output,
            )

            store = WorkspaceStateStore(Settings.state_db_file)
            report = store.task_report("thm_1_1")
            self.assertIsNotNone(report["head_review_coverage"].get("toy_reviewed"))
            reviewed_manifest = json.loads(report["heads"]["toy_reviewed"]["manifest_json"])
            self.assertEqual(len(reviewed_manifest), 2)
            queue = [item for item in report["integrations"] if item["integration_kind"] == "mat_promotion"]
            self.assertEqual(len(queue), 1)
            self.assertEqual(queue[0]["state"], "ready")
            self.assertFalse(queue[0]["detail_json"] == "{}")

    def test_review_apply_projection_uses_cordis_profile_without_mat_queue(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cordis"
            output = root / "Cordis" / "Foundations" / "EffectContext.lean"
            pack = Path(tmp) / "cordis-artifacts" / "phase2_prompt_packs" / "thm_4"
            output.parent.mkdir(parents=True)
            pack.mkdir(parents=True)
            code = "theorem theorem4_projection : True := by trivial\n"
            output.write_text(code, encoding="utf-8")
            evidence = pack / "semantic_review_result_v1.json"
            evidence.write_text("{}\n", encoding="utf-8")

            class Settings:
                runtime_root = root
                phase2_prompt_packs_dir = pack.parent
                state_db_file = Path(tmp) / "cordis-artifacts" / "state.sqlite3"
                profile = "cordis"
                supported_prompt_versions = (1,)
                supported_rubric_version = 1

            WorkspaceStateStore(Settings.state_db_file).initialize()

            candidate = SubjectBundle.from_files(
                task_id="thm_4",
                files={str(pack / "official_snapshot_v1.lean"): code},
                primary_path=str(pack / "official_snapshot_v1.lean"),
                source_repo="cordis",
                layout="review_official_output",
            )
            review_input = {
                "prompt_version": 1,
                "rubric_version": 1,
                "review_subject_kind": "official_output",
                "subject_bundle": {
                    "task_id": "thm_4",
                    "primary_path": candidate.primary_path,
                    "primary_hash": candidate.primary_hash,
                    "bundle_hash": candidate.bundle_hash,
                    "files": candidate.manifest(),
                },
            }
            record_review_apply_state(
                settings=Settings,
                task_id="thm_4",
                review_input=review_input,
                semantic_review={
                    "verdict": "pass",
                    "phase2_status": "pass",
                    "proof_class": "source_route_theorem",
                    "completion_class": "textbook_source_route_completed",
                    "review_result_file": str(evidence),
                },
                candidate_path=pack / "official_snapshot_v1.lean",
                candidate_code=code,
                success=True,
                final_build_success=True,
                disposition="accepted_existing_output",
                output_path=output,
            )

            report = WorkspaceStateStore(Settings.state_db_file).task_report("thm_4")
            self.assertIn("cordis_reviewed", report["head_review_coverage"])
            self.assertNotIn("toy_reviewed", report["heads"])
            self.assertEqual(report["integrations"], [])
            receipt = pack / "review_apply_receipt_v1.json"
            self.assertTrue(receipt.is_file())
            receipt_payload = json.loads(receipt.read_text(encoding="utf-8"))
            self.assertEqual(
                receipt_payload["schema_version"],
                "toy-apollo.phase2-review-apply-receipt.v1",
            )
            self.assertEqual(receipt_payload["reviewed_head_role"], "cordis_reviewed")

    def test_review_apply_requires_explicit_state_rebuild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            class Settings:
                runtime_root = root
                phase2_prompt_packs_dir = root / "phase2_prompt_packs"
                state_db_file = root / "runtime-artifacts" / "state.sqlite3"

            with self.assertRaises(StateDatabaseMissingError):
                record_review_apply_state(
                    settings=Settings,
                    task_id="thm_1_1",
                    review_input={},
                    semantic_review={},
                    candidate_path=root / "candidate.lean",
                    candidate_code="theorem t : True := by trivial\n",
                    success=False,
                    final_build_success=False,
                    disposition="blocked",
                    output_path=None,
                )
            self.assertFalse(Settings.state_db_file.exists())

    def test_migration_only_authorizes_review_with_matching_apply_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "evidence"
            pack = root / "phase2_prompt_packs" / "thm_1_1"
            pack.mkdir(parents=True)
            review = {
                "task_id": "thm_1_1",
                "verdict": "pass",
                "phase2_status": "pass",
                "candidate_hash": "candidate-hash",
                "review_input_hash": "input-hash",
            }
            review_path = pack / "semantic_review_result_v1.json"
            review_path.write_text(json.dumps(review, indent=2), encoding="utf-8")
            # The canonical alias is discovered first and has the same bytes,
            # but only the versioned path is named by the apply receipt.
            (pack / "semantic_review_result.json").write_text(
                json.dumps(review, indent=2), encoding="utf-8"
            )
            ledger = {
                "tasks": {
                    "thm_1_1": {
                        "status": "COMPLETED",
                        "latest_applied_review_result_file": str(review_path),
                        "latest_applied_review_result_hash": sha256_json(review),
                        "latest_applied_review_input_hash": "input-hash",
                        "latest_applied_review_subject_hash": "candidate-hash",
                        "latest_applied_review_post_basis_hash": "post-basis",
                        "latest_applied_review_subject_kind": "candidate",
                    }
                },
                "symbols": {},
            }
            (root / "project_ledger.json").write_text(json.dumps(ledger, indent=2), encoding="utf-8")
            state_path = Path(tmp) / "state.sqlite3"
            report = rebuild_workspace_database(
                state_path=state_path,
                workspace_root=Path(tmp),
                runtime_root=Path(tmp) / "runtime",
                roots=[root],
                refresh_remote=False,
            )
            self.assertFalse(report.errors)
            with closing(sqlite3.connect(state_path)) as connection:
                eligible = connection.execute("SELECT authority_eligible FROM reviews").fetchone()[0]
            self.assertEqual(eligible, 1)

            ledger["tasks"]["thm_1_1"]["latest_applied_review_input_hash"] = "wrong-input"
            (root / "project_ledger.json").write_text(json.dumps(ledger, indent=2), encoding="utf-8")
            rebuild_workspace_database(
                state_path=state_path,
                workspace_root=Path(tmp),
                runtime_root=Path(tmp) / "runtime",
                roots=[root],
                refresh_remote=False,
            )
            with closing(sqlite3.connect(state_path)) as connection:
                eligible = connection.execute("SELECT authority_eligible FROM reviews").fetchone()[0]
            self.assertEqual(eligible, 0)

    def test_migration_promotes_explicit_artifacts_ledger_to_workspace_active(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            artifacts = workspace / "toy-apollo-artifacts"
            runtime = workspace / "toy-apollo"
            artifacts.mkdir()
            active = {
                "tasks": {
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "status": "COMPLETED",
                        "source_plan": "chapter1",
                    }
                },
                "symbols": {},
            }
            legacy = artifacts / "project_ledger.json"
            legacy.write_text(json.dumps(active, indent=2), encoding="utf-8")
            state_path = artifacts / "state.sqlite3"
            rebuild_workspace_database(
                state_path=state_path,
                workspace_root=workspace,
                runtime_root=runtime,
                roots=[artifacts],
                refresh_remote=False,
            )

            loaded = WorkspaceStateStore(state_path).load_campaign_ledger("workspace:active")
            self.assertIsNotNone(loaded)
            self.assertIn("thm_1_1", loaded[0]["tasks"])


if __name__ == "__main__":
    unittest.main()
