from __future__ import annotations

import hashlib
import json
import subprocess
import unittest
import uuid
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

from tests.git_fixture_cleanup import remove_git_fixture_tree

from src.toy_apollo.state_bundle_delta import analyze_current_mat_bundles
from src.toy_apollo.state_evidence_bridge import (
    EVIDENCE_BRIDGE_INPUT_SCHEMA,
    EVIDENCE_BRIDGE_SCHEMA,
    FINAL122_BATCH_RECEIPT_SCHEMA,
    KENNETH_DECISION_SCHEMA,
    MAT_SYNC_DECISION_SCHEMA,
    ROUTE_A,
    ROUTE_B,
    EvidenceBridgeError,
    _named_declaration_occurrences,
    _validate_special_author_sync,
    _read_json,
    _snapshot_resolution,
    capture_final122_evidence_snapshot_graph,
    emit_final122_bridge_batch_receipt,
    build_evidence_bridge,
    inspect_evidence_bridge,
    build_final122_bridge_batch_receipt,
    validate_final122_bridge_batch_payload,
    validate_final122_bridge_batch_receipt,
    subject_payload,
    validate_evidence_bridge_receipt,
)
from src.toy_apollo.state_migration import (
    MigrationReport,
    discover_evidence_inventory,
    import_validated_evidence_bridge_receipt,
    import_validated_evidence_bridge_batch_receipt,
    rebuild_invariants,
)
from src.toy_apollo.state_store import (
    StateIntegrityError,
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
)
from src.toy_apollo.task_catalog import build_catalog


class EvidenceBridgeTests(unittest.TestCase):
    def test_special_author_sync_uses_manifest_named_current_triplet(self):
        target = SubjectBundle.from_files(
            task_id="ex_14_4_1",
            files={"Primary.lean": "theorem t : True := by trivial\n"},
            primary_path="Primary.lean", source_repo="mat", source_commit="a" * 40,
        )
        row = {
            "task_id": "ex_14_4_1",
            "disposition": "TYPED_AUTHOR_SYNC_BRIDGE_CONSTRUCTIBLE",
            "genuine_new_user_decision_required": False,
            "route": "author_full_scope_build_verified_snapshot_selection_then_reviewed_sync_reassembly",
            "current_target": {
                "commit": target.source_commit,
                "subject_id": target.subject_id,
                "bundle_manifest_sha256": target.bundle_hash,
                "provenance_manifest_sha256": target.primary_hash,
                "owned_file_count": len(target.files),
            },
            "immutable_author_selection": {
                "commit": "b" * 40,
                "tree": "c" * 40,
                "full_scope": [{
                    "path": "Primary.lean", "git_blob": "d" * 40,
                    "sha256": target.primary_hash,
                }],
            },
            "historical_review": {
                "candidate_sha256": target.primary_hash,
                "input": {"path": "input.json", "sha256": "1" * 64},
                "result": {"path": "result.json", "sha256": "2" * 64, "decision": "PASS"},
                "verify": {"path": "verify.json", "sha256": "3" * 64, "success": False},
            },
            "bridge_reason": "immutable author selection plus reviewed synchronization",
            "fail_closed_conditions": ["bind full scope"],
        }
        with patch("src.toy_apollo.state_evidence_bridge._check_file_ref", return_value={}):
            self.assertEqual(
                _validate_special_author_sync(row, task_id="ex_14_4_1", target=target)["decision_status"],
                "pass",
            )
            row["current_target"]["provenance_manifest_sha256"] = "0" * 64
            with self.assertRaisesRegex(EvidenceBridgeError, "special current target mismatch"):
                _validate_special_author_sync(row, task_id="ex_14_4_1", target=target)

    def test_final122_batch_emit_is_no_replace_and_validator_replays(self):
        with self._root() as root:
            index = self._write(root / "index.json", {"schema": "fixture"})
            target = SubjectBundle.from_files(
                task_id="thm_5_1", files={"T.lean": "theorem t : True := by trivial\n"},
                primary_path="T.lean", source_repo="mat", source_commit="a" * 40,
                layout="mat", subject_kind="catalog_git_bundle",
            )
            build = self._write(root / "build.json", {"schema": "fixture"})
            source = self._write(root / "source.json", {"schema": "fixture"})
            inspected = {
                "index": self._ref(index), "target_commit": "a" * 40,
                "repositories": {
                    "target": {"path": str(root), "commit": "a" * 40, "tree": "b" * 40},
                    "kenneth": {"path": str(root), "commit": "a" * 40, "tree": "b" * 40},
                },
                "items": [{
                    "task_id": "thm_5_1", "route": ROUTE_A, "target": subject_payload(target),
                    "source_manifest": {**self._ref(source), "item_pointer": "/items/0"},
                    "source_authority": {"source_schema": "fixture", "decision_status": "pass"},
                    "target_exact_build": self._ref(build),
                    "direct_consumers": {"consumer_task_ids": [], "unowned_module_coverage": {}},
                    "consumer_exact_builds": [],
                }],
            }
            output = root / "receipt.json"
            with (
                patch("src.toy_apollo.state_evidence_bridge.inspect_final122_minimal_index", return_value=inspected),
                patch("src.toy_apollo.state_evidence_bridge._run", return_value=("b" * 40 + "\n").encode()),
            ):
                dry_payload = build_final122_bridge_batch_receipt(
                    index, target_repo=root, kenneth_repo=root,
                    created_at="2026-08-08T00:00:00+00:00",
                )
                self.assertFalse(output.exists())
                self.assertEqual(
                    validate_final122_bridge_batch_payload(
                        dry_payload, target_repo=root, kenneth_repo=root,
                    )["count"],
                    1,
                )
                wrong_root = root / "wrong-kenneth"
                wrong_root.mkdir()
                with self.assertRaisesRegex(EvidenceBridgeError, "repository root/anchor mismatch"):
                    validate_final122_bridge_batch_payload(
                        dry_payload, target_repo=root, kenneth_repo=wrong_root,
                    )
                emitted = emit_final122_bridge_batch_receipt(
                    index, output, target_repo=root, kenneth_repo=root,
                    created_at="2026-08-08T00:00:00+00:00",
                )
                self.assertEqual(emitted["status"], "emitted")
                validated = validate_final122_bridge_batch_receipt(
                    output, target_repo=root, kenneth_repo=root,
                )
                self.assertEqual(validated["count"], 1)
                with self.assertRaises(Exception):
                    emit_final122_bridge_batch_receipt(
                        index, output, target_repo=root, kenneth_repo=root,
                        created_at="2026-08-08T00:00:00+00:00",
                    )

    def test_audit_v1_named_declaration_extractor_is_body_exact(self):
        source = b"""-- ignored\n/-- ignored -/\ndef def_5_5 : Prop := True\n\ntheorem later : True := by trivial\n"""
        self.assertEqual(
            _named_declaration_occurrences(source, "def_5_5"),
            [{
                "kind": "def", "name": "def_5_5", "normalized_line": 1,
                "token_count": 6,
                "token_sha256": sha256_json(["def", "def_5_5", ":", "Prop", ":=", "True"]),
            }],
        )

    @contextmanager
    def _root(self):
        root = Path(__file__).resolve().parents[1] / f"_tmp_evidence_bridge_{uuid.uuid4().hex}"
        root.mkdir()
        try:
            yield root
        finally:
            remove_git_fixture_tree(root)

    def _repo(self, root: Path, name: str, files: dict[str, str]) -> tuple[Path, str]:
        repo = root / name
        repo.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(["git", "config", "user.email", "fixture@example.invalid"], cwd=repo, check=True)
        subprocess.run(["git", "config", "user.name", "Fixture"], cwd=repo, check=True)
        for raw, content in files.items():
            path = repo / raw
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8", newline="\n")
        subprocess.run(["git", "add", "."], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=repo, check=True)
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        return repo, commit

    @staticmethod
    def _write(path: Path, payload: dict) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True), encoding="utf-8")
        return path

    @staticmethod
    def _ref(path: Path) -> dict[str, str]:
        return {"path": str(path.resolve()), "sha256": sha256_file(path)}

    @staticmethod
    def _catalog(mat_commit: str):
        plan = json.dumps(
            [{
                "block_id": "thm_5_1", "type": "Theorem_with_Proof",
                "title": "Fixture", "content": "Fixture", "dependencies": [],
                "source_plan": "fixture",
            }]
        ).encode("utf-8")
        manifest = (
            "group,chapter,file_path,basename,module_name,ledger_task_match,"
            "ledger_status,phase2_status,classification,axiom_count,sorry_or_admit_in_code\n"
            "ProbabilityTheory/chapter_05,5,ProbabilityTheory/chapter_05/thm_5_1.lean,"
            "thm_5_1,ProbabilityTheory.chapter_05.thm_5_1,yes,COMPLETED,pass,"
            "ledger_task_module,0,no\n"
        ).encode("utf-8")
        return build_catalog(
            catalog_name="fixture", toy_commit="1" * 40, mat_commit=mat_commit,
            plan_documents={"plans/fixture.json": plan}, manifest_bytes=manifest,
            family_overrides=[], restored_task_ids=[], legacy_cohort_id="legacy",
            mat_tree_paths=["ProbabilityTheory/chapter_05/thm_5_1.lean"],
        )

    def _fixture(self, root: Path, *, route: str = ROUTE_A, target_text: str | None = None):
        lean = "theorem bridge_fixture : True := by trivial\n"
        source_repo, source_commit = self._repo(
            root, "kenneth" if route == ROUTE_A else "mat_source",
            {"Probability/Chapter05/thm_5_1.lean": lean},
        )
        target_repo, target_commit = self._repo(
            root, "mat_target",
            {"ProbabilityTheory/chapter_05/thm_5_1.lean": target_text or lean},
        )
        kenneth_repo = source_repo
        kenneth_commit = source_commit
        if route == ROUTE_B:
            kenneth_repo, kenneth_commit = self._repo(
                root, "kenneth_anchor", {"Unrelated.lean": "theorem unrelated : True := by trivial\n"}
            )
        source_path = "Probability/Chapter05/thm_5_1.lean"
        target_path = "ProbabilityTheory/chapter_05/thm_5_1.lean"
        source = SubjectBundle.from_files(
            task_id="thm_5_1", files={source_path: lean}, primary_path=source_path,
            source_repo="kenneth" if route == ROUTE_A else "mat",
            source_commit=source_commit, layout="kenneth" if route == ROUTE_A else "mat",
            subject_kind="catalog_git_bundle",
        )
        target = SubjectBundle.from_files(
            task_id="thm_5_1", files={target_path: target_text or lean}, primary_path=target_path,
            source_repo="mat", source_commit=target_commit, layout="mat",
            subject_kind="catalog_git_bundle",
        )
        signature_hash = hashlib.sha256(
            json.dumps(["theorem", "bridge_fixture", ":", "True"], separators=(",", ":")).encode()
        ).hexdigest()
        # Use the implementation-computed declaration hash; keeping this in
        # the fixture avoids weakening production comparison for test setup.
        from src.toy_apollo.state_boundary_delta_receipt import _declaration_signatures
        signature_hash = _declaration_signatures(lean, {})[0]["signature_sha256"]
        unit = {
            "unit_id": "bridge_fixture", "owner_task": "thm_5_1",
            "source_hash": signature_hash, "target_hash": signature_hash,
        }
        if route == ROUTE_A:
            decision = {
                "schema": KENNETH_DECISION_SCHEMA, "task_id": "thm_5_1",
                "decision_kind": "author_exact", "exactness_mode": "complete_bundle_blob_exact",
                "complete_scope": True, "kenneth_commit": kenneth_commit,
                "source_subject_id": source.subject_id, "source_bundle_hash": source.bundle_hash,
                "target_subject_id": target.subject_id, "target_bundle_hash": target.bundle_hash,
                "matched_units": [{
                    "unit_id": "complete_bundle", "status": "exact",
                    "source_hash": source.primary_hash, "target_hash": target.primary_hash,
                }],
            }
            authority_type = "kenneth_git_author_exact"
        else:
            decision = {
                "schema": MAT_SYNC_DECISION_SCHEMA, "task_id": "thm_5_1",
                "decision_kind": "mat_sync_author_attested_selection",
                "author_controlled": True, "complete_scope": True, "no_later_conflict": True,
                "source_subject_id": source.subject_id, "source_bundle_hash": source.bundle_hash,
                "target_subject_id": target.subject_id, "target_bundle_hash": target.bundle_hash,
                "target_commit": target_commit, "sync_commits": [source_commit, target_commit],
            }
            authority_type = "mat_sync_author_attested_selection"
        decision_path = self._write(root / "decision.json", decision)
        build = {
            "schema": "mat.catalog.exact-build.v1", "task_id": "thm_5_1",
            "commit": target_commit, "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash, "primary_hash": target.primary_hash,
            "primary_path": target.primary_path, "subject_files": target.manifest(),
            "success": True, "exit_code": 0,
            "forbidden_token_scan": {"exit_code": 0, "findings": {}},
            "lean_tree_equivalence": {
                "target_commit": target_commit, "build_checkout_clean": True,
                "changed_lean_files": [],
            },
        }
        build_path = self._write(root / "target_build.json", build)
        consumers = {
            "schema": "mat.catalog.direct-consumer-manifest.v1", "task_id": "thm_5_1",
            "commit": target_commit, "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash, "consumers": [],
        }
        consumers_path = self._write(root / "consumers.json", consumers)
        checks = {
            key: "pass" for key in (
                "source_authority_validated", "source_complete_bundle",
                "target_complete_bundle_at_pinned_commit", "complete_scope_coverage",
                "ordered_lean_tokens_unchanged", "public_declarations_unchanged",
                "proof_support_scope_unchanged", "target_build_and_forbidden_scan",
                "direct_consumers_built_and_scanned", "no_semantic_or_rubric_upgrade",
            )
        }
        manifest = {
            "schema": EVIDENCE_BRIDGE_INPUT_SCHEMA, "task_id": "thm_5_1",
            "created_at": "2026-08-08T00:00:00+00:00", "bridge_route": route,
            "semantic_upgrade": False, "rubric_upgrade": False, "creates_review": False,
            "anchors": {"mat_commit": target_commit, "kenneth_commit": kenneth_commit},
            "source_authority": {
                "type": authority_type, "artifact": self._ref(decision_path),
                "decision": self._ref(decision_path),
            },
            "source_subject": subject_payload(source), "target_subject": subject_payload(target),
            "comparison": {
                "comparator": "strict_ordered_lean_tokens_and_declarations.v1",
                "status": "pass", "complete_scope": True,
                "module_rewrites": [],
                "reassembly_groups": [{
                    "group_id": "main", "source_paths": [source_path],
                    "target_paths": [target_path],
                }],
                "unmatched_source": [], "unmatched_target": [],
            },
            "proof_support_manifest": {
                "complete_scope": True, "ownership_partition": "pass", "carrier_closure": "pass",
                "declaration_pairs": [unit], "proof_pairs": [unit],
                "support_pairs": [], "zero_payload_shims": [],
            },
            "artifacts": {
                "target_build": self._ref(build_path),
                "direct_consumer_manifest": self._ref(consumers_path),
                "consumer_builds": [],
            },
            "checks": checks,
        }
        input_path = self._write(root / "evidence_bridge_input.json", manifest)
        return {
            "input": input_path, "source_repo": source_repo, "target_repo": target_repo,
            "kenneth_repo": kenneth_repo, "source": source, "target": target,
            "target_commit": target_commit, "decision": decision_path,
        }

    @staticmethod
    def _build(fixture):
        return build_evidence_bridge(
            fixture["input"], source_repos=[fixture["source_repo"]],
            target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
        )

    def test_A_inspect_and_receipt_replay_are_canonical(self):
        with self._root() as root:
            fixture = self._fixture(root)
            inspected = inspect_evidence_bridge(
                fixture["input"], source_repos=[fixture["source_repo"]],
                target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(inspected["status"], "ready_for_receipt_emission")
            self.assertEqual(inspected["bridge_route"], ROUTE_A)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", inspected["receipt"])
            receipt, source, target = validate_evidence_bridge_receipt(
                receipt_path, source_repos=[fixture["source_repo"]],
                target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(receipt["schema"], EVIDENCE_BRIDGE_SCHEMA)
            self.assertEqual(source.subject_id, fixture["source"].subject_id)
            self.assertEqual(target.subject_id, fixture["target"].subject_id)

    def test_B_sync_attested_is_typed_but_not_a_review(self):
        with self._root() as root:
            fixture = self._fixture(root, route=ROUTE_B)
            receipt, _source, target = self._build(fixture)
            self.assertEqual(receipt["bridge_route"], ROUTE_B)
            self.assertEqual(receipt["authority_scope"], "sync_author_attested_acceptance")
            self.assertFalse(receipt["creates_review"])
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.persist_catalog(self._catalog(fixture["target_commit"]))
            store.upsert_subject(target)
            store.set_task_head(task_id="thm_5_1", role="mat_main", subject_id=target.subject_id)
            import_validated_evidence_bridge_receipt(
                store, receipt_path, MigrationReport(database=str(store.path)),
                source_repos=[fixture["source_repo"]], target_repo=fixture["target_repo"],
                kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(
                store.authority_coverage(target.subject_id)["capability"],
                "sync_author_attested_acceptance",
            )
            self.assertIsNone(store.review_coverage(target.subject_id))

    def test_receipt_replay_accepts_only_sibling_worktree_repository_identity(self):
        with self._root() as root:
            fixture = self._fixture(root, route=ROUTE_B)
            clean_worktree = root / "target_clean_worktree"
            subprocess.run(
                [
                    "git",
                    "worktree",
                    "add",
                    "--detach",
                    str(clean_worktree),
                    fixture["target_commit"],
                ],
                cwd=fixture["target_repo"],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            receipt, _source, _target = build_evidence_bridge(
                fixture["input"],
                source_repos=[fixture["source_repo"]],
                target_repo=clean_worktree,
                kenneth_repo=fixture["kenneth_repo"],
            )
            receipt_path = self._write(
                root / "validated_evidence_bridge_receipt_v1.json", receipt
            )
            validated, _source, target = validate_evidence_bridge_receipt(
                receipt_path,
                source_repos=[fixture["source_repo"]],
                target_repo=fixture["target_repo"],
                kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(validated["task_id"], "thm_5_1")
            self.assertEqual(target.source_commit, fixture["target_commit"])

            unrelated_clone = root / "target_unrelated_clone"
            subprocess.run(
                ["git", "clone", "-q", str(fixture["target_repo"]), str(unrelated_clone)],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            with self.assertRaisesRegex(EvidenceBridgeError, "receipt differs"):
                validate_evidence_bridge_receipt(
                    receipt_path,
                    source_repos=[fixture["source_repo"]],
                    target_repo=unrelated_clone,
                    kenneth_repo=fixture["kenneth_repo"],
                )

    def test_C_route_rejects_before_artifact_or_state_access(self):
        with self._root() as root:
            fixture = self._fixture(root)
            manifest = json.loads(fixture["input"].read_text(encoding="utf-8"))
            manifest["bridge_route"] = "C"
            self._write(fixture["input"], manifest)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.initialize()
            before = store.summary()
            with self.assertRaisesRegex(EvidenceBridgeError, "C cannot be bridged"):
                build_evidence_bridge(
                    fixture["input"], source_repos=[fixture["source_repo"]],
                    target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
                )
            self.assertEqual(before, store.summary())
            forged_receipt = self._write(
                root / "validated_evidence_bridge_receipt_v1.json",
                {
                    "schema": EVIDENCE_BRIDGE_SCHEMA,
                    "created_at": "2026-08-08T00:00:00+00:00",
                    "orchestration": {"input_manifest": self._ref(fixture["input"])},
                },
            )
            with self.assertRaisesRegex(EvidenceBridgeError, "C cannot be bridged"):
                import_validated_evidence_bridge_receipt(
                    store, forged_receipt, MigrationReport(database=str(store.path)),
                    source_repos=[fixture["source_repo"]],
                    target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
                )
            self.assertEqual(before, store.summary())

    def test_semantic_payload_delta_is_fail_closed(self):
        with self._root() as root:
            fixture = self._fixture(root, target_text="theorem bridge_fixture : False := by trivial\n")
            with self.assertRaisesRegex(EvidenceBridgeError, "R_KENNETH|R_SEMANTIC_DELTA"):
                self._build(fixture)

    def test_authority_hash_mutation_rejects(self):
        with self._root() as root:
            fixture = self._fixture(root)
            decision = json.loads(fixture["decision"].read_text(encoding="utf-8"))
            decision["complete_scope"] = False
            self._write(fixture["decision"], decision)
            with self.assertRaisesRegex(EvidenceBridgeError, "path/hash mismatch"):
                self._build(fixture)

    def test_import_records_typed_binding_atomically_without_review_or_head_change(self):
        with self._root() as root:
            fixture = self._fixture(root)
            receipt, _source, target = self._build(fixture)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.persist_catalog(self._catalog(fixture["target_commit"]))
            store.upsert_subject(target)
            store.set_task_head(task_id="thm_5_1", role="mat_main", subject_id=target.subject_id)
            report = MigrationReport(database=str(store.path))
            import_validated_evidence_bridge_receipt(
                store, receipt_path, report,
                source_repos=[fixture["source_repo"]], target_repo=fixture["target_repo"],
                kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(report.evidence_bridge_receipts, 1)
            self.assertIsNone(store.review_coverage(target.subject_id))
            coverage = store.authority_coverage(target.subject_id)
            self.assertEqual(coverage["capability"], "author_current_exact_acceptance")
            invariants = rebuild_invariants(store, self._catalog(fixture["target_commit"]))
            self.assertTrue(invariants["typed_authority_bindings"]["valid"])
            self.assertEqual(invariants["exact_current_mat_typed_authority_coverage"], 1)
            self.assertEqual(invariants["exact_current_mat_bundle_coverage"], 1)
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM reviews").fetchone()[0], 0)
                head = connection.execute(
                    "SELECT subject_id FROM task_heads WHERE task_id='thm_5_1' AND role='mat_main'"
                ).fetchone()[0]
            self.assertEqual(head, target.subject_id)
            # Same bytes are idempotent; no duplicate binding is created.
            import_validated_evidence_bridge_receipt(
                store, receipt_path, report,
                source_repos=[fixture["source_repo"]], target_repo=fixture["target_repo"],
                kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(report.skipped, 1)
            self.assertEqual(store.summary()["authority_bindings"], 1)

    def test_store_rejects_conflicting_binding_without_overwrite(self):
        with self._root() as root:
            fixture = self._fixture(root)
            receipt, source, target = self._build(fixture)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.record_evidence_bridge_binding(
                source=source, target=target, bridge_route=ROUTE_A,
                authority_type="kenneth_git_author_exact",
                capability="author_current_exact_acceptance",
                decision_path=fixture["decision"], decision_hash=sha256_file(fixture["decision"]),
                evidence_path=receipt_path, evidence_hash=sha256_file(receipt_path),
                created_at=receipt["created_at"],
            )
            collision = self._write(root / "other.json", {"different": True})
            with self.assertRaises(StateIntegrityError):
                store.record_evidence_bridge_binding(
                    source=source, target=target, bridge_route=ROUTE_A,
                    authority_type="kenneth_git_author_exact",
                    capability="author_current_exact_acceptance",
                    decision_path=collision, decision_hash=sha256_file(collision),
                    evidence_path=collision, evidence_hash=sha256_file(collision),
                    created_at=receipt["created_at"],
                )
            self.assertEqual(store.summary()["authority_bindings"], 1)

    def test_bulk_caught_second_binding_conflict_leaves_no_partial_rows(self):
        with self._root() as root:
            fixture = self._fixture(root)
            receipt, source, target = self._build(fixture)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.record_evidence_bridge_binding(
                source=source, target=target, bridge_route=ROUTE_A,
                authority_type="kenneth_git_author_exact", capability="author_current_exact_acceptance",
                decision_path=fixture["decision"], decision_hash=sha256_file(fixture["decision"]),
                evidence_path=receipt_path, evidence_hash=sha256_file(receipt_path),
                created_at=receipt["created_at"],
            )
            before = store.summary()
            other = SubjectBundle.from_files(
                task_id=target.task_id, files={"Other.lean": "theorem other : True := by trivial\n"},
                primary_path="Other.lean", source_repo="kenneth",
                source_commit=source.source_commit, layout="kenneth",
            )
            with store.bulk_write():
                with self.assertRaises(StateIntegrityError):
                    store.record_evidence_bridge_binding(
                        source=other, target=target, bridge_route=ROUTE_A,
                        authority_type="kenneth_git_author_exact", capability="author_current_exact_acceptance",
                        decision_path=fixture["decision"], decision_hash=sha256_file(fixture["decision"]),
                        evidence_path=receipt_path, evidence_hash=sha256_file(receipt_path),
                        created_at=receipt["created_at"],
                    )
            self.assertEqual(before, store.summary())

    def test_malformed_binding_is_never_coverage(self):
        with self._root() as root:
            fixture = self._fixture(root)
            receipt, source, target = self._build(fixture)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.record_evidence_bridge_binding(
                source=source, target=target, bridge_route=ROUTE_A,
                authority_type="kenneth_git_author_exact", capability="author_current_exact_acceptance",
                decision_path=fixture["decision"], decision_hash=sha256_file(fixture["decision"]),
                evidence_path=receipt_path, evidence_hash=sha256_file(receipt_path),
                created_at=receipt["created_at"],
            )
            mutations = [
                ("authority_bindings", "bridge_route", ROUTE_B, ROUTE_A),
                ("authority_bindings", "authority_type", "mat_sync_author_attested_selection", "kenneth_git_author_exact"),
                ("authority_bindings", "capability", "sync_author_attested_acceptance", "author_current_exact_acceptance"),
                ("authority_bindings", "task_id", "prob_5_1", target.task_id),
                ("transformations", "source_subject_id", target.subject_id, source.subject_id),
                ("authority_bindings", "target_subject_id", source.subject_id, target.subject_id),
            ]
            for table, column, malformed, original in mutations:
                with self.subTest(column=column):
                    with store._connection(write=True) as connection:
                        connection.execute(f"UPDATE {table} SET {column} = ?", (malformed,))
                    self.assertFalse(store.validate_authority_bindings()["valid"])
                    self.assertIsNone(store.authority_coverage(target.subject_id))
                    with store._connection(write=True) as connection:
                        connection.execute(f"UPDATE {table} SET {column} = ?", (original,))
            store.record_review(
                task_id=target.task_id, subject_id=target.subject_id,
                verdict="fail", proof_class="fixture", completion_class="fixture",
                phase2_status="fail", evidence_path=receipt_path,
                evidence_hash=sha256_file(receipt_path), authority_eligible=False,
            )
            self.assertFalse(store.validate_authority_bindings()["valid"])
            self.assertIsNone(store.authority_coverage(target.subject_id))

    def test_bundle_delta_exposes_bridge_separately_from_review_coverage(self):
        with self._root() as root:
            fixture = self._fixture(root)
            receipt, source, target = self._build(fixture)
            receipt_path = self._write(root / "validated_evidence_bridge_receipt_v1.json", receipt)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.record_evidence_bridge_binding(
                source=source, target=target, bridge_route=ROUTE_A,
                authority_type="kenneth_git_author_exact",
                capability="author_current_exact_acceptance",
                decision_path=fixture["decision"], decision_hash=sha256_file(fixture["decision"]),
                evidence_path=receipt_path, evidence_hash=sha256_file(receipt_path),
                created_at=receipt["created_at"],
            )
            store.set_task_head(task_id="thm_5_1", role="mat_main", subject_id=target.subject_id)
            delta = analyze_current_mat_bundles(store, task_ids=["thm_5_1"])
            self.assertEqual(delta["tasks"][0]["status"], "validated_evidence_bridge")
            self.assertIsNone(store.review_coverage(target.subject_id))

    def test_inventory_discovers_only_canonical_bridge_receipt_prefix(self):
        with self._root() as root:
            canonical = self._write(root / "validated_evidence_bridge_receipt_v1.json", {"schema": EVIDENCE_BRIDGE_SCHEMA})
            self._write(root / "evidence_bridge_input.json", {"schema": EVIDENCE_BRIDGE_INPUT_SCHEMA})
            inventory = discover_evidence_inventory([root])
            self.assertEqual(inventory.evidence_bridge_receipts, (canonical.resolve(),))

    def test_inventory_and_batch_import_use_explicit_schema_and_one_marker(self):
        with self._root() as root:
            fixture = self._fixture(root)
            _receipt, _source, target = self._build(fixture)
            batch_path = self._write(
                root / "final122_evidence_bridge_batch_receipt_v1.json",
                {"schema": FINAL122_BATCH_RECEIPT_SCHEMA},
            )
            inventory = discover_evidence_inventory([root])
            self.assertEqual(inventory.evidence_bridge_batch_receipts, (batch_path.resolve(),))
            decision = self._ref(fixture["decision"])
            item = {
                "schema": EVIDENCE_BRIDGE_SCHEMA, "task_id": target.task_id,
                "created_at": "2026-08-08T00:00:00+00:00", "bridge_route": ROUTE_A,
                "source_authority": {
                    "type": "kenneth_git_author_exact",
                    "capability": "author_current_exact_acceptance", "decision": decision,
                },
                "target_subject": subject_payload(target),
            }
            validated = {
                "schema": FINAL122_BATCH_RECEIPT_SCHEMA, "count": 1, "items": [item],
            }
            digest = sha256_file(batch_path)
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.persist_catalog(self._catalog(fixture["target_commit"]))
            store.upsert_subject(target)
            store.set_task_head(task_id=target.task_id, role="mat_main", subject_id=target.subject_id)
            report = MigrationReport(database=str(store.path))
            with patch(
                "src.toy_apollo.state_migration.load_validated_final122_bridge_batch_receipt",
                return_value=(validated, digest),
            ):
                import_validated_evidence_bridge_batch_receipt(
                    store, batch_path, report,
                    target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
                )
            self.assertEqual(report.evidence_bridge_receipts, 1)
            self.assertEqual(report.evidence_bridge_batch_receipts, 1)
            with store._connection(write=False) as connection:
                marker = connection.execute(
                    "SELECT source_kind, record_count FROM imports WHERE source_path = ?",
                    (str(batch_path.resolve()),),
                ).fetchone()
            self.assertEqual(dict(marker), {
                "source_kind": "validated_evidence_bridge_batch_receipt", "record_count": 1,
            })

            # A matching path/hash is not sufficient for an idempotent skip:
            # marker type/count and the exact valid binding set are authoritative.
            with store._connection(write=True) as connection:
                connection.execute(
                    """
                    UPDATE imports SET source_kind = 'wrong_kind', record_count = 0
                    WHERE source_path = ?
                    """,
                    (str(batch_path.resolve()),),
                )
            before = store.summary()
            with patch(
                "src.toy_apollo.state_migration.load_validated_final122_bridge_batch_receipt",
                return_value=(validated, digest),
            ):
                with self.assertRaisesRegex(ValueError, "idempotent state mismatch"):
                    import_validated_evidence_bridge_batch_receipt(
                        store, batch_path, MigrationReport(database=str(store.path)),
                        target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
                    )
            self.assertEqual(store.summary(), before)

            with store._connection(write=True) as connection:
                connection.execute(
                    """
                    UPDATE imports
                    SET source_kind = 'validated_evidence_bridge_batch_receipt', record_count = 1
                    WHERE source_path = ?
                    """,
                    (str(batch_path.resolve()),),
                )
            replay = MigrationReport(database=str(store.path))
            with patch(
                "src.toy_apollo.state_migration.load_validated_final122_bridge_batch_receipt",
                return_value=(validated, digest),
            ):
                import_validated_evidence_bridge_batch_receipt(
                    store, batch_path, replay,
                    target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
                )
            self.assertEqual(replay.skipped, 1)
            self.assertEqual(replay.evidence_bridge_receipts, 0)

    def test_snapshot_graph_replays_captured_bytes_after_original_mutation(self):
        with self._root() as root:
            child = self._write(root / "child.json", {"schema": "child", "value": 1})
            index = self._write(root / "index.json", {
                "schema": "index", "child": self._ref(child),
            })
            collision_root = root / "collision"
            self._write(
                collision_root / "objects" / f"{sha256_file(index)}.json",
                {"schema": "wrong-bytes"},
            )
            with self.assertRaisesRegex(EvidenceBridgeError, "collision mismatch"):
                capture_final122_evidence_snapshot_graph(index, snapshot_root=collision_root)
            graph = capture_final122_evidence_snapshot_graph(index, snapshot_root=root / "snapshots")
            self._write(index, {"schema": "mutated"})
            self._write(child, {"schema": "mutated"})
            with _snapshot_resolution(graph):
                replayed = _read_json(index, label="fixture index")
                self.assertEqual(replayed["schema"], "index")
                child_entry = next(
                    entry for entry in graph
                    if Path(entry["original"]["path"]) == child.resolve()
                )
                child_snapshot = json.loads(Path(child_entry["snapshot"]["path"]).read_text(encoding="utf-8"))
                self.assertEqual(child_snapshot, {"schema": "child", "value": 1})


if __name__ == "__main__":
    unittest.main()
