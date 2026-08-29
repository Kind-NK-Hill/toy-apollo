import json
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, Mock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import (  # noqa: E402
    LedgerBasisRebindConflictError,
    TaskStatus,
)
from src.toy_apollo.phase2_basis_rebind import (  # noqa: E402
    AppliedReviewBasisRebindError,
    _materialize_receipt_before_cas,
    _next_receipt_path,
    _validate_accepted_output_advancement,
    _validate_added_consumer,
    rebase_accepted_output_advancements_to_chain_tip,
    rebase_review_basis_to_chain_tip,
    validate_applied_review_clean_pass,
    validate_downstream_additions_and_accepted_output_advancements,
    validate_downstream_only_additions,
    validate_pending_to_completed_enrichment,
    validate_pending_to_completed_advancements,
    validate_rebind_basis_delta,
    validate_rebind_basis_delta_with_accepted_output_advancements,
    validate_rebind_chain_tip,
)
from src.toy_apollo.phase2_pack_shared.io import sha256_json, sha256_text  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class AppliedReviewBasisRebindLedgerTests(Phase2ReviewTestSupport, unittest.TestCase):
    TASK_ID = "def_6_2"

    def test_receipt_materialization_failure_never_calls_ledger_cas(self):
        payload = b'{"complete": true}\n'
        for failure_point in ("open", "fsync"):
            with self.subTest(failure_point=failure_point), tempfile.TemporaryDirectory() as tmp:
                receipt_path = Path(tmp) / "basis_rebind_receipt_v1.json"
                land_cas = Mock(return_value={"landed": True})
                target = f"src.toy_apollo.phase2_basis_rebind.os.{failure_point}"
                with patch(target, side_effect=OSError(f"injected {failure_point} failure")):
                    with self.assertRaisesRegex(
                        AppliedReviewBasisRebindError,
                        "failed before ledger CAS",
                    ):
                        _materialize_receipt_before_cas(receipt_path, payload, land_cas)

                land_cas.assert_not_called()
                if failure_point == "fsync":
                    self.assertEqual(receipt_path.read_bytes(), payload)
                    self.assertEqual(
                        _next_receipt_path(receipt_path.parent).name,
                        "basis_rebind_receipt_v2.json",
                    )

    def test_cas_conflict_preserves_complete_unreferenced_orphan_and_skips_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt_path = Path(tmp) / "basis_rebind_receipt_v1.json"
            payload = b'{"complete": true}\n'
            land_cas = Mock(side_effect=LedgerBasisRebindConflictError("injected race"))

            with self.assertRaisesRegex(
                AppliedReviewBasisRebindError,
                "complete unreferenced orphan is preserved",
            ):
                _materialize_receipt_before_cas(receipt_path, payload, land_cas)

            land_cas.assert_called_once_with()
            self.assertEqual(receipt_path.read_bytes(), payload)
            self.assertEqual(
                _next_receipt_path(receipt_path.parent).name,
                "basis_rebind_receipt_v2.json",
            )

    def test_successful_cas_runs_only_after_exact_receipt_is_durable(self):
        with tempfile.TemporaryDirectory() as tmp:
            receipt_path = Path(tmp) / "basis_rebind_receipt_v1.json"
            payload = b'{"complete": true}\n'

            def assert_receipt_then_land() -> dict:
                self.assertTrue(receipt_path.exists())
                self.assertEqual(receipt_path.read_bytes(), payload)
                return {"landed": True}

            self.assertEqual(
                _materialize_receipt_before_cas(
                    receipt_path,
                    payload,
                    assert_receipt_then_land,
                ),
                {"landed": True},
            )

    def _setup_applied_pass(self, root: Path):
        ledger, _settings, _pack_dir, _output_path = self._setup_trivial_phase2_task(
            root,
            self.TASK_ID,
            completed=True,
        )
        ledger.update_status(self.TASK_ID, TaskStatus.COMPLETED)
        ledger.update_runtime_metadata(
            self.TASK_ID,
            phase2_status="pass",
            latest_applied_review_subject_hash="subject-hash",
            latest_applied_review_subject_kind="official_output",
            latest_applied_review_origin_basis_hash="origin-basis",
            latest_applied_review_post_basis_hash="old-basis",
            latest_applied_review_input_hash="input-hash",
            latest_applied_review_result_file="semantic_review_result_v1.json",
            latest_applied_review_result_hash="result-hash",
        )
        record = ledger.ledger["tasks"][self.TASK_ID]
        snapshot = record["candidate_snapshot"]
        payload = {
            "block_id": self.TASK_ID,
            "type": str(snapshot["type"]),
            "title": str(snapshot["title"]),
            "content": str(snapshot["content"]),
            "source_plan": str(snapshot["source_plan"]),
            "dependencies": list(snapshot["dependencies"]),
            "soft_imports": list(snapshot["soft_imports"]),
            "soft_imports_confirmed_at": str(record.get("soft_imports_confirmed_at", "")),
        }
        return ledger, payload

    def test_exact_cas_advances_only_post_basis_and_appends_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, payload = self._setup_applied_pass(Path(tmp))
            before = json.loads(json.dumps(ledger.ledger["tasks"][self.TASK_ID]))

            event = ledger.rebind_applied_review_basis(
                self.TASK_ID,
                expected_subject_hash="subject-hash",
                expected_subject_kind="official_output",
                expected_origin_basis_hash="origin-basis",
                expected_old_basis_hash="old-basis",
                replacement_basis_hash="new-basis",
                expected_input_hash="input-hash",
                expected_result_file="semantic_review_result_v1.json",
                expected_result_hash="result-hash",
                expected_rebind_revision=0,
                expected_rebind_tip_id="",
                expected_rebind_tip_receipt_sha256="",
                expected_dependencies=[],
                expected_task_payload=payload,
                receipt_event={"schema_version": "test", "rebind_id": "receipt-1"},
            )

            after = ledger.ledger["tasks"][self.TASK_ID]
            self.assertEqual(after["latest_applied_review_post_basis_hash"], "new-basis")
            self.assertEqual(after["applied_review_basis_rebind_history"], [event])
            self.assertEqual(after["latest_applied_review_basis_rebind"], event)
            self.assertEqual(after["applied_review_basis_rebind_revision"], 1)
            for field in (
                "status",
                "phase2_status",
                "latest_applied_review_subject_hash",
                "latest_applied_review_input_hash",
                "latest_applied_review_result_file",
                "latest_applied_review_result_hash",
            ):
                self.assertEqual(after[field], before[field])

    def test_cas_refuses_subject_basis_dependencies_or_payload_drift_atomically(self):
        mutations = {
            "subject_hash": {"expected_subject_hash": "wrong-subject"},
            "subject_kind": {"expected_subject_kind": "candidate"},
            "origin_basis_hash": {"expected_origin_basis_hash": "wrong-origin"},
            "old_basis_hash": {"expected_old_basis_hash": "wrong-basis"},
            "input_hash": {"expected_input_hash": "wrong-input"},
            "result_file": {"expected_result_file": "wrong-result.json"},
            "result_hash": {"expected_result_hash": "wrong-result"},
            "dependencies": {"expected_dependencies": ["def_6_1"]},
            "task_payload": {"expected_task_payload": {"block_id": self.TASK_ID}},
        }
        for label, overrides in mutations.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                ledger, payload = self._setup_applied_pass(Path(tmp))
                before = json.loads(json.dumps(ledger.ledger["tasks"][self.TASK_ID]))
                kwargs = {
                    "expected_subject_hash": "subject-hash",
                    "expected_subject_kind": "official_output",
                    "expected_origin_basis_hash": "origin-basis",
                    "expected_old_basis_hash": "old-basis",
                    "replacement_basis_hash": "new-basis",
                    "expected_input_hash": "input-hash",
                    "expected_result_file": "semantic_review_result_v1.json",
                    "expected_result_hash": "result-hash",
                    "expected_rebind_revision": 0,
                    "expected_rebind_tip_id": "",
                    "expected_rebind_tip_receipt_sha256": "",
                    "expected_dependencies": [],
                    "expected_task_payload": payload,
                    "receipt_event": {"schema_version": "test", "rebind_id": "receipt-1"},
                    **overrides,
                }

                with self.assertRaises(LedgerBasisRebindConflictError):
                    ledger.rebind_applied_review_basis(self.TASK_ID, **kwargs)

                self.assertEqual(ledger.ledger["tasks"][self.TASK_ID], before)

    def test_cas_refuses_atomic_review_provenance_or_chain_tip_race(self):
        mutations = {
            "input_hash": lambda task: task.update(latest_applied_review_input_hash="raced-input"),
            "result_file": lambda task: task.update(
                latest_applied_review_result_file="raced-result.json"
            ),
            "result_hash": lambda task: task.update(latest_applied_review_result_hash="raced-result"),
            "origin": lambda task: task.update(latest_applied_review_origin_basis_hash="raced-origin"),
            "subject_kind": lambda task: task.update(latest_applied_review_subject_kind="candidate"),
            "chain_tip": lambda task: task.update(
                applied_review_basis_rebind_history=[
                    {
                        "rebind_id": "raced-tip",
                        "receipt_sha256": "f" * 64,
                    }
                ],
                latest_applied_review_basis_rebind={
                    "rebind_id": "raced-tip",
                    "receipt_sha256": "f" * 64,
                },
                applied_review_basis_rebind_revision=1,
            ),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                ledger, payload = self._setup_applied_pass(Path(tmp))
                mutate(ledger.ledger["tasks"][self.TASK_ID])
                ledger.save()
                before = json.loads(json.dumps(ledger.ledger["tasks"][self.TASK_ID]))
                with self.assertRaises(LedgerBasisRebindConflictError):
                    ledger.rebind_applied_review_basis(
                        self.TASK_ID,
                        expected_subject_hash="subject-hash",
                        expected_subject_kind="official_output",
                        expected_origin_basis_hash="origin-basis",
                        expected_old_basis_hash="old-basis",
                        replacement_basis_hash="new-basis",
                        expected_input_hash="input-hash",
                        expected_result_file="semantic_review_result_v1.json",
                        expected_result_hash="result-hash",
                        expected_rebind_revision=0,
                        expected_rebind_tip_id="",
                        expected_rebind_tip_receipt_sha256="",
                        expected_dependencies=[],
                        expected_task_payload=payload,
                        receipt_event={"schema_version": "test", "rebind_id": "receipt-1"},
                    )
                self.assertEqual(ledger.ledger["tasks"][self.TASK_ID], before)

    @staticmethod
    def _basis(*, include_added: bool) -> dict:
        direct = [
            {
                "block_id": "thm_6_1",
                "relation": "hard_dependency",
                "type": "Theorem",
                "title": "Theorem",
                "source_plan": "19_chap6_simple_functions",
            }
        ]
        evidence = [
            {
                **direct[0],
                "official_output_file": "thm.lean",
                "official_output_exists": True,
                "official_output_hash": "thm-hash",
                "official_output_imports": ["import ToyApollo.Output.def_6_2"],
            }
        ]
        if include_added:
            added = {
                "block_id": "ex_6_1_1",
                "relation": "hard_dependency",
                "type": "Exercise",
                "title": "Exercise",
                "source_plan": "19_chap6_simple_functions",
            }
            direct.insert(0, added)
            evidence.insert(
                0,
                {
                    **added,
                    "official_output_file": "ex.lean",
                    "official_output_exists": True,
                    "official_output_hash": "ex-hash",
                    "official_output_imports": ["import ToyApollo.Output.def_6_2"],
                },
            )
        return {
            "task": {"block_id": "def_6_2", "dependencies": []},
            "review_subject_hash": "subject-hash",
            "policy": {"version": 1},
            "direct_downstream_consumers": direct,
            "downstream_evidence": {
                "direct_downstream_consumers": evidence,
                "downstream_import_scan_required_before_quarantine": True,
            },
        }

    def test_downstream_validator_accepts_only_strict_additions(self):
        additions = validate_downstream_only_additions(
            self._basis(include_added=False),
            self._basis(include_added=True),
        )
        self.assertEqual([item["consumer"]["block_id"] for item in additions], ["ex_6_1_1"])

    def test_downstream_validator_refuses_non_downstream_or_existing_evidence_drift(self):
        old = self._basis(include_added=False)
        for label, mutate in {
            "policy": lambda basis: basis["policy"].update(version=2),
            "old_evidence": lambda basis: basis["downstream_evidence"][
                "direct_downstream_consumers"
            ][1].update(official_output_hash="changed"),
            "not_strict": lambda basis: basis.update(self._basis(include_added=False)),
        }.items():
            with self.subTest(label=label):
                current = self._basis(include_added=True)
                mutate(current)
                with self.assertRaises(AppliedReviewBasisRebindError):
                    validate_downstream_only_additions(old, current)

    def test_downstream_validator_refuses_removal_or_upstream_drift(self):
        old = self._basis(include_added=True)
        for label, current in {
            "consumer_removal": self._basis(include_added=False),
            "upstream_task_drift": self._basis(include_added=True),
        }.items():
            with self.subTest(label=label):
                if label == "upstream_task_drift":
                    current["task"]["dependencies"] = ["def_6_1"]
                with self.assertRaises(AppliedReviewBasisRebindError):
                    validate_downstream_only_additions(old, current)

    def test_rebind_delta_accepts_official_retirement_normalization_plus_pending_addition(self):
        old = self._basis(include_added=False)
        old.update(
            {
                "proof_obligations": {},
                "required_evidence_classes": ["source_tex", "proof_obligations"],
                "route_inspection_gate": {
                    "policy": ["`proof_obligations.json` is checklist/review context only."],
                },
            }
        )
        current = self._basis(include_added=True)
        current.update(
            {
                "required_evidence_classes": ["source_tex"],
                "route_inspection_gate": {
                    "policy": [
                        "Historical `proof_obligations.json` files are inert audit artifacts: "
                        "never generate, bind, apply, or gate on them."
                    ],
                },
            }
        )

        additions, retirement_used = validate_rebind_basis_delta(old, current)

        self.assertTrue(retirement_used)
        self.assertEqual(
            [item["consumer"]["block_id"] for item in additions],
            ["ex_6_1_1"],
        )

    def test_rebind_delta_refuses_arbitrary_policy_drift_after_retirement_normalization(self):
        old = self._basis(include_added=False)
        current = self._basis(include_added=True)
        current["policy"]["version"] = 2

        with self.assertRaisesRegex(
            AppliedReviewBasisRebindError,
            "non-downstream semantic field changed",
        ):
            validate_rebind_basis_delta(old, current)

    def test_existing_consumer_accepted_output_advancement_is_exact_and_receipted(self):
        old = self._basis(include_added=False)
        current = json.loads(json.dumps(old))
        old_evidence = old["downstream_evidence"]["direct_downstream_consumers"][0]
        new_evidence = current["downstream_evidence"]["direct_downstream_consumers"][0]
        old_evidence["official_output_hash"] = "a" * 64
        new_evidence["official_output_hash"] = "b" * 64

        additions, advancements, retirement_used = (
            validate_rebind_basis_delta_with_accepted_output_advancements(old, current)
        )

        self.assertFalse(retirement_used)
        self.assertEqual(additions, [])
        self.assertEqual(len(advancements), 1)
        advancement = advancements[0]
        self.assertEqual(advancement["consumer"]["block_id"], "thm_6_1")
        self.assertEqual(advancement["old_official_output_hash"], "a" * 64)
        self.assertEqual(advancement["new_official_output_hash"], "b" * 64)
        self.assertEqual(advancement["old_evidence_hash"], sha256_json(old_evidence))
        self.assertEqual(advancement["new_evidence_hash"], sha256_json(new_evidence))

    def test_accepted_output_advancement_refuses_removal_upstream_or_non_output_drift(self):
        old = self._basis(include_added=True)
        cases = {
            "consumer_removal": self._basis(include_added=False),
            "upstream_task_drift": json.loads(json.dumps(old)),
            "non_output_evidence_drift": json.loads(json.dumps(old)),
        }
        cases["upstream_task_drift"]["task"]["dependencies"] = ["def_6_1"]
        cases["non_output_evidence_drift"]["downstream_evidence"][
            "direct_downstream_consumers"
        ][0]["official_output_file"] = "moved.lean"
        for label, current in cases.items():
            with self.subTest(label=label):
                with self.assertRaises(AppliedReviewBasisRebindError):
                    validate_downstream_additions_and_accepted_output_advancements(old, current)

    def test_accepted_output_advancement_rebases_to_exact_new_chain_tip(self):
        consumer = {
            "block_id": "thm_6_1",
            "relation": "hard_dependency",
            "type": "Theorem",
            "title": "Theorem",
            "source_plan": "19_chap6_simple_functions",
        }
        origin = {
            **consumer,
            "official_output_file": "thm.lean",
            "official_output_exists": True,
            "official_output_hash": "a" * 64,
            "official_output_imports": ["import ToyApollo.Output.def_6_2"],
        }
        prior = {**origin, "official_output_hash": "b" * 64}
        current = {**origin, "official_output_hash": "c" * 64}
        advancement = {
            "consumer": consumer,
            "old_evidence": origin,
            "new_evidence": current,
            "old_evidence_hash": sha256_json(origin),
            "new_evidence_hash": sha256_json(current),
            "old_official_output_hash": "a" * 64,
            "new_official_output_hash": "c" * 64,
        }
        chain_tip = {"receipt": {"identity": {"post_downstream_evidence": [prior]}}}

        rebound = rebase_accepted_output_advancements_to_chain_tip([advancement], chain_tip)

        self.assertEqual(rebound[0]["old_evidence"], prior)
        self.assertEqual(rebound[0]["old_evidence_hash"], sha256_json(prior))
        self.assertEqual(rebound[0]["old_official_output_hash"], "b" * 64)

    def test_effective_old_basis_catches_chain_added_consumer_removal_or_descriptor_drift(self):
        origin = self._basis(include_added=False)
        tip_basis = self._basis(include_added=True)
        additions = validate_downstream_only_additions(origin, tip_basis)
        chain_tip = {"receipt": {"identity": {"added_consumers": additions}}}
        effective = rebase_review_basis_to_chain_tip(
            origin,
            chain_tip,
            expected_post_basis_hash=sha256_json(tip_basis),
        )
        self.assertEqual(effective, tip_basis)

        descriptor_drift = json.loads(json.dumps(tip_basis))
        descriptor_drift["direct_downstream_consumers"][0]["title"] = "Changed"
        descriptor_drift["downstream_evidence"]["direct_downstream_consumers"][0][
            "title"
        ] = "Changed"
        for label, current in {
            "removal": self._basis(include_added=False),
            "descriptor": descriptor_drift,
        }.items():
            with self.subTest(label=label):
                with self.assertRaises(AppliedReviewBasisRebindError):
                    validate_downstream_additions_and_accepted_output_advancements(
                        effective,
                        current,
                    )

    def test_chain_added_consumer_output_change_is_an_advancement_not_an_addition(self):
        origin = self._basis(include_added=False)
        tip_basis = self._basis(include_added=True)
        tip_basis["downstream_evidence"]["direct_downstream_consumers"][0][
            "official_output_hash"
        ] = "a" * 64
        additions = validate_downstream_only_additions(origin, tip_basis)
        chain_tip = {
            "receipt": {
                "identity": {
                    "added_consumers": additions,
                    "post_direct_downstream_consumers": tip_basis[
                        "direct_downstream_consumers"
                    ],
                    "post_downstream_evidence": tip_basis["downstream_evidence"][
                        "direct_downstream_consumers"
                    ],
                }
            }
        }
        effective = rebase_review_basis_to_chain_tip(
            origin,
            chain_tip,
            expected_post_basis_hash=sha256_json(tip_basis),
        )
        current = json.loads(json.dumps(tip_basis))
        current["downstream_evidence"]["direct_downstream_consumers"][0][
            "official_output_hash"
        ] = "b" * 64

        new_additions, advancements = (
            validate_downstream_additions_and_accepted_output_advancements(
                effective,
                current,
            )
        )

        self.assertEqual(new_additions, [])
        self.assertEqual([item["consumer"]["block_id"] for item in advancements], ["ex_6_1_1"])
        self.assertEqual(advancements[0]["old_official_output_hash"], "a" * 64)
        self.assertEqual(advancements[0]["new_official_output_hash"], "b" * 64)

    def test_staggered_multi_consumer_advancement_compares_only_tip_to_current(self):
        origin = self._basis(include_added=True)
        origin_evidence = origin["downstream_evidence"]["direct_downstream_consumers"]
        origin_evidence[0]["official_output_hash"] = "a" * 64
        origin_evidence[1]["official_output_hash"] = "c" * 64
        tip_basis = json.loads(json.dumps(origin))
        tip_basis["downstream_evidence"]["direct_downstream_consumers"][0][
            "official_output_hash"
        ] = "b" * 64
        chain_tip = {
            "receipt": {
                "identity": {
                    "post_direct_downstream_consumers": tip_basis[
                        "direct_downstream_consumers"
                    ],
                    "post_downstream_evidence": tip_basis["downstream_evidence"][
                        "direct_downstream_consumers"
                    ],
                }
            }
        }
        effective = rebase_review_basis_to_chain_tip(
            origin,
            chain_tip,
            expected_post_basis_hash=sha256_json(tip_basis),
        )
        current = json.loads(json.dumps(tip_basis))
        current["downstream_evidence"]["direct_downstream_consumers"][1][
            "official_output_hash"
        ] = "d" * 64

        additions, advancements = validate_downstream_additions_and_accepted_output_advancements(
            effective,
            current,
        )

        self.assertEqual(additions, [])
        self.assertEqual([item["consumer"]["block_id"] for item in advancements], ["thm_6_1"])

    def test_tip_declared_pending_consumer_can_advance_from_empty_to_reviewed_output(self):
        pending = self._basis(include_added=False)
        old_evidence = pending["downstream_evidence"]["direct_downstream_consumers"][0]
        old_evidence.update(
            {
                "official_output_file": "",
                "official_output_exists": False,
                "official_output_hash": "",
                "official_output_imports": [],
            }
        )
        completed = json.loads(json.dumps(pending))
        completed_evidence = completed["downstream_evidence"]["direct_downstream_consumers"][0]
        completed_evidence.update(
            {
                "official_output_file": "thm.lean",
                "official_output_exists": True,
                "official_output_hash": "b" * 64,
                "official_output_imports": ["import ToyApollo.Output.def_6_2"],
            }
        )

        additions, advancements = validate_downstream_additions_and_accepted_output_advancements(
            pending,
            completed,
            pending_to_completed_ids={"thm_6_1"},
        )

        self.assertEqual(additions, [])
        self.assertEqual(len(advancements), 1)
        self.assertEqual(advancements[0]["old_official_output_hash"], "")
        self.assertEqual(advancements[0]["new_official_output_hash"], "b" * 64)
        self.assertEqual(
            advancements[0]["transition_kind"],
            "pending_to_completed_accepted_output",
        )

    def test_pending_completion_allowance_refuses_generic_cross_id_reverse_or_dirty_empty_evidence(self):
        pending = self._basis(include_added=False)
        old_evidence = pending["downstream_evidence"]["direct_downstream_consumers"][0]
        old_evidence.update(
            {
                "official_output_file": "",
                "official_output_exists": False,
                "official_output_hash": "",
                "official_output_imports": [],
            }
        )
        completed = json.loads(json.dumps(pending))
        completed["downstream_evidence"]["direct_downstream_consumers"][0].update(
            {
                "official_output_file": "thm.lean",
                "official_output_exists": True,
                "official_output_hash": "b" * 64,
                "official_output_imports": ["import ToyApollo.Output.def_6_2"],
            }
        )
        dirty_pending = json.loads(json.dumps(pending))
        dirty_pending["downstream_evidence"]["direct_downstream_consumers"][0][
            "official_output_file"
        ] = "stale-shadow.lean"
        cases = (
            ("generic", pending, completed, set()),
            ("cross_id", pending, completed, {"ex_6_1_1"}),
            ("reverse", completed, pending, {"thm_6_1"}),
            ("dirty_empty", dirty_pending, completed, {"thm_6_1"}),
        )
        for label, old, new, pending_ids in cases:
            with self.subTest(label=label):
                with self.assertRaises(AppliedReviewBasisRebindError):
                    validate_downstream_additions_and_accepted_output_advancements(
                        old,
                        new,
                        pending_to_completed_ids=pending_ids,
                    )

    def test_completed_consumer_refuses_legacy_shadow_when_canonical_output_is_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, addition = self._pending_consumer_fixture(
                root,
                dependencies=["def_6_2"],
            )
            shadow = settings.output_lean_files_dir / "general" / "ex_6_1_1.lean"
            shadow.parent.mkdir(parents=True)
            shadow_text = "import ToyApollo.Output.def_6_2\n"
            shadow.write_text(shadow_text, encoding="utf-8")
            shadow_hash = sha256_text(shadow_text)
            ledger.ledger["tasks"]["ex_6_1_1"].update(
                {
                    "status": TaskStatus.COMPLETED.value,
                    "phase2_status": "pass",
                    "latest_applied_review_subject_hash": shadow_hash,
                }
            )
            addition["evidence"].update(
                {
                    "official_output_exists": True,
                    "official_output_file": str(shadow),
                    "official_output_hash": shadow_hash,
                    "official_output_imports": ["import ToyApollo.Output.def_6_2"],
                }
            )

            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "no official output"):
                _validate_added_consumer(
                    task_id="def_6_2",
                    addition=addition,
                    ledger=ledger,
                    settings=settings,
                )

    @staticmethod
    def _pending_consumer_fixture(root: Path, *, dependencies: list[str]):
        plans_dir = root / "plans"
        plans_dir.mkdir()
        task = {
            "block_id": "ex_6_1_1",
            "type": "Exercise",
            "title": "Exercise",
            "content": "Pending downstream exercise.",
            "dependencies": dependencies,
            "soft_imports": [],
            "source_plan": "19_chap6_simple_functions",
        }
        (plans_dir / "19_chap6_simple_functions_plan.json").write_text(
            json.dumps([task]),
            encoding="utf-8",
        )
        settings = SimpleNamespace(
            plans_dir=plans_dir,
            phase2_prompt_packs_dir=root / "phase2_prompt_packs",
            toyapollo_output_dir=root / "ToyApollo" / "Output",
            output_lean_files_dir=root / "output_lean_files",
        )
        ledger = SimpleNamespace(
            ledger={
                "tasks": {
                    "ex_6_1_1": {
                        "block_id": "ex_6_1_1",
                        "status": TaskStatus.DISCOVERED.value,
                        "phase2_status": "",
                        "candidate_snapshot": task,
                    }
                }
            }
        )
        addition = {
            "consumer": {
                "block_id": "ex_6_1_1",
                "relation": "hard_dependency",
            },
            "evidence": {
                "block_id": "ex_6_1_1",
                "relation": "hard_dependency",
                "official_output_exists": False,
                "official_output_file": "",
                "official_output_hash": "",
                "official_output_imports": [],
            },
        }
        return ledger, settings, addition

    def test_added_pending_planned_consumer_is_accepted_without_completion_claim(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, addition = self._pending_consumer_fixture(
                Path(tmp),
                dependencies=["def_6_2"],
            )

            validation = _validate_added_consumer(
                task_id="def_6_2",
                addition=addition,
                ledger=ledger,
                settings=settings,
            )

        self.assertEqual(validation["validation_mode"], "pending_authoritative_plan")
        self.assertFalse(validation["completion_claimed"])
        self.assertFalse(validation["official_import_verified"])

    def test_added_pending_consumer_without_authoritative_hard_dep_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, addition = self._pending_consumer_fixture(
                Path(tmp),
                dependencies=[],
            )

            with self.assertRaisesRegex(
                AppliedReviewBasisRebindError,
                "authoritative plan",
            ):
                _validate_added_consumer(
                    task_id="def_6_2",
                    addition=addition,
                    ledger=ledger,
                    settings=settings,
                )

    def test_added_retired_consumer_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, addition = self._pending_consumer_fixture(
                Path(tmp),
                dependencies=["def_6_2"],
            )
            ledger.ledger["tasks"]["ex_6_1_1"]["status"] = TaskStatus.ORPHANED.value

            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "ORPHANED"):
                _validate_added_consumer(
                    task_id="def_6_2",
                    addition=addition,
                    ledger=ledger,
                    settings=settings,
                )

    @staticmethod
    def _write_pending_rebind_tip(
        pack_dir: Path,
        *,
        origin_hash: str,
        pending_hash: str,
    ) -> tuple[dict, dict, list[dict]]:
        addition = {
            "consumer": {
                "block_id": "ex_6_1_1",
                "relation": "hard_dependency",
                "type": "Exercise",
                "title": "Exercise",
                "source_plan": "19_chap6_simple_functions",
            },
            "evidence": {
                "block_id": "ex_6_1_1",
                "relation": "hard_dependency",
                "type": "Exercise",
                "title": "Exercise",
                "source_plan": "19_chap6_simple_functions",
                "official_output_file": "old-ex.lean",
                "official_output_exists": True,
                "official_output_hash": "old-output-hash",
                "official_output_imports": ["import Mathlib"],
            },
        }
        validation = {
            "block_id": "ex_6_1_1",
            "validation_mode": "pending_authoritative_plan",
            "completion_claimed": False,
            "official_import_verified": False,
        }
        identity = {
            "task_id": "def_6_2",
            "old_basis_hash": origin_hash,
            "new_basis_hash": pending_hash,
            "added_consumers": [addition],
            "added_consumer_validations": [validation],
        }
        receipt = {
            "schema_version": "phase2.applied_review_basis_rebind.v2",
            "rebind_id": sha256_json(identity),
            "identity": identity,
            "basis_delta_components": {
                "pending_consumers": ["ex_6_1_1"],
            },
        }
        receipt_path = pack_dir / "basis_rebind_receipt_v1.json"
        receipt_bytes = (json.dumps(receipt, indent=2) + "\n").encode("utf-8")
        receipt_path.write_bytes(receipt_bytes)
        event = {
            **receipt,
            "task_id": "def_6_2",
            "previous_post_basis_hash": origin_hash,
            "replacement_post_basis_hash": pending_hash,
            "preserved_semantic_review": True,
            "receipt_file": str(receipt_path),
            "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(),
        }
        record = {
            "latest_applied_review_post_basis_hash": pending_hash,
            "applied_review_basis_rebind_history": [event],
        }
        return record, receipt, [addition]

    def test_valid_second_hop_requires_exact_tip_and_completed_same_consumer(self):
        with tempfile.TemporaryDirectory() as tmp:
            pack_dir = Path(tmp) / "phase2_prompt_packs" / "def_6_2"
            pack_dir.mkdir(parents=True)
            origin_hash = "a" * 64
            pending_hash = "b" * 64
            record, previous_receipt, additions = self._write_pending_rebind_tip(
                pack_dir,
                origin_hash=origin_hash,
                pending_hash=pending_hash,
            )

            tip = validate_rebind_chain_tip(
                record,
                task_id="def_6_2",
                pack_dir=pack_dir,
                origin_basis_hash=origin_hash,
                expected_current_post_basis_hash=pending_hash,
            )
            validations = [
                {
                    "block_id": "ex_6_1_1",
                    "validation_mode": "completed_pass_import_verified",
                    "completion_claimed": True,
                    "official_import_verified": True,
                }
            ]
            validate_pending_to_completed_enrichment(
                previous_receipt,
                additions,
                validations,
            )

        self.assertIsNotNone(tip)
        self.assertEqual(tip["receipt"]["rebind_id"], previous_receipt["rebind_id"])

    def test_second_hop_refuses_stale_or_branched_tip(self):
        with tempfile.TemporaryDirectory() as tmp:
            pack_dir = Path(tmp) / "phase2_prompt_packs" / "def_6_2"
            pack_dir.mkdir(parents=True)
            origin_hash = "a" * 64
            pending_hash = "b" * 64
            record, _receipt, _additions = self._write_pending_rebind_tip(
                pack_dir,
                origin_hash=origin_hash,
                pending_hash=pending_hash,
            )
            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "tip"):
                validate_rebind_chain_tip(
                    record,
                    task_id="def_6_2",
                    pack_dir=pack_dir,
                    origin_basis_hash=origin_hash,
                    expected_current_post_basis_hash="c" * 64,
                )

            branched = json.loads(json.dumps(record))
            branched["applied_review_basis_rebind_history"].append(
                {
                    "previous_post_basis_hash": "d" * 64,
                    "replacement_post_basis_hash": "e" * 64,
                }
            )
            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "stale or branched"):
                validate_rebind_chain_tip(
                    branched,
                    task_id="def_6_2",
                    pack_dir=pack_dir,
                    origin_basis_hash=origin_hash,
                    expected_current_post_basis_hash="e" * 64,
                )

    @staticmethod
    def _completed_consumer_fixture(root: Path, *, import_line: str):
        ledger, settings, addition = AppliedReviewBasisRebindLedgerTests._pending_consumer_fixture(
            root,
            dependencies=["def_6_2"],
        )
        output_path = settings.toyapollo_output_dir / "ex_6_1_1.lean"
        output_path.parent.mkdir(parents=True)
        output_text = f"{import_line}\n\ntheorem downstream : True := by trivial\n"
        output_path.write_text(output_text, encoding="utf-8")
        output_hash = sha256_text(output_text)
        record = ledger.ledger["tasks"]["ex_6_1_1"]
        record.update(
            {
                "status": TaskStatus.COMPLETED.value,
                "phase2_status": "pass",
                "latest_applied_review_subject_hash": output_hash,
            }
        )
        addition["evidence"].update(
            {
                "official_output_exists": True,
                "official_output_file": str(output_path),
                "official_output_hash": output_hash,
                "official_output_imports": [import_line],
            }
        )
        return ledger, settings, addition

    @staticmethod
    def _bind_completed_consumer_review(ledger, settings, addition):
        from tests.test_phase2_review_decision import Phase2ReviewDecisionTests

        consumer_id = addition["consumer"]["block_id"]
        output_path = Path(addition["evidence"]["official_output_file"])
        output_text = output_path.read_text(encoding="utf-8")
        output_hash = sha256_text(output_text)
        fixture = Phase2ReviewDecisionTests()
        review_input = fixture._review_input(task_id=consumer_id, task_type="Exercise")
        pack_dir = settings.phase2_prompt_packs_dir / consumer_id
        pack_dir.mkdir(parents=True)
        input_path = pack_dir / "semantic_review_input_v1.json"
        result_path = pack_dir / "semantic_review_result_v1.json"
        review_input.update(
            {
                "review_subject_kind": "candidate",
                "review_subject_file": str(output_path),
                "review_subject_hash": output_hash,
                "review_context_file": str(pack_dir / "semantic_review_context_v1.md"),
                "candidate": {
                    "file": str(output_path),
                    "hash": output_hash,
                    "lean": output_text,
                },
            }
        )
        result = fixture._raw_result(review_input)
        result["review_input_file"] = str(input_path)
        input_path.write_text(
            json.dumps(review_input, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        result_path.write_text(
            json.dumps(result, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        ledger.ledger["tasks"][consumer_id].update(
            {
                "latest_applied_review_subject_kind": "candidate",
                "latest_applied_review_input_hash": sha256_json(review_input),
                "latest_applied_review_result_file": str(result_path),
                "latest_applied_review_result_hash": sha256_json(result),
            }
        )

    @staticmethod
    def _accepted_output_advancement(addition, *, old_hash: str = "a" * 64):
        new_evidence = json.loads(json.dumps(addition["evidence"]))
        old_evidence = {**new_evidence, "official_output_hash": old_hash}
        return {
            "consumer": json.loads(json.dumps(addition["consumer"])),
            "old_evidence": old_evidence,
            "new_evidence": new_evidence,
            "old_evidence_hash": sha256_json(old_evidence),
            "new_evidence_hash": sha256_json(new_evidence),
            "old_official_output_hash": old_hash,
            "new_official_output_hash": new_evidence["official_output_hash"],
        }

    def test_existing_consumer_advancement_requires_completed_pass_import_and_review_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, addition = self._completed_consumer_fixture(
                Path(tmp),
                import_line="import ToyApollo.Output.def_6_2",
            )
            self._bind_completed_consumer_review(ledger, settings, addition)
            advancement = self._accepted_output_advancement(addition)

            validation = _validate_accepted_output_advancement(
                task_id="def_6_2",
                advancement=advancement,
                ledger=ledger,
                settings=settings,
            )

        self.assertEqual(
            validation["validation_mode"],
            "existing_consumer_accepted_output_advancement",
        )
        self.assertTrue(validation["completion_claimed"])
        self.assertTrue(validation["official_import_verified"])
        self.assertEqual(validation["review_binding"]["review_verdict"], "pass")

    def test_existing_consumer_advancement_refuses_nonpass_no_hard_dep_output_or_import_mismatch(self):
        cases = (
            "nonpass",
            "no_hard_dep",
            "output_mismatch",
            "import_mismatch",
            "receipt_mismatch",
            "candidate_text_mismatch",
            "candidate_hash_mismatch",
        )
        for label in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                dependencies = [] if label == "no_hard_dep" else ["def_6_2"]
                import_line = "import Mathlib" if label == "import_mismatch" else "import ToyApollo.Output.def_6_2"
                ledger, settings, addition = self._completed_consumer_fixture(
                    Path(tmp),
                    import_line=import_line,
                )
                self._bind_completed_consumer_review(ledger, settings, addition)
                advancement = self._accepted_output_advancement(addition)
                record = ledger.ledger["tasks"]["ex_6_1_1"]
                if label == "nonpass":
                    record["phase2_status"] = "fail"
                elif label == "no_hard_dep":
                    plan_path = settings.plans_dir / "19_chap6_simple_functions_plan.json"
                    plan = json.loads(plan_path.read_text(encoding="utf-8"))
                    plan[0]["dependencies"] = dependencies
                    plan_path.write_text(json.dumps(plan), encoding="utf-8")
                    record["candidate_snapshot"]["dependencies"] = dependencies
                elif label == "output_mismatch":
                    advancement["new_evidence"]["official_output_hash"] = "c" * 64
                elif label == "receipt_mismatch":
                    record["latest_applied_review_result_hash"] = "d" * 64
                elif label in {"candidate_text_mismatch", "candidate_hash_mismatch"}:
                    result_path = Path(record["latest_applied_review_result_file"])
                    result = json.loads(result_path.read_text(encoding="utf-8"))
                    input_path = Path(result["review_input_file"])
                    review_input = json.loads(input_path.read_text(encoding="utf-8"))
                    if label == "candidate_text_mismatch":
                        review_input["candidate"]["lean"] += "\n-- stale candidate text\n"
                    else:
                        review_input["candidate"]["hash"] = "e" * 64
                        result["candidate_hash"] = "e" * 64
                    result["review_input_hash"] = sha256_json(review_input)
                    input_path.write_text(
                        json.dumps(review_input, indent=2, ensure_ascii=False) + "\n",
                        encoding="utf-8",
                    )
                    result_path.write_text(
                        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
                        encoding="utf-8",
                    )
                    record["latest_applied_review_input_hash"] = sha256_json(review_input)
                    record["latest_applied_review_result_hash"] = sha256_json(result)

                with self.assertRaises(AppliedReviewBasisRebindError):
                    _validate_accepted_output_advancement(
                        task_id="def_6_2",
                        advancement=advancement,
                        ledger=ledger,
                        settings=settings,
                    )

    def test_second_hop_refuses_consumer_downgrade_output_or_import_mismatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, addition = self._completed_consumer_fixture(
                root,
                import_line="import ToyApollo.Output.def_6_2",
            )
            completed = _validate_added_consumer(
                task_id="def_6_2",
                addition=addition,
                ledger=ledger,
                settings=settings,
            )
            previous_receipt = {
                "identity": {
                    "added_consumers": [addition],
                    "added_consumer_validations": [
                        {
                            "block_id": "ex_6_1_1",
                            "validation_mode": "pending_authoritative_plan",
                            "completion_claimed": False,
                            "official_import_verified": False,
                        }
                    ],
                }
            }
            downgraded = {
                **completed,
                "validation_mode": "pending_authoritative_plan",
                "completion_claimed": False,
                "official_import_verified": False,
            }
            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "did not enrich"):
                validate_pending_to_completed_enrichment(
                    previous_receipt,
                    [addition],
                    [downgraded],
                )

            addition["evidence"]["official_output_hash"] = "mismatch"
            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "output hash changed"):
                _validate_added_consumer(
                    task_id="def_6_2",
                    addition=addition,
                    ledger=ledger,
                    settings=settings,
                )

        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, addition = self._completed_consumer_fixture(
                Path(tmp),
                import_line="import Mathlib",
            )
            with self.assertRaisesRegex(AppliedReviewBasisRebindError, "does not import"):
                _validate_added_consumer(
                    task_id="def_6_2",
                    addition=addition,
                    ledger=ledger,
                    settings=settings,
                )

    def test_historical_def_6_2_three_info_findings_remain_an_official_clean_pass(self):
        from tests.test_phase2_review_decision import Phase2ReviewDecisionTests

        fixture = Phase2ReviewDecisionTests()
        review_input = fixture._review_input(task_id="def_6_2", task_type="Definition")
        result = fixture._raw_result(
            review_input,
            proof_class="textbook_definition_completed",
            completion_class="source_faithful_definition_bridge_completed",
        )
        result["findings"] = [
            {
                "severity": "info",
                "code": "definition_source_route_preserved",
                "message": "The canonical weighted range sum and mixed-infinity Option guard match Definition 6.2.",
            },
            {
                "severity": "info",
                "code": "live_downstream_covered",
                "message": "The exact consumer uses the exported support transparently.",
            },
            {
                "severity": "info",
                "code": "blockers_zero",
                "message": "No high- or medium-severity source, interface, or downstream blocker was found.",
            },
        ]

        self.assertEqual(len(result["findings"]), 3)
        self.assertEqual({finding["severity"] for finding in result["findings"]}, {"info"})
        normalized = validate_applied_review_clean_pass(result, review_input)

        self.assertEqual(normalized["verdict"], "pass")
        self.assertEqual(normalized["phase2_status"], "pass")

    def test_cli_requires_and_parses_all_basis_rebind_cas_values(self):
        from src.toy_apollo.cli import app as cli_app

        digest = "a" * 64
        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "basis-rebind",
                "--tasks",
                self.TASK_ID,
                "--expected-old-basis",
                digest,
                "--expected-new-basis",
                "b" * 64,
                "--expected-subject-hash",
                "c" * 64,
                "--expected-dependencies",
                "",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target:
            self.assertEqual(cli_app.main(), 0)

        args = process_target.await_args.args[0]
        self.assertEqual(args.phase2_mode, "basis-rebind")
        self.assertEqual(args.expected_old_basis, digest)
        self.assertEqual(args.expected_dependencies, [])

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "basis-rebind",
                "--tasks",
                self.TASK_ID,
            ],
        ):
            with self.assertRaises(SystemExit) as caught:
                cli_app.main()
        self.assertEqual(caught.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
