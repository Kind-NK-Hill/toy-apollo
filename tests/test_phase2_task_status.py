import unittest
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_task_status import classify_phase2_task_status
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    normalize_reviewer_result,
)


class Phase2TaskStatusClassifierTest(unittest.TestCase):
    def test_textbook_proof_completion_passes_proof_bearing_task(self):
        result = classify_phase2_task_status(
            task_id="thm_11_7",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="textbook_proof_completed",
        )

        self.assertEqual(result.task_status, "pass")
        self.assertEqual(result.proof_class, "textbook_proof_completed")
        self.assertFalse(result.needs_class_normalization)

    def test_textbook_proof_completion_passes_obligation_child_task(self):
        result = classify_phase2_task_status(
            task_id="thm_10_8__obligation_quantile_event_measurability",
            task_type="Phase2ObligationTask",
            review_verdict="pass",
            proof_class="textbook_proof_completed",
        )

        self.assertEqual(result.task_status, "pass")

    def test_definition_bridge_can_pass_definition_task(self):
        for proof_class in ("textbook_definition_completed", "source_faithful_definition_bridge_completed", "interface_bridge_completed"):
            with self.subTest(proof_class=proof_class):
                result = classify_phase2_task_status(
                    task_id="def_13_5",
                    task_type="Definition",
                    review_verdict="pass",
                    proof_class=proof_class,
                )

                self.assertEqual(result.task_status, "pass")
                self.assertFalse(result.needs_class_normalization)

    def test_mathlib_adapter_pass_review_fails_proof_bearing_task(self):
        for task_id, task_type in (("thm_14_6", "Theorem"), ("prob_14_12", "Problem")):
            with self.subTest(task_id=task_id):
                result = classify_phase2_task_status(
                    task_id=task_id,
                    task_type=task_type,
                    review_verdict="pass",
                    proof_class="mathlib_backed_adapter_completed",
                )

                self.assertEqual(result.task_status, "fail")
                self.assertIn("adapter", result.reason)

    def test_interface_bridge_does_not_pass_proof_bearing_task(self):
        result = classify_phase2_task_status(
            task_id="thm_14_6",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="interface_bridge_completed",
        )

        self.assertEqual(result.task_status, "fail")
        self.assertIn("bridge", result.reason)

    def test_missing_proof_class_uses_normalization_path(self):
        result = classify_phase2_task_status(
            task_id="thm_11_7",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="",
        )

        self.assertEqual(result.task_status, "fail")
        self.assertTrue(result.needs_class_normalization)
        self.assertIn("needs_class_normalization", result.evidence_type)

    def test_dependency_gate_blocked_is_blocked_when_no_local_open_debt(self):
        result = classify_phase2_task_status(
            task_id="prob_14_2",
            task_type="Problem",
            review_verdict="inconclusive",
            proof_class="dependency_blocked_root_debt",
        )

        self.assertEqual(result.task_status, "blocked")

    def test_allowed_exception_is_only_for_thm_14_8(self):
        result = classify_phase2_task_status(
            task_id="thm_14_8",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="beyond_book_exception",
        )

        self.assertEqual(result.task_status, "allowed_exception")
        self.assertEqual(result.as_metadata()["phase2_status"], "allowed_exception")

        ordinary = classify_phase2_task_status(
            task_id="prob_14_8",
            task_type="Problem",
            review_verdict="pass",
            proof_class="beyond_book_exception",
        )

        self.assertEqual(ordinary.task_status, "fail")

    def test_open_debt_beats_dependency_blocked(self):
        result = classify_phase2_task_status(
            task_id="ex_14_4_3",
            task_type="Exercise",
            review_verdict="fail",
            proof_class="open_math_debt_and_dependency_blocked",
        )

        self.assertEqual(result.task_status, "fail")

    def test_semantic_review_pass_without_proof_class_is_marked_for_normalization(self):
        review_input = {
            "task": {"block_id": "thm_11_7", "type": "Theorem"},
            "mode": "codex",
            "attempt": 1,
            "cache_key": "fixture",
            "reviewer_backend_id": "test",
            "candidate": {"hash": "candidate-hash"},
            "review_basis": {"required_evidence_classes": []},
        }
        raw = {
            "task_id": "thm_11_7",
            "review_input_hash": hashlib.sha256(
                json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "candidate_hash": "candidate-hash",
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "verdict": "pass",
            "confidence": "high",
            "summary": "legacy pass without proof_class",
            "reviewer_independence": {
                "role": "independent_read_only_reviewer",
                "read_only": True,
                "did_edit_candidate": False,
                "used_current_review_request": True,
                "attestation": "test reviewer read the current request",
            },
            "source_claims": [{"claim": "source proof"}],
            "claim_mapping": [{"source_claim": "source proof", "lean_declaration": "thm_11_7"}],
            "spine_alignment": {
                "status": "covered",
                "summary": "covered",
                "obligations_checked": [{"source_obligation": "source proof", "lean_landing": "thm_11_7", "status": "covered"}],
                "missing_obligations": [],
                "shortcut_assessment": "covered",
            },
            "obligation_review": {
                "status": "covered",
                "summary": "covered",
                "items": [],
                "open_blockers": [],
                "scaffold_assessment": [],
            },
            "evidence_review": {
                "status": "covered",
                "summary": "covered",
                "items": [],
                "blocking_issues": [],
            },
            "interface_contract": {"status": "covered", "summary": "covered", "mismatches": []},
            "downstream_adequacy": {"status": "covered", "summary": "covered", "consumers_checked": [], "blocking_issues": []},
            "forbidden_weakenings": [{"status": "not_present", "summary": "none"}],
            "findings": [],
            "recommended_disposition": "promote",
        }

        result = normalize_reviewer_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertEqual(result["cache_class"], "semantic_verdict")
        self.assertEqual(result["proof_class"], "")
        self.assertEqual(result["completion_class"], "")
        self.assertTrue(result["needs_class_normalization"])


if __name__ == "__main__":
    unittest.main()
