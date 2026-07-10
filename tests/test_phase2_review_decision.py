import hashlib
import json
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


from src.toy_apollo.phase2_review_decision import evaluate_semantic_review_result  # noqa: E402
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
)


class Phase2ReviewDecisionTests(unittest.TestCase):
    def _review_input(self, task_id: str = "thm_11_7", task_type: str = "Theorem") -> dict:
        return {
            "task": {"block_id": task_id, "type": task_type},
            "mode": "review-pack",
            "attempt": 1,
            "cache_key": "fixture",
            "reviewer_backend_id": "test",
            "candidate": {"hash": "candidate-hash"},
            "review_basis": {"required_evidence_classes": []},
        }

    def _raw_result(
        self,
        review_input: dict,
        *,
        proof_class: str = "source_route_proof_completed",
        completion_class: str = "source_route_proof_completed",
    ) -> dict:
        return {
            "task_id": review_input["task"]["block_id"],
            "review_input_hash": hashlib.sha256(
                json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "candidate_hash": review_input["candidate"]["hash"],
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "verdict": "pass",
            "confidence": "high",
            "summary": "fixture review",
            "proof_class": proof_class,
            "completion_class": completion_class,
            "reviewer_independence": {
                "role": "independent_read_only_reviewer",
                "read_only": True,
                "did_edit_candidate": False,
                "used_current_review_request": True,
                "attestation": "independent fixture reviewer",
            },
            "source_claims": [{"claim": "source proof"}],
            "claim_mapping": [{"source_claim": "source proof", "lean_declaration": review_input["task"]["block_id"]}],
            "route_inspection": {
                "status": "covered",
                "source_route": "source proof",
                "expected_answer_or_statement": review_input["task"]["block_id"],
                "local_mathlib_search": "checked",
                "public_interface_check": "no public-premise relocation",
                "support_or_reassembly_decision": "direct proof",
                "stop_go_verdict": "go",
            },
            "spine_alignment": {
                "status": "covered",
                "summary": "covered",
                "obligations_checked": [{"source_obligation": "source proof", "lean_landing": review_input["task"]["block_id"], "status": "covered"}],
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
            "evidence_review": {"status": "covered", "summary": "covered", "items": [], "blocking_issues": []},
            "interface_contract": {"status": "covered", "summary": "covered", "mismatches": []},
            "downstream_adequacy": {"status": "covered", "summary": "covered", "consumers_checked": [], "blocking_issues": []},
            "forbidden_weakenings": [{"status": "not_present", "summary": "none"}],
            "findings": [],
            "recommended_disposition": "promote",
        }

    def test_authoritative_projection_overwrites_reviewer_self_reported_pass(self):
        review_input = self._review_input()
        raw = self._raw_result(
            review_input,
            proof_class="mathlib_backed_adapter_completed",
            completion_class="mathlib_backed_adapter_completed",
        )
        raw.update({"phase2_status": "pass", "task_status": "pass", "task_role": "reviewer_claim"})

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertTrue(decision.is_semantic_verdict)
        self.assertFalse(decision.is_clean_pass)
        self.assertEqual(decision.task_status_projection.task_status, "fail")
        self.assertEqual(decision.result["phase2_status"], "fail")
        self.assertEqual(decision.result["task_status"], "fail")
        self.assertEqual(decision.result["task_role"], "proof_bearing")

    def test_missing_class_has_no_authoritative_projection(self):
        review_input = self._review_input()
        raw = self._raw_result(review_input)
        raw.pop("proof_class")
        raw.pop("completion_class")
        raw["phase2_status"] = "pass"

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertFalse(decision.is_semantic_verdict)
        self.assertFalse(decision.is_clean_pass)
        self.assertIsNone(decision.task_status_projection)
        self.assertNotIn("phase2_status", decision.result)

    def test_allowed_exception_is_not_counted_as_clean_pass(self):
        review_input = self._review_input("thm_14_8", "Theorem")
        raw = self._raw_result(
            review_input,
            proof_class="beyond_book_exception",
            completion_class="beyond_book_exception",
        )

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertTrue(decision.is_semantic_verdict)
        self.assertEqual(decision.task_status_projection.task_status, "allowed_exception")
        self.assertFalse(decision.is_clean_pass)


if __name__ == "__main__":
    unittest.main()
