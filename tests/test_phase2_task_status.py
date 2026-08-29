import unittest
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_task_status import (
    DEFINITION_INTERFACE_PASS_PREFIXES,
    PROOF_BEARING_PASS_PREFIXES,
    REMARK_PASS_PREFIXES,
    classify_phase2_task_status,
    phase2_pass_class_contract,
)
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    normalize_reviewer_result,
)


class Phase2TaskStatusClassifierTest(unittest.TestCase):
    def test_reviewer_pass_class_contract_follows_task_role_and_explicit_exceptions(self):
        theorem = phase2_pass_class_contract("thm_7_8", "Theorem_with_Proof")
        definition = phase2_pass_class_contract("def_6_3", "Definition")
        remark = phase2_pass_class_contract("rem_5_1", "Remark")
        exception = phase2_pass_class_contract("thm_11_8", "Theorem")
        lemma = phase2_pass_class_contract("lem_18", "Lemma")
        corollary = phase2_pass_class_contract("cor_21", "Corollary")

        self.assertEqual(theorem["task_role"], "proof_bearing")
        self.assertEqual(theorem["clean_pass_prefixes"], list(PROOF_BEARING_PASS_PREFIXES))
        self.assertEqual(definition["task_role"], "definition_interface")
        self.assertEqual(definition["clean_pass_prefixes"], list(DEFINITION_INTERFACE_PASS_PREFIXES))
        self.assertEqual(remark["task_role"], "remark")
        self.assertEqual(remark["clean_pass_prefixes"], list(REMARK_PASS_PREFIXES))
        self.assertEqual(lemma["task_role"], "proof_bearing")
        self.assertEqual(corollary["task_role"], "proof_bearing")
        self.assertEqual(exception["allowed_exception_classes"], ["cited_external_proof_exception"])

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

    def test_source_route_theorem_passes_proof_bearing_task(self):
        result = classify_phase2_task_status(
            task_id="obl_obl_prob_14_12_obligation_5_obligation_5",
            task_type="Phase2ObligationTask",
            review_verdict="pass",
            proof_class="source_route_theorem",
        )

        self.assertEqual(result.task_status, "pass")
        self.assertIn("source-route completion", result.reason)

    def test_source_route_theorem_slash_lemma_class_normalizes_to_pass(self):
        result = classify_phase2_task_status(
            task_id="obl_obl_thm_7_9_t7_9_improper_filter_bookkeeping_recover_value",
            task_type="Phase2ObligationTask",
            review_verdict="pass",
            proof_class="source_route_theorem/lemma",
        )

        self.assertEqual(result.task_status, "pass")
        self.assertEqual(result.proof_class, "source_route_theorem_lemma")

    def test_textbook_source_route_completion_passes_problem(self):
        result = classify_phase2_task_status(
            task_id="prob_14_12",
            task_type="Problem",
            review_verdict="pass",
            proof_class="textbook_source_route_completed",
        )

        self.assertEqual(result.task_status, "pass")
        self.assertIn("source-route completion", result.reason)

    def test_focused_support_predicate_passes_only_obligation_child_task(self):
        child = classify_phase2_task_status(
            task_id="obl_ex_14_4_1_record_bernoulli_source_law",
            task_type="Phase2ObligationTask",
            review_verdict="pass",
            proof_class="source_route_support_predicate_completed",
            completion_class="focused_child_obligation_completed",
        )

        self.assertEqual(child.task_status, "pass")
        self.assertIn("focused completion", child.reason)

        parent = classify_phase2_task_status(
            task_id="ex_14_4_1",
            task_type="Exercise",
            review_verdict="pass",
            proof_class="source_route_support_predicate_completed",
            completion_class="focused_child_obligation_completed",
        )

        self.assertEqual(parent.task_status, "fail")
        self.assertIn("not a task-level pass", parent.reason)

    def test_focused_source_route_theorem_passes_only_obligation_child_task(self):
        child = classify_phase2_task_status(
            task_id="obl_obl_prob_14_12_obligation_5_obligation_5_bounded_truncations",
            task_type="Phase2ObligationTask",
            review_verdict="pass",
            proof_class="focused_child_source_route_theorem",
            completion_class="focused_obligation_closed",
        )

        self.assertEqual(child.task_status, "pass")
        self.assertIn("focused completion", child.reason)

        parent = classify_phase2_task_status(
            task_id="prob_14_12",
            task_type="Problem",
            review_verdict="pass",
            proof_class="focused_child_source_route_theorem",
            completion_class="focused_obligation_closed",
        )

        self.assertEqual(parent.task_status, "fail")
        self.assertIn("not a task-level pass", parent.reason)

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

    def test_textual_remark_completion_passes_remark_task(self):
        for proof_class in (
            "textbook_remark_completed",
            "source_faithful_non_theorem_artifact",
            "non_proof_textual_remark_carrier",
        ):
            with self.subTest(proof_class=proof_class):
                result = classify_phase2_task_status(
                    task_id="rem_9_2_computing_moments",
                    task_type="Remark",
                    review_verdict="pass",
                    proof_class=proof_class,
                )

                self.assertEqual(result.task_status, "pass")
                self.assertEqual(result.task_role, "remark")
                self.assertFalse(result.needs_class_normalization)

    def test_intro_prefix_can_pass_as_textual_remark_task(self):
        result = classify_phase2_task_status(
            task_id="intro_9_2",
            task_type="",
            review_verdict="pass",
            proof_class="source_faithful_textual_remark_completed",
        )

        self.assertEqual(result.task_status, "pass")
        self.assertEqual(result.task_role, "remark")

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

    def test_allowed_exception_is_only_for_explicit_tasks_and_classes(self):
        thm_14_8 = classify_phase2_task_status(
            task_id="thm_14_8",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="beyond_book_exception",
        )

        self.assertEqual(thm_14_8.task_status, "allowed_exception")
        self.assertEqual(thm_14_8.as_metadata()["phase2_status"], "allowed_exception")

        thm_11_8 = classify_phase2_task_status(
            task_id="thm_11_8",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="cited_external_proof_exception",
        )

        self.assertEqual(thm_11_8.task_status, "allowed_exception")

        thm_1_2 = classify_phase2_task_status(
            task_id="thm_1_2",
            task_type="Theorem_Statement",
            review_verdict="pass",
            proof_class="source_statement_exception",
        )

        self.assertEqual(thm_1_2.task_status, "allowed_exception")

        ex_1_3_2 = classify_phase2_task_status(
            task_id="ex_1_3_2",
            task_type="Example_Proof",
            review_verdict="pass",
            proof_class="source_typo_statement_exception",
        )

        self.assertEqual(ex_1_3_2.task_status, "allowed_exception")

        ordinary = classify_phase2_task_status(
            task_id="prob_14_8",
            task_type="Problem",
            review_verdict="pass",
            proof_class="beyond_book_exception",
        )

        self.assertEqual(ordinary.task_status, "fail")

        wrong_class = classify_phase2_task_status(
            task_id="thm_11_8",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="beyond_book_exception",
        )

        self.assertEqual(wrong_class.task_status, "fail")

        ordinary_source_exception = classify_phase2_task_status(
            task_id="ex_1_2_1",
            task_type="Example_Proof",
            review_verdict="pass",
            proof_class="source_typo_statement_exception",
        )

        self.assertEqual(ordinary_source_exception.task_status, "fail")

    def test_open_debt_beats_dependency_blocked(self):
        result = classify_phase2_task_status(
            task_id="ex_14_4_3",
            task_type="Exercise",
            review_verdict="fail",
            proof_class="open_math_debt_and_dependency_blocked",
        )

        self.assertEqual(result.task_status, "fail")

    def test_completion_class_local_debt_overrides_clean_proof_class(self):
        result = classify_phase2_task_status(
            task_id="thm_11_7",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="source_route_proof_completed",
            completion_class="open_math_debt",
        )

        self.assertEqual(result.task_status, "fail")
        self.assertEqual(result.evidence_type, "local_open_debt")

    def test_completion_class_dependency_block_overrides_clean_proof_class(self):
        result = classify_phase2_task_status(
            task_id="thm_11_7",
            task_type="Theorem",
            review_verdict="pass",
            proof_class="source_route_proof_completed",
            completion_class="dependency_blocked_root_debt",
        )

        self.assertEqual(result.task_status, "blocked")
        self.assertEqual(result.evidence_type, "blocked_by_dependency_gate")

    def test_any_documented_local_defect_marker_overrides_clean_completion_prefix(self):
        for defect_class in ("private_axiom", "proof_debt", "source_mismatch"):
            with self.subTest(defect_class=defect_class):
                result = classify_phase2_task_status(
                    task_id="thm_11_7",
                    task_type="Theorem",
                    review_verdict="pass",
                    proof_class="source_route_proof_completed",
                    completion_class=defect_class,
                )
                suffixed = classify_phase2_task_status(
                    task_id="thm_11_7",
                    task_type="Theorem",
                    review_verdict="pass",
                    proof_class=f"source_route_proof_completed_{defect_class}",
                    completion_class=f"source_route_proof_completed_{defect_class}",
                )

                self.assertEqual(result.task_status, "fail")
                self.assertEqual(result.evidence_type, "local_open_debt")
                self.assertEqual(suffixed.task_status, "fail")
                self.assertEqual(suffixed.evidence_type, "local_open_debt")

    def test_incompatible_completion_class_cannot_hide_behind_clean_proof_class(self):
        incompatible = (
            "beyond_book_exception",
            "interface_bridge_completed",
            "source_statement_exception",
            "definition_only_completed",
            "focused_child_obligation_completed",
        )
        for completion_class in incompatible:
            with self.subTest(completion_class=completion_class):
                result = classify_phase2_task_status(
                    task_id="thm_11_7",
                    task_type="Theorem",
                    review_verdict="pass",
                    proof_class="source_route_proof_completed",
                    completion_class=completion_class,
                )

                self.assertEqual(result.task_status, "fail")
                expected_evidence = (
                    "bridge_not_task_pass"
                    if completion_class == "interface_bridge_completed"
                    else "class_not_task_pass"
                )
                self.assertEqual(result.evidence_type, expected_evidence)

    def test_semantic_review_pass_without_completion_classes_is_operationally_invalid(self):
        task_payload = {
            "block_id": "thm_11_7",
            "type": "Theorem",
            "title": "Fixture theorem",
            "content": "A fixture source theorem.",
            "source_plan": "fixture_plan",
            "dependencies": [],
            "soft_imports": [],
            "soft_imports_confirmed_at": "",
        }
        candidate_lean = "import Mathlib\n\ntheorem thm_11_7 : True := by trivial\n"
        candidate_hash = hashlib.sha256(candidate_lean.encode("utf-8")).hexdigest()
        review_basis = {"task": dict(task_payload), "required_evidence_classes": []}
        context_markdown = "# Fixture review context\n"
        review_input = {
            "schema_version": "phase2.semantic_review.input.v3",
            "task": task_payload,
            "mode": "codex",
            "attempt": 1,
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "cache_key": "fixture",
            "reviewer_backend_id": "test",
            "review_subject_kind": "candidate",
            "review_subject_file": "candidate.lean",
            "review_subject_hash": candidate_hash,
            "candidate": {"file": "candidate.lean", "hash": candidate_hash, "lean": candidate_lean},
            "review_context_hash": hashlib.sha256(context_markdown.encode("utf-8")).hexdigest(),
            "review_context_markdown": context_markdown,
            "review_basis": review_basis,
            "review_basis_hash": hashlib.sha256(
                json.dumps(review_basis, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
        }
        raw = {
            "task_id": "thm_11_7",
            "review_input_hash": hashlib.sha256(
                json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "candidate_hash": candidate_hash,
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
            "route_inspection": {
                "status": "covered",
                "source_route": "source proof",
                "expected_answer_or_statement": "thm_11_7",
                "local_mathlib_search": "not needed",
                "public_interface_check": "covered",
                "support_or_reassembly_decision": "candidate is direct parent theorem",
                "stop_go_verdict": "go",
                "notes": "covered",
            },
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

        self.assertEqual(result["cache_class"], "operational_failure")
        self.assertEqual(result["verdict"], "inconclusive")
        self.assertIn("completion_class", result["normalization_reason"])
        self.assertIn("proof_class", result["normalization_reason"])
        self.assertEqual(result["proof_class"], "")
        self.assertEqual(result["completion_class"], "")
        self.assertFalse(result["needs_class_normalization"])


if __name__ == "__main__":
    unittest.main()
