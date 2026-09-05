import asyncio
import json
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack  # noqa: E402
from formalization_engine.phase2_semantic_fail_triage import classify_semantic_failure  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2SemanticFailTriageTests(Phase2ReviewTestSupport, unittest.TestCase):
    def _write_failed_result(
        self,
        pack_dir: Path,
        *,
        summary: str,
        proof_class: str = "open_math_debt",
        completion_class: str | None = None,
    ) -> Path:
        result_path = self._write_codex_review_result(
            pack_dir,
            verdict="fail",
            source_claims=[],
            claim_mapping=[],
            proof_class=proof_class,
            completion_class=completion_class or proof_class,
        )
        payload = json.loads(result_path.read_text(encoding="utf-8"))
        payload["summary"] = summary
        payload["findings"] = [{"severity": "error", "category": "semantic", "message": summary}]
        result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
        return result_path

    def _apply_failed_review(self, root: Path, task_id: str, *, summary: str, proof_class: str):
        ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
        build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
        self.assertTrue(build_success, build_detail)
        review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
        self.assertTrue(review_success, review_detail)
        result_path = self._write_failed_result(pack_dir, summary=summary, proof_class=proof_class)
        success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
        self.assertFalse(success)
        return detail, pack_dir, ledger

    def test_statement_source_mismatch_triggers_diagnoser_prompt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_triage_statement_mismatch"
        try:
            self._clean_root(root)
            detail, pack_dir, ledger = self._apply_failed_review(
                root,
                "thm_4_triage_statement_mismatch",
                summary="The public theorem is stronger than the textbook probability-space statement; source statement mismatch.",
                proof_class="statement_mismatch",
            )

            triage = json.loads((pack_dir / "semantic_fail_triage.json").read_text(encoding="utf-8"))
            self.assertTrue(triage["needs_diagnoser"])
            self.assertFalse(triage["local_repair_allowed"])
            self.assertEqual(triage["category"], "statement_or_source_mismatch")
            self.assertTrue(Path(triage["prompt_path"]).exists())
            self.assertIn("requires read-only diagnoser", detail)
            task_record = ledger.ledger["tasks"]["thm_4_triage_statement_mismatch"]
            self.assertTrue(task_record["latest_semantic_fail_triage_needs_diagnoser"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_open_math_debt_triggers_once_then_medium_step_does_not_retrigger(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_triage_open_debt_once"
        try:
            self._clean_root(root)
            _, pack_dir, _ = self._apply_failed_review(
                root,
                "thm_4_triage_open_debt",
                summary="The theorem still depends on a private axiom and carries open math debt.",
                proof_class="open_math_debt",
            )
            first = json.loads((pack_dir / "semantic_fail_triage.json").read_text(encoding="utf-8"))
            self.assertTrue(first["needs_diagnoser"])
            self.assertEqual(first["category"], "private_axiom_or_open_math_debt")

            medium_result = {
                "verdict": "fail",
                "summary": "The route is accepted; one medium lemma missing within an accepted route.",
                "proof_class": "partial_source_route",
                "completion_class": "partial_source_route",
            }
            category, _, base_needs = classify_semantic_failure(medium_result)
            self.assertEqual(category, "missing_step")
            self.assertFalse(base_needs)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_mathlib_adapter_source_route_mismatch_triggers_diagnoser(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_triage_adapter"
        try:
            self._clean_root(root)
            _, pack_dir, _ = self._apply_failed_review(
                root,
                "prob_4_triage_adapter",
                summary="This is a useful Mathlib adapter route but it does not start from the local source interface.",
                proof_class="source_route_mismatch_adapter",
            )

            triage = json.loads((pack_dir / "semantic_fail_triage.json").read_text(encoding="utf-8"))
            self.assertTrue(triage["needs_diagnoser"])
            self.assertEqual(triage["category"], "mathlib_adapter")
            prompt = Path(triage["prompt_path"]).read_text(encoding="utf-8")
            self.assertIn("Do not hallucinate Mathlib theorem names", prompt)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_public_premise_check_text_does_not_hide_private_axiom_debt(self):
        result = {
            "verdict": "fail",
            "summary": "The proof still depends on a private axiom and remains open_math_debt.",
            "proof_class": "open_math_debt",
            "completion_class": "open_math_debt",
            "obligation_review": {
                "items": [
                    {
                        "landing_kind": "public_premise",
                        "public_premise_check": "passed",
                        "proof_contract_status": "open_math_debt",
                    }
                ]
            },
        }

        category, _, needs = classify_semantic_failure(result)

        self.assertEqual(category, "private_axiom_or_open_math_debt")
        self.assertTrue(needs)

    def test_public_premise_relocation_still_triggers_public_premise(self):
        result = {
            "verdict": "fail",
            "summary": "The core Bernoulli law is exposed as public setup fields; this is public-premise relocation.",
            "proof_class": "open_math_debt",
            "completion_class": "open_math_debt",
        }

        category, _, needs = classify_semantic_failure(result)

        self.assertEqual(category, "public_premise")
        self.assertTrue(needs)

    def test_build_type_api_failure_does_not_trigger_diagnoser(self):
        result = {
            "verdict": "fail",
            "summary": "Lean failed with unknown identifier and type mismatch in an API call.",
            "proof_class": "build_repair_needed",
            "completion_class": "build_repair_needed",
        }

        category, _, needs = classify_semantic_failure(result)

        self.assertEqual(category, "lean_engineering")
        self.assertFalse(needs)

    def test_unclear_semantic_failure_triggers_once(self):
        result = {
            "verdict": "inconclusive",
            "summary": "Reviewer cannot determine whether the source proof spine is represented.",
            "proof_class": "",
            "completion_class": "",
        }

        category, _, needs = classify_semantic_failure(result)

        self.assertEqual(category, "unclear_semantic_failure")
        self.assertTrue(needs)


if __name__ == "__main__":
    unittest.main()
