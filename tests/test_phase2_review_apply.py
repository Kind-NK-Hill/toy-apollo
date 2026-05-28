import asyncio
import json
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack, write_existing_output_review_pack  # noqa: E402
from src.toy_apollo.phase2_review_apply import apply_codex_review_result_once  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ReviewApplyTests(Phase2ReviewTestSupport, unittest.TestCase):
    def _write_single_open_obligation(self, pack_dir: Path, task_id: str) -> None:
        (pack_dir / "proof_obligations.json").write_text(
            json.dumps(
                {
                    "schema_version": "phase2.proof_obligations.v1",
                    "task_id": task_id,
                    "classification": {
                        "requires_decomposition": True,
                        "reason": "test complex proof",
                        "evidence": ["proof has independently reviewable intermediate obligations"],
                    },
                    "obligations": [
                        {
                            "id": "source_step",
                            "title": "Source proof step",
                            "kind": "source_step",
                            "source_ref": "test source proof",
                            "depends_on": [],
                            "lean_landing": "",
                            "status": "open",
                            "review_status": "unreviewed",
                            "blocking": True,
                            "scaffold_hypotheses": [],
                            "notes": "Must be discharged before semantic pass.",
                        }
                    ],
                    "scaffold_hypotheses": [],
                    "review_history": [],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def _write_single_proof_debt_obligation(self, pack_dir: Path, task_id: str) -> None:
        (pack_dir / "proof_obligations.json").write_text(
            json.dumps(
                {
                    "schema_version": "phase2.proof_obligations.v1",
                    "task_id": task_id,
                    "classification": {
                        "requires_decomposition": True,
                        "reason": "test complex proof with accepted proof debt",
                        "evidence": ["proof carries an explicit reusable support assumption"],
                    },
                    "obligations": [
                        {
                            "id": "tail_bound_support",
                            "title": "Tail bound support",
                            "kind": "proof_debt_support",
                            "source_ref": "test source proof tail estimate",
                            "depends_on": [],
                            "lean_landing": "h_tail_bound_support",
                            "status": "accepted_as_proof_debt",
                            "review_status": "accepted",
                            "blocking": True,
                            "scaffold_hypotheses": [
                                {
                                    "name": "h_tail_bound_support",
                                    "category": "proof_debt_support",
                                    "obligation_id": "tail_bound_support",
                                    "discharge_plan": "replace support parameter by a proved local lemma",
                                    "status": "accepted_as_proof_debt",
                                }
                            ],
                            "notes": "Accepted proof debt must not be reported as a clean completion.",
                        }
                    ],
                    "scaffold_hypotheses": [],
                    "review_history": [],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def _write_two_open_obligations(self, pack_dir: Path, task_id: str) -> None:
        obligations = []
        for obligation_id in ["covered_step", "missing_step"]:
            obligations.append(
                {
                    "id": obligation_id,
                    "title": obligation_id.replace("_", " ").title(),
                    "kind": "source_step",
                    "source_ref": "test source proof",
                    "depends_on": [],
                    "lean_landing": "",
                    "status": "open",
                    "review_status": "unreviewed",
                    "blocking": True,
                    "scaffold_hypotheses": [
                        {
                            "name": f"{obligation_id}_scaffold",
                            "category": "proof_obligation",
                            "obligation_id": obligation_id,
                            "discharge_plan": "replace scaffold by reviewed Lean evidence",
                            "status": "open",
                        }
                    ]
                    if obligation_id == "covered_step"
                    else [],
                    "notes": "Must be discharged before semantic pass.",
                }
            )
        (pack_dir / "proof_obligations.json").write_text(
            json.dumps(
                {
                    "schema_version": "phase2.proof_obligations.v1",
                    "task_id": task_id,
                    "classification": {
                        "requires_decomposition": True,
                        "reason": "test complex proof",
                        "evidence": ["proof has independently reviewable intermediate obligations"],
                    },
                    "obligations": obligations,
                    "scaffold_hypotheses": [],
                    "review_history": [],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def _seed_review_failures(self, pack_dir: Path, task_id: str, count: int) -> None:
        (pack_dir / "attempt_history.json").write_text(
            json.dumps(
                {
                    "task_id": task_id,
                    "attempts": [
                        {
                            "attempt": index + 1,
                            "candidate_file": str(pack_dir / f"candidate_seed_{index + 1}.lean"),
                            "candidate_hash": f"review-fail-{index + 1}",
                            "success": False,
                            "primary_failure_kind": "semantic_review_fail",
                            "stage": "semantic_review",
                            "review_verdict": "fail",
                            "disposition": "codex_review_fail_no_promotion",
                        }
                        for index in range(count)
                    ],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def test_codex_review_apply_valid_pass_promotes_and_marks_completed(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_valid_pass"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_valid_pass"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")

            def promote_side_effect(*args, **kwargs):
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text((pack_dir / "candidate_v1.lean").read_text(encoding="utf-8"), encoding="utf-8")
                return True, "final build ok"

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
                side_effect=promote_side_effect,
            ), patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                side_effect=promote_side_effect,
            ):
                success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertTrue(success, detail)
            self.assertTrue(output_path.exists())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "COMPLETED")
            self.assertEqual(ledger.ledger["tasks"][task_id]["exported_symbols"], [task_id])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_is_idempotent_after_candidate_promoted(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_idempotent_pass"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_idempotent_pass"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")

            def promote_side_effect(*args, **kwargs):
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text((pack_dir / "candidate_v1.lean").read_text(encoding="utf-8"), encoding="utf-8")
                return True, "final build ok"

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
                side_effect=promote_side_effect,
            ), patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                side_effect=promote_side_effect,
            ):
                success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertTrue(success, detail)
            first_record = dict(ledger.ledger["tasks"][task_id])
            first_verify_files = sorted(pack_dir.glob("verify_result_v*.json"))

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertTrue(success, detail)
            self.assertIn("already promoted", detail.lower())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "COMPLETED")
            self.assertEqual(ledger.ledger["tasks"][task_id]["pack_candidate_state"], first_record["pack_candidate_state"])
            self.assertEqual(ledger.ledger["tasks"][task_id]["latest_operation_file"], first_record["latest_operation_file"])
            self.assertEqual(ledger.ledger["tasks"][task_id]["latest_verify_result_file"], first_record["latest_verify_result_file"])
            self.assertEqual(sorted(pack_dir.glob("verify_result_v*.json")), first_verify_files)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_requires_proof_obligation_coverage(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_obligation_partial_pass"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_obligation_partial_pass"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            self._write_single_open_obligation(pack_dir, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="pass",
                obligation_review={
                    "status": "partial",
                    "summary": "source_step is not discharged",
                    "items": [{"obligation_id": "source_step", "status": "partial", "evidence": "missing Lean landing"}],
                    "open_blockers": [{"obligation_id": "source_step", "issue": "missing Lean landing"}],
                    "scaffold_assessment": [],
                },
            )

            with patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("obligation", detail.lower())
            self.assertFalse(output_path.exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_with_proof_debt_marks_completed_with_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_pass_with_proof_debt"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_pass_with_proof_debt"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            self._write_single_proof_debt_obligation(pack_dir, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="pass",
                obligation_review={
                    "status": "covered",
                    "summary": "tail_bound_support is explicit accepted proof debt",
                    "items": [
                        {
                            "obligation_id": "tail_bound_support",
                            "status": "accepted_as_proof_debt",
                            "evidence": "support parameter is explicit and has a discharge plan",
                        }
                    ],
                    "open_blockers": [],
                    "scaffold_assessment": [
                        {
                            "name": "h_tail_bound_support",
                            "assessment": "accepted as explicit proof debt",
                        }
                    ],
                },
            )

            def promote_side_effect(*args, **kwargs):
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text((pack_dir / "candidate_v1.lean").read_text(encoding="utf-8"), encoding="utf-8")
                return True, "final build ok"

            with patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                side_effect=promote_side_effect,
            ):
                success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertTrue(success, detail)
            self.assertTrue(output_path.exists())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "COMPLETED_WITH_PROOF_DEBT")
            self.assertEqual(
                ledger.ledger["tasks"][task_id]["proof_obligation_summary"]["status_counts"]["accepted_as_proof_debt"],
                1,
            )
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_rejects_placeholder_decomposition(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_placeholder_decomposition"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_placeholder_decomposition"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.proof_obligations.v1",
                        "task_id": task_id,
                        "classification": {
                            "requires_decomposition": True,
                            "reason": "test complex proof",
                            "evidence": ["proof has independently reviewable intermediate obligations"],
                        },
                        "obligations": [
                            {
                                "id": "source_proof_spine",
                                "title": "Source proof spine",
                                "kind": "source_step",
                                "source_ref": "Original task text; replace this placeholder with precise source spans.",
                                "depends_on": [],
                                "lean_landing": "",
                                "status": "open",
                                "review_status": "unreviewed",
                                "blocking": True,
                                "scaffold_hypotheses": [],
                                "notes": "Complex tasks must split this placeholder into concrete proof obligations before semantic pass.",
                            }
                        ],
                        "scaffold_hypotheses": [],
                        "review_history": [],
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")

            with patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("concrete proof_obligations", detail)
            self.assertFalse(output_path.exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_carries_proof_obligation_blockers_into_repair_request(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_obligation_repair"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_obligation_repair"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._write_single_open_obligation(pack_dir, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                obligation_review={
                    "status": "violated",
                    "summary": "source_step is missing",
                    "items": [{"obligation_id": "source_step", "status": "missing", "evidence": "no Lean landing"}],
                    "open_blockers": [{"obligation_id": "source_step", "issue": "prove the source proof step"}],
                    "scaffold_assessment": [],
                },
            )

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("source_step", json.dumps(json.loads((pack_dir / "review_repair_request_v1.json").read_text(encoding="utf-8"))))
            repair_request = json.loads((pack_dir / "review_repair_request_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(repair_request["proof_obligation_blockers"][0]["obligation_id"], "source_step")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_keeps_unverified_covered_obligations_partial(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_obligation_partial_progress"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_obligation_partial_progress"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._write_two_open_obligations(pack_dir, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                obligation_review={
                    "status": "partial",
                    "summary": "covered_step has local evidence, missing_step still blocks promotion",
                    "items": [
                        {"obligation_id": "covered_step", "status": "covered", "evidence": "covered by local theorem"},
                        {"obligation_id": "missing_step", "status": "missing", "evidence": "no Lean landing"},
                    ],
                    "open_blockers": [{"obligation_id": "missing_step", "issue": "finish the remaining source step"}],
                    "scaffold_assessment": [],
                },
            )

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success, detail)
            updated = json.loads((pack_dir / "proof_obligations.json").read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in updated["obligations"]}
            self.assertEqual(by_id["covered_step"]["status"], "partial")
            self.assertEqual(by_id["covered_step"]["review_status"], "needs_review")
            self.assertEqual(by_id["covered_step"]["proof_contract_status"], "unverified")
            self.assertEqual(by_id["covered_step"]["scaffold_hypotheses"][0]["status"], "open")
            self.assertEqual(by_id["missing_step"]["status"], "blocked")
            repair_request = json.loads((pack_dir / "review_repair_request_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(repair_request["proof_obligation_summary"]["open_blocking_ids"], ["covered_step", "missing_step"])
            self.assertEqual(repair_request["proof_obligation_blockers"][0]["obligation_id"], "missing_step")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_marks_verified_contract_covered_obligations_as_proved(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_verified_obligation_progress"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_verified_obligation_progress"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._write_two_open_obligations(pack_dir, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                obligation_review={
                    "status": "partial",
                    "summary": "covered_step has verified contract, missing_step still blocks promotion",
                    "items": [
                        {
                            "obligation_id": "covered_step",
                            "status": "covered",
                            "evidence": "covered by local theorem",
                            "expected_theorem_signature": "theorem covered_step : True",
                            "lean_landing": "covered_step",
                            "landing_kind": "theorem",
                            "proof_contract_status": "verified",
                            "proof_contract_notes": "reviewed test contract",
                            "body_reassumption_check": "passed",
                            "signature_match": "passed",
                            "public_premise_check": "passed",
                        },
                        {"obligation_id": "missing_step", "status": "missing", "evidence": "no Lean landing"},
                    ],
                    "open_blockers": [{"obligation_id": "missing_step", "issue": "finish the remaining source step"}],
                    "scaffold_assessment": [],
                },
            )

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success, detail)
            updated = json.loads((pack_dir / "proof_obligations.json").read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in updated["obligations"]}
            self.assertEqual(by_id["covered_step"]["status"], "proved")
            self.assertEqual(by_id["covered_step"]["review_status"], "accepted")
            self.assertEqual(by_id["covered_step"]["proof_contract_status"], "verified")
            self.assertEqual(by_id["covered_step"]["scaffold_hypotheses"][0]["status"], "discharged")
            self.assertEqual(by_id["missing_step"]["status"], "blocked")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_rejects_basis_drift(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_basis_drift"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_basis_drift"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            self._append_direct_downstream_consumer(settings.plans_dir, task_id, "thm_4_review_apply_basis_drift_consumer")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("basis", detail.lower())
            self.assertFalse(output_path.exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_with_empty_mapping_rejects_promotion(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_empty_mapping"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_empty_mapping"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="pass", claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("claim_mapping", detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_pass_with_empty_source_claims_rejects_promotion(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_empty_source_claims"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_empty_source_claims"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="pass", source_claims=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("source_claims", detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_rejects_candidate_hash_mismatch(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_candidate_hash_mismatch"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_candidate_hash_mismatch"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            review_input["candidate"]["hash"] = "mismatch"
            (pack_dir / "semantic_review_input_v1.json").write_text(json.dumps(review_input, indent=2, ensure_ascii=False), encoding="utf-8")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("candidate hash", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_validation_failure_preserves_result_file(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_preserve_invalid_result"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_preserve_invalid_result"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="pass", candidate_hash="mismatch")
            original_result_text = result_path.read_text(encoding="utf-8")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("candidate hash", detail.lower())
            self.assertEqual(result_path.read_text(encoding="utf-8"), original_result_text)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_inconclusive_auto_continues_review_fix(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_inconclusive_continue"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_inconclusive_continue"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)

            result_path = self._write_codex_review_result(pack_dir, verdict="inconclusive")
            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("repair loop continued automatically", detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertTrue(str(task_record["current_review_repair_request_file"]).endswith("review_repair_request_v1.json"))
            self.assertTrue(str(task_record["current_review_repair_seed_file"]).endswith("candidate_v1.lean"))
            self.assertEqual((pack_dir / "draft.lean").read_text(encoding="utf-8"), (pack_dir / "candidate_v1.lean").read_text(encoding="utf-8"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_existing_review_apply_pass_clears_stale_auto_loop_state(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_existing_review_apply_pass_clears_auto_loop"
        try:
            self._clean_root(root)
            task_id = "thm_4_existing_review_apply_pass_clears_auto_loop"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)
            with patch("src.toy_apollo.phase2_prompt_pack._run_official_module_build", return_value=(True, "sanity ok")):
                review_success, review_detail = asyncio.run(
                    write_existing_output_review_pack(task_id, ledger, settings, force_new_attempt=True)
                )
            self.assertTrue(review_success, review_detail)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="existing",
                current_auto_loop_round=2,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=1,
                current_auto_loop_phase="applying",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="stale",
                current_auto_loop_last_review_fingerprint="stale",
                current_auto_loop_last_repair_request_file="stale.json",
            )

            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertTrue(success, detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertFalse(task_record.get("current_auto_loop_enabled"))
            self.assertEqual(task_record.get("current_auto_loop_status"), "")
            self.assertEqual(task_record.get("current_auto_loop_phase"), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_strict_schema_gate_preserves_active_auto_loop_state(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_auto_loop_strict_schema_gate"
        try:
            self._clean_root(root)
            task_id = "thm_4_auto_loop_strict_schema_gate"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)

            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="existing",
                current_auto_loop_round=1,
                current_auto_loop_max_rounds=2,
                current_auto_loop_max_build_attempts_per_round=1,
                current_auto_loop_nonprogress_limit=1,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="reviewing",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
            )

            review_request = json.loads((pack_dir / "semantic_review_request_v1.json").read_text(encoding="utf-8"))
            result_path = Path(str(review_request["expected_result_file"]))
            template_path = Path(str(review_request["review_result_template_file"]))
            stale_result = json.loads(template_path.read_text(encoding="utf-8"))
            stale_result.pop("spine_alignment", None)
            result_path.write_text(json.dumps(stale_result, indent=2, ensure_ascii=False), encoding="utf-8")

            outcome = asyncio.run(apply_codex_review_result_once(task_id, ledger, settings, str(result_path)))

            self.assertFalse(outcome.success)
            self.assertIn("spine_alignment", outcome.detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record["current_review_subject_kind"], "official_output")
            self.assertEqual(task_record["current_auto_loop_status"], "active")
            self.assertEqual(task_record["current_auto_loop_phase"], "reviewing")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_invalid_result_does_not_leave_active_auto_loop_state(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_invalid_clears_auto_loop"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_invalid_clears_auto_loop"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=1,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="applying",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="candidate-hash",
                current_auto_loop_last_review_fingerprint="review-fingerprint",
                current_auto_loop_last_repair_request_file="repair.json",
            )
            invalid_result = pack_dir / "semantic_review_result_invalid.json"
            invalid_result.write_text("{not-json", encoding="utf-8")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(invalid_result)))

            self.assertFalse(success)
            self.assertTrue(
                "prompt_version" in detail or "review_input_file" in detail or "review result is not a json object" in detail.lower(),
                detail,
            )
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record.get("current_auto_loop_status"), "")
            self.assertEqual(task_record.get("current_auto_loop_phase"), "")
            self.assertEqual(task_record.get("current_auto_loop_stop_reason"), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_invalid_semantic_output_does_not_auto_continue_review_fix(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_invalid_semantic_output"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_invalid_semantic_output"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._append_direct_downstream_consumer(settings.plans_dir, task_id, "thm_4_review_apply_invalid_semantic_output_consumer")
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["downstream_adequacy"]["consumers_checked"] = []
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertNotIn("repair loop continued automatically", detail.lower())
            self.assertIn("downstream", detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(str(task_record.get("current_review_repair_request_file", "") or ""), "")
            self.assertEqual(str(task_record.get("current_review_repair_seed_file", "") or ""), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_generates_repair_request_and_summary(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_fail_generates_repair"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_fail_generates_repair"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("repair loop continued automatically", detail.lower())
            self.assertTrue((pack_dir / "review_repair_request_v1.json").exists())
            self.assertTrue((pack_dir / "review_repair_summary_v1.md").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_updates_runtime_history_for_repair_loop(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_fail_history"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_fail_history"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            history = json.loads((pack_dir / "attempt_history.json").read_text(encoding="utf-8"))
            latest = history["attempts"][-1]
            self.assertEqual(latest["stage"], "semantic_review")
            self.assertEqual(latest["review_verdict"], "fail")
            self.assertTrue(str(latest["repair_request_file"]).endswith("review_repair_request_v1.json"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_does_not_demote_existing_completed_output(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_existing_fail_no_demote"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_existing_fail_no_demote"
            bad_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=bad_candidate,
                completed=True,
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "COMPLETED")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fail_does_not_promote_uncompleted_task(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_fail_no_promotion"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_fail_no_promotion"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("fail", detail.lower())
            self.assertFalse(output_path.exists())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "PACKED")
            self.assertEqual(ledger.ledger["tasks"][task_id]["pack_candidate_state"], "review_rejected")
            self.assertEqual(ledger.ledger["tasks"][task_id]["phase2_review_fail_counter"], 1)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_fails_only_after_15_review_failures(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_fails_after_15_review_failures"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_fails_after_15_review_failures"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            self._seed_review_failures(pack_dir, task_id, 14)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("fail", detail.lower())
            self.assertFalse(output_path.exists())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "FAILED_LOCAL")
            self.assertEqual(ledger.ledger["tasks"][task_id]["phase2_review_fail_counter"], 15)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_apply_inconclusive_does_not_promote_uncompleted_task(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_inconclusive_no_promotion"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_inconclusive_no_promotion"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="inconclusive")

            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("inconclusive", detail.lower())
            self.assertFalse(output_path.exists())
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "PACKED")
            self.assertEqual(ledger.ledger["tasks"][task_id]["pack_candidate_state"], "review_rejected")
            self.assertEqual(ledger.ledger["tasks"][task_id]["phase2_review_fail_counter"], 1)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_apply_invalid_does_not_overwrite_existing_semantic_fail_result(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_apply_preserves_failed_result"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_apply_preserves_failed_result"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
            original_text = result_path.read_text(encoding="utf-8")

            ledger.update_runtime_metadata(task_id, latest_build_ready_candidate_hash="stale-hash")
            success, detail = asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            self.assertFalse(success)
            self.assertIn("candidate hash changed", detail.lower())
            self.assertEqual(result_path.read_text(encoding="utf-8"), original_text)
            persisted = json.loads(result_path.read_text(encoding="utf-8"))
            self.assertEqual(persisted["verdict"], "fail")
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
