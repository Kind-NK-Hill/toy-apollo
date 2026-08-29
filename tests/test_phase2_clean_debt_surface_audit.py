import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.audit_phase2_clean_debt_surface import (  # noqa: E402
    apply_status_fixes,
    findings_payload,
    scan_obligations,
    scan_public_surface,
)


class Phase2CleanDebtSurfaceAuditTests(unittest.TestCase):
    def test_support_parameter_is_error_but_proof_beyond_book_is_allowed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "thm_10_8.lean").write_text(
                """
structure SomeSupport where
  ok : True

theorem thm_10_8 (h : SomeSupport) : True := by
  exact True.intro
""",
                encoding="utf-8",
            )
            (output / "thm_14_8.lean").write_text(
                """
structure thm_14_8_ProofBeyondBook where
  ok : True

theorem thm_14_8 (H : thm_14_8_ProofBeyondBook) : True := by
  exact True.intro
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["severity_counts"]["allowed"], 1)
            self.assertEqual(payload["findings"][0]["category"], "public_proof_package_parameter")

    def test_support_return_is_review_but_implicit_support_parameter_is_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "thm_10_9.lean").write_text(
                """
structure SomeSupport where
  ok : True

theorem prove_some_support : SomeSupport := by
  exact ⟨True.intro⟩

theorem thm_10_9 {h : SomeSupport} : True := by
  exact h.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["severity_counts"]["review"], 1)
            categories = [finding["category"] for finding in payload["findings"]]
            self.assertEqual(
                categories,
                [
                    "public_proof_package_return_review",
                    "public_proof_package_parameter",
                ],
            )

    def test_prob63support_namespace_is_not_a_proof_package_parameter(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "ex_14_4_3.lean").write_text(
                """
theorem ex_14_4_3_geometric_mgf_hasSum :
    (fun m : Nat => Prob63Support.scalarStageWait m) = id := by
  rfl
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertNotIn("error", payload["severity_counts"])
            self.assertEqual([], payload["findings"])

    def test_support_proof_from_support_parameter_is_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "prob_11_6.lean").write_text(
                """
structure SixthMomentSupport where
  ok : True

structure TailSummabilitySupport where
  ok : True

theorem tail_from_sixth (h : SixthMomentSupport) : TailSummabilitySupport := by
  exact ⟨h.ok⟩
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["review"], 1)
            self.assertNotIn("error", payload["severity_counts"])
            self.assertEqual(
                payload["findings"][0]["category"],
                "public_proof_package_parameter_in_support_proof_review",
            )

    def test_bridge_parameter_is_interface_review_not_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "thm_14_6.lean").write_text(
                """
structure SomeMathlibBridge where
  ok : True

theorem thm_14_6 (B : SomeMathlibBridge) : True := by
  exact B.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertNotIn("error", payload["severity_counts"])
            self.assertEqual(payload["severity_counts"]["review"], 1)
            self.assertEqual(
                payload["findings"][0]["category"],
                "public_interface_bridge_parameter_review",
            )
            self.assertIn("interface translation", payload["findings"][0]["action"])

    def test_non_thm_14_8_beyond_book_obligation_is_not_allowed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            packs = root / "phase2_prompt_packs" / "prob_14_11"
            output.mkdir(parents=True)
            packs.mkdir(parents=True)
            (output / "prob_14_11.lean").write_text(
                """
structure prob_14_11_ProofBeyondBook where
  ok : True
""",
                encoding="utf-8",
            )
            (packs / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "prob_14_11",
                        "obligations": [
                            {
                                "id": "beyond_book_proof_obligations",
                                "kind": "proof_debt_support",
                                "status": "accepted_as_proof_debt",
                                "review_status": "accepted",
                                "lean_landing": "prob_14_11_ProofBeyondBook",
                            }
                        ],
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertNotIn("allowed", payload["severity_counts"])
            self.assertEqual(payload["findings"][0]["category"], "non_exception_accepted_debt")

    def test_thm_14_8_beyond_book_parameter_is_allowed_for_direct_downstream(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "prob_14_11.lean").write_text(
                """
structure thm_14_8_ProofBeyondBook where
  ok : True

theorem prob_14_11 (H : thm_14_8_ProofBeyondBook) : True := by
  exact H.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertNotIn("error", payload["severity_counts"])
            self.assertEqual(payload["severity_counts"]["allowed"], 1)
            self.assertEqual(payload["findings"][0]["category"], "inherited_beyond_book_surface")

    def test_verification_parameter_is_treated_as_public_proof_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "ex_14_4_3.lean").write_text(
                """
structure LocalLyapunovVerification where
  ok : True

theorem ex_14_4_3 (V : LocalLyapunovVerification) : True := by
  exact V.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["findings"][0]["category"], "public_proof_package_parameter")

    def test_interface_parameter_is_treated_as_public_proof_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "thm_10_8.lean").write_text(
                """
structure QuantileInterface where
  ok : True

theorem thm_10_8 (I : QuantileInterface) : True := by
  exact I.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["findings"][0]["detail"], "QuantileInterface")
            self.assertEqual(payload["findings"][0]["category"], "public_proof_package_parameter")

    def test_setup_parameter_is_reviewed_without_becoming_proof_package_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "prob_14_1.lean").write_text(
                """
structure prob_14_1_PolyaUrnBetaSetup where
  ok : True

theorem prob_14_1 (S : prob_14_1_PolyaUrnBetaSetup) : True := by
  exact S.ok
""",
                encoding="utf-8",
            )

            payload = findings_payload(scan_public_surface(root, 10, 14))

            self.assertNotIn("error", payload["severity_counts"])
            self.assertEqual(payload["severity_counts"]["review"], 1)
            self.assertEqual(payload["findings"][0]["category"], "public_setup_parameter_review")

    def test_mirror_scan_is_opt_in(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            mirror = root / "output_lean_files" / "general"
            output.mkdir(parents=True)
            mirror.mkdir(parents=True)
            (root / "phase2_prompt_packs").mkdir()
            (output / "thm_10_8.lean").write_text(
                """
theorem thm_10_8 : True := by
  exact True.intro
""",
                encoding="utf-8",
            )
            (mirror / "thm_10_8.lean").write_text(
                """
structure QuantileSupport where
  ok : True

theorem thm_10_8 (h : QuantileSupport) : True := by
  exact h.ok
""",
                encoding="utf-8",
            )

            official_payload = findings_payload(scan_public_surface(root, 10, 14))
            mirror_payload = findings_payload(scan_public_surface(root, 10, 14, include_mirrors=True))

            self.assertNotIn("error", official_payload["severity_counts"])
            self.assertEqual(mirror_payload["severity_counts"]["error"], 1)
            self.assertEqual(
                mirror_payload["findings"][0]["file"],
                "output_lean_files/general/thm_10_8.lean",
            )

    def test_proved_proof_debt_landing_on_structure_field_is_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            pack = root / "phase2_prompt_packs" / "thm_14_5"
            output.mkdir(parents=True)
            pack.mkdir(parents=True)
            (output / "thm_14_5.lean").write_text(
                """
structure thm_14_5_SourceProofSpine where
  fubini_identity : True
""",
                encoding="utf-8",
            )
            (pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "thm_14_5",
                        "obligations": [
                            {
                                "id": "fubini_identity",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "lean_landing": "thm_14_5_SourceProofSpine.fubini_identity",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["findings"][0]["category"], "proved_proof_debt_lands_on_structure_field")

    def test_proved_proof_debt_landing_on_projection_wrapper_is_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            pack = root / "phase2_prompt_packs" / "prob_14_8"
            output.mkdir(parents=True)
            pack.mkdir(parents=True)
            (output / "prob_14_8.lean").write_text(
                """
structure prob_14_8_MgfConvergenceSetup where
  mgf_to_characteristic_convergence : True

theorem prob_14_8_characteristic_convergence
    (S : prob_14_8_MgfConvergenceSetup) : True :=
  S.mgf_to_characteristic_convergence
""",
                encoding="utf-8",
            )
            (pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "prob_14_8",
                        "obligations": [
                            {
                                "id": "obligation_4",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "lean_landing": "prob_14_8_characteristic_convergence",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(
                payload["findings"][0]["category"],
                "proved_proof_debt_lands_on_projection_wrapper",
            )

    def test_proved_source_obligation_landing_on_setup_field_is_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            pack = root / "phase2_prompt_packs" / "prob_14_2"
            output.mkdir(parents=True)
            pack.mkdir(parents=True)
            (output / "prob_14_2.lean").write_text(
                """
structure prob_14_2_GammaCLTSetup where
  cltSetup : True
""",
                encoding="utf-8",
            )
            (pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "prob_14_2",
                        "obligations": [
                            {
                                "id": "apply_lindeberg_levy_clt",
                                "kind": "source_step",
                                "status": "proved",
                                "lean_landing": "prob_14_2_GammaCLTSetup.cltSetup",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["findings"][0]["category"], "proved_obligation_lands_on_structure_field")

    def test_verified_source_setup_field_landing_is_not_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            pack = root / "phase2_prompt_packs" / "prob_14_11"
            output.mkdir(parents=True)
            pack.mkdir(parents=True)
            (output / "prob_14_11.lean").write_text(
                """
structure prob_14_11_CouponRatioTriangularArraySetup where
  ratio_tendsto : True
""",
                encoding="utf-8",
            )
            (pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "prob_14_11",
                        "obligations": [
                            {
                                "id": "ratio",
                                "kind": "source_step",
                                "status": "proved",
                                "lean_landing": (
                                    "prob_14_11_CouponRatioTriangularArraySetup."
                                    "ratio_tendsto"
                                ),
                                "proof_contract_status": "verified",
                                "signature_match": "passed",
                                "body_reassumption_check": "passed",
                                "public_premise_check": "passed",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))

            self.assertNotIn("error", payload["severity_counts"])

    def test_child_obligation_pack_is_in_scope_through_parent_task(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            pack = root / "phase2_prompt_packs" / "obl_prob_14_8_obligation_4"
            output.mkdir(parents=True)
            pack.mkdir(parents=True)
            (root / "docs").mkdir()
            (output / "prob_14_8.lean").write_text(
                """
structure prob_14_8_MgfConvergenceSetup where
  mgf_to_characteristic_convergence : True
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "obl_prob_14_8_obligation_4": {
                                "block_id": "obl_prob_14_8_obligation_4",
                                "type": "Phase2ObligationTask",
                                "status": "COMPLETED",
                                "proof_obligation_summary": {
                                    "open_blocking_ids": [],
                                    "status_counts": {"proved": 1},
                                },
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "task_id": "obl_prob_14_8_obligation_4",
                        "classification": {
                            "evidence": ["parent_task_id=prob_14_8"],
                        },
                        "obligations": [
                            {
                                "id": "obligation_4",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "review_status": "accepted",
                                "lean_landing": "prob_14_8_MgfConvergenceSetup.mgf_to_characteristic_convergence",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = findings_payload(scan_obligations(root, 10, 14))
            manifest = apply_status_fixes(root, 10, 14)

            self.assertEqual(payload["severity_counts"]["error"], 1)
            self.assertEqual(payload["findings"][0]["task_id"], "obl_prob_14_8_obligation_4")
            self.assertEqual(manifest["changed_task_count"], 1)
            updated_pack = json.loads((pack / "proof_obligations.json").read_text(encoding="utf-8"))
            self.assertEqual(updated_pack["obligations"][0]["status"], "open")
            ledger = json.loads((root / "project_ledger.json").read_text(encoding="utf-8"))
            self.assertEqual(
                ledger["tasks"]["obl_prob_14_8_obligation_4"]["status"],
                "FAILED_LOCAL",
            )


if __name__ == "__main__":
    unittest.main()
