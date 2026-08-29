import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.audit_phase2_unfinished_tasks import (  # noqa: E402
    apply_metadata_drift_fixes,
    build_inventory,
    has_blocking_unfinished,
    markdown_report,
    sync_ledger_proof_obligation_summaries,
)


class Phase2UnfinishedTasksAuditTests(unittest.TestCase):
    def test_inventory_merges_ledger_obligations_surface_and_critical_bridge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ToyApollo" / "Output").mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "prob_11_4").mkdir(parents=True)
            (root / "phase2_prompt_packs" / "prob_11_6").mkdir(parents=True)

            for task_id in [
                "thm_6_7__lemma_1",
                "thm_10_8",
                "prob_11_4",
                "prob_11_5",
                "prob_11_6",
                "prob_11_1",
                "thm_13_13",
                "thm_9_5_kernel",
            ]:
                (root / "ToyApollo" / "Output" / f"{task_id}.lean").write_text(
                    "theorem dummy : True := by exact True.intro\n",
                    encoding="utf-8",
                )
            (root / "ToyApollo" / "Output" / "prob_11_6.lean").write_text(
                """
import ToyApollo.Output.thm_9_5_kernel

structure TailSupport where
  field : True

theorem dummy : True := by exact True.intro
""",
                encoding="utf-8",
            )

            ledger = {
                "tasks": {
                    "thm_6_7__lemma_1": {
                        "block_id": "thm_6_7__lemma_1",
                        "type": "Theorem",
                        "status": "COMPLETED",
                    },
                    "thm_10_8": {
                        "block_id": "thm_10_8",
                        "type": "Theorem",
                        "status": "COMPLETED",
                        "proof_obligation_summary": {
                            "open_blocking_ids": ["quantile_bridge"],
                        },
                    },
                    "prob_11_5": {
                        "block_id": "prob_11_5",
                        "type": "Problem",
                        "status": "FAILED_LOCAL",
                        "proof_obligation_summary": {
                            "open_blocking_ids": [],
                        },
                    },
                    "prob_11_4": {
                        "block_id": "prob_11_4",
                        "type": "Problem",
                        "status": "COMPLETED",
                        "proof_obligation_summary": {
                            "open_blocking_ids": ["density_mean_interface"],
                        },
                    },
                    "prob_11_6": {
                        "block_id": "prob_11_6",
                        "type": "Problem",
                        "status": "FAILED_LOCAL",
                        "proof_obligation_summary": {
                            "open_blocking_ids": ["tail_support"],
                        },
                    },
                    "thm_13_13": {
                        "block_id": "thm_13_13",
                        "type": "Theorem",
                        "status": "COMPLETED",
                    },
                    "prob_11_1": {
                        "block_id": "prob_11_1",
                        "type": "Problem",
                        "status": "COMPLETED",
                    },
                    "obl_prob_11_6_tail_support": {
                        "block_id": "obl_prob_11_6_tail_support",
                        "parent_task_id": "prob_11_6",
                        "type": "ProofObligation",
                        "status": "COMPLETED",
                        "output_hash": "pack-build-cache-hash",
                        "exported_symbols": ["PackBuildCheck_obl_prob_11_6_tail_support"],
                    },
                },
                "symbols": {},
            }
            (root / "project_ledger.json").write_text(
                json.dumps(ledger),
                encoding="utf-8",
            )
            (root / ".lake" / "build" / "lib" / "lean" / "ToyApollo" / "Output").mkdir(
                parents=True
            )
            (
                root
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "ToyApollo"
                / "Output"
                / "PackBuildCheck_obl_prob_11_6_tail_support.olean"
            ).write_text("cache", encoding="utf-8")
            (root / "docs" / "phase2_ch10_14_clean_debt_surface_audit.json").write_text(
                json.dumps({"error_tasks": {"thm_13_13": {}, "prob_11_6": {}}}),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_11_6" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "tail_support",
                                "name": "tail_interface",
                                "kind": "proof_debt_support",
                                "status": "open",
                                "review_status": "needs_review",
                                "lean_landing": "TailSupport.field",
                                "ledger_task_id": "obl_prob_11_6_tail_support",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            (root / "ToyApollo" / "Output" / "prob_11_4.lean").write_text(
                "theorem prob_11_4_mean_of_density : True := by exact True.intro\n",
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_11_4" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "density_mean_interface",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "review_status": "accepted",
                                "lean_landing": "prob_11_4_mean_of_density",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=["thm_6_7__lemma_1"],
                check_build=False,
            )

            by_id = {item["task_id"]: item for item in payload["items"]}
            self.assertEqual(payload["summary"]["unfinished_or_verify_count"], 5)
            self.assertEqual(payload["summary"]["blocking_unfinished_count"], 4)
            self.assertEqual(payload["summary"]["verification_only_count"], 1)
            self.assertEqual(payload["summary"]["orphan_output_count"], 1)
            self.assertEqual(payload["orphan_outputs"][0]["task_id"], "thm_9_5_kernel")
            self.assertFalse(payload["orphan_outputs"][0]["has_prompt_pack"])
            self.assertEqual(payload["orphan_outputs"][0]["imported_by"], ["prob_11_6"])
            self.assertNotIn("obl_prob_11_6_tail_support", by_id)
            self.assertNotIn("thm_9_5_kernel", by_id)
            self.assertNotIn("prob_11_4", by_id)
            self.assertIn("critical_ch6_bridge_verify", by_id["thm_6_7__lemma_1"]["reasons"])
            self.assertIn("open_obligations", by_id["thm_10_8"]["reasons"])
            self.assertIn("metadata_drift_status_only", by_id["prob_11_5"]["reasons"])
            self.assertIn("public_surface_error", by_id["thm_13_13"]["reasons"])
            self.assertIn("public_surface_error", by_id["prob_11_6"]["reasons"])
            self.assertEqual(
                payload["summary"]["open_obligation_kind_counts"],
                {"proof_debt_support": 1},
            )
            self.assertEqual(payload["summary"]["open_interface_obligation_count"], 1)
            self.assertEqual(payload["summary"]["structural_field_landing_count"], 1)
            self.assertEqual(payload["summary"]["theorem_wrapper_structural_count"], 0)
            self.assertEqual(payload["summary"]["empty_landing_count"], 0)
            self.assertEqual(payload["summary"]["ledger_only_child_obligation_count"], 1)
            self.assertEqual(
                by_id["prob_11_6"]["open_obligation_details"][0]["id"],
                "tail_support",
            )
            self.assertTrue(by_id["prob_11_6"]["open_obligation_details"][0]["is_interface"])
            self.assertEqual(
                by_id["prob_11_6"]["open_obligation_details"][0]["landing_analysis"]["problem"],
                "structure_field_landing",
            )
            self.assertFalse(by_id["prob_11_6"]["open_obligation_details"][0]["child_has_output"])
            self.assertEqual(
                by_id["thm_6_7__lemma_1"]["action_bucket"],
                "critical_bridge_verification",
            )
            self.assertEqual(by_id["prob_11_5"]["action_bucket"], "metadata_drift")
            self.assertEqual(
                by_id["prob_11_6"]["action_bucket"],
                "public_surface_and_obligations",
            )
            self.assertEqual(
                by_id["thm_13_13"]["action_bucket"],
                "public_surface_cleanup",
            )

            by_bucket = {batch["bucket"]: batch for batch in payload["repair_batches"]}
            self.assertEqual(
                by_bucket["metadata_drift"]["task_ids"],
                ["prob_11_5"],
            )
            self.assertEqual(
                by_bucket["public_surface_and_obligations"]["task_ids"],
                ["prob_11_6"],
            )
            self.assertEqual(
                by_bucket["obligation_resolution"]["task_ids"],
                ["thm_10_8"],
            )
            self.assertEqual(
                payload["orphan_outputs"][0]["action_bucket"],
                "support_output_without_ledger",
            )

    def test_build_check_only_runs_on_unfinished_or_verify_items(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            for task_id in ["prob_11_1", "prob_11_6"]:
                (output / f"{task_id}.lean").write_text(
                    "theorem dummy : True := by exact True.intro\n",
                    encoding="utf-8",
                )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_11_1": {
                                "block_id": "prob_11_1",
                                "type": "Problem",
                                "status": "COMPLETED",
                            },
                            "prob_11_6": {
                                "block_id": "prob_11_6",
                                "type": "Problem",
                                "status": "FAILED_LOCAL",
                                "proof_obligation_summary": {
                                    "open_blocking_ids": ["tail_support"],
                                },
                            },
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            calls = []

            def fake_build(_root, task_id, _timeout):
                calls.append(task_id)
                return {"checked": True, "status": "ok"}

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=True,
                build_checker=fake_build,
            )

            self.assertEqual(calls, ["prob_11_6"])
            self.assertEqual(payload["items"][0]["task_id"], "prob_11_6")
            self.assertEqual(payload["summary"]["build_status_counts"], {"ok": 1})

    def test_proved_projection_wrapper_still_counts_as_open_proof_debt(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "prob_14_8").mkdir(parents=True)
            (output / "prob_14_8.lean").write_text(
                """
structure prob_14_8_MgfConvergenceSetup where
  mgf_to_characteristic_convergence : True

theorem prob_14_8_mgf_convergence_gives_characteristic_convergence
    (S : prob_14_8_MgfConvergenceSetup) : True :=
  S.mgf_to_characteristic_convergence
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_14_8": {
                                "block_id": "prob_14_8",
                                "type": "Problem",
                                "status": "COMPLETED",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_14_8" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "mgf_bridge",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "review_status": "accepted",
                                "lean_landing": "prob_14_8_mgf_convergence_gives_characteristic_convergence",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=False,
            )

            by_id = {item["task_id"]: item for item in payload["items"]}
            self.assertIn("open_obligations", by_id["prob_14_8"]["reasons"])
            detail = by_id["prob_14_8"]["open_obligation_details"][0]
            self.assertEqual(detail["id"], "mgf_bridge")
            self.assertEqual(
                detail["landing_analysis"]["problem"],
                "theorem_wrapper_over_projection_field",
            )
            self.assertEqual(
                detail["landing_analysis"]["projection_wrapper_theorems"],
                [
                    {
                        "name": "prob_14_8_mgf_convergence_gives_characteristic_convergence",
                        "projection": "S.mgf_to_characteristic_convergence",
                    }
                ],
            )

    def test_alignment_theorem_landings_clear_stale_proof_debt_landing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "prob_10_10").mkdir(parents=True)
            (output / "prob_10_10.lean").write_text(
                """
theorem prob_10_10_add_distribution_stability : True := by exact True.intro
theorem prob_10_10_mul_distribution_stability : True := by exact True.intro
theorem prob_10_10 : True := by exact True.intro
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_10_10": {
                                "block_id": "prob_10_10",
                                "type": "Problem",
                                "status": "COMPLETED",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_10_10" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "distribution_stability_under_probability_perturbation",
                                "kind": "proof_debt_support",
                                "status": "proved",
                                "review_status": "accepted",
                                "blocking": True,
                                "lean_landing": "h_add_perturbation_support, h_mul_perturbation_support",
                                "source_output_alignment": {
                                    "audit_class": "A_existing_theorem_candidate",
                                    "existing_local_declarations": [
                                        {
                                            "name": "prob_10_10_add_distribution_stability",
                                            "kind": "theorem",
                                        },
                                        {
                                            "name": "prob_10_10_mul_distribution_stability",
                                            "kind": "theorem",
                                        },
                                    ],
                                    "missing_landing_names": [],
                                },
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=False,
            )

            self.assertNotIn("prob_10_10", {item["task_id"] for item in payload["items"]})

    def test_review_covered_support_predicate_source_step_is_not_open(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "prob_11_9").mkdir(parents=True)
            (output / "prob_11_9.lean").write_text(
                """
def prob_11_9_asymptoticRegime : Prop := True
theorem prob_11_9 : True := by exact True.intro
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_11_9": {
                                "block_id": "prob_11_9",
                                "type": "Problem",
                                "status": "COMPLETED",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_11_9" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "asymptotic_regime",
                                "kind": "source_step",
                                "status": "partial",
                                "review_status": "needs_review",
                                "blocking": True,
                                "lean_landing": "prob_11_9_asymptoticRegime",
                                "landing_kind": "support_predicate",
                                "proof_contract_status": "not_applicable",
                                "proof_contract_notes": "Source assumption predicate.",
                            }
                        ],
                        "review_history": [
                            {
                                "reviewed_at": "2026-06-06T09:56:46.057870Z",
                                "verdict": "pass",
                                "status": "covered",
                                "open_blockers": [
                                    {
                                        "obligation_id": "asymptotic_regime",
                                        "issue": "covered",
                                    }
                                ],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=False,
            )

            self.assertNotIn("prob_11_9", {item["task_id"] for item in payload["items"]})

    def test_unreviewed_support_predicate_source_step_still_counts_open(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "prob_11_9").mkdir(parents=True)
            (output / "prob_11_9.lean").write_text(
                """
def prob_11_9_asymptoticRegime : Prop := True
theorem prob_11_9 : True := by exact True.intro
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_11_9": {
                                "block_id": "prob_11_9",
                                "type": "Problem",
                                "status": "COMPLETED",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_11_9" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "asymptotic_regime",
                                "kind": "source_step",
                                "status": "partial",
                                "review_status": "needs_review",
                                "blocking": True,
                                "lean_landing": "prob_11_9_asymptoticRegime",
                                "landing_kind": "support_predicate",
                                "proof_contract_status": "not_applicable",
                            }
                        ],
                        "review_history": [],
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=False,
            )

            by_id = {item["task_id"]: item for item in payload["items"]}
            self.assertIn("open_obligations", by_id["prob_11_9"]["reasons"])
            self.assertEqual(by_id["prob_11_9"]["open_blocking_ids"], ["asymptotic_regime"])

    def test_allowed_exception_boundary_is_visible_but_not_blocking(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "phase2_prompt_packs" / "thm_11_8").mkdir(parents=True)
            (output / "thm_11_8.lean").write_text(
                "theorem thm_11_8 : True := by exact True.intro\n",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "thm_11_8": {
                                "block_id": "thm_11_8",
                                "type": "Theorem",
                                "status": "COMPLETED",
                                "phase2_status": "allowed_exception",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "thm_11_8" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "obligations": [
                            {
                                "id": "etemadi_external_proof_bridge",
                                "kind": "source_step",
                                "status": "accepted_as_proof_debt",
                                "review_status": "accepted",
                                "blocking": True,
                                "lean_landing": "ProbabilityTheory.strong_law_ae",
                                "proof_contract_status": "beyond_book_exception",
                                "proof_contract_notes": "Explicit cited Etemadi external-proof exception.",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=False,
            )

            by_id = {item["task_id"]: item for item in payload["items"]}
            self.assertEqual(by_id["thm_11_8"]["reasons"], ["allowed_exception_boundary"])
            self.assertEqual(by_id["thm_11_8"]["action_bucket"], "allowed_exception_boundary")
            self.assertEqual(payload["summary"]["blocking_unfinished_count"], 0)
            report = markdown_report(payload)
            self.assertIn(
                "A zero blocking_unfinished_count does not claim external or beyond-book mathematics has been locally proved.",
                report,
            )

    def test_fail_gate_ignores_verification_only_bridge(self):
        self.assertFalse(
            has_blocking_unfinished(
                {
                    "summary": {
                        "unfinished_or_verify_count": 1,
                        "blocking_unfinished_count": 0,
                        "verification_only_count": 1,
                    },
                    "items": [{"task_id": "thm_6_7__lemma_1"}],
                }
            )
        )
        self.assertTrue(
            has_blocking_unfinished(
                {
                    "summary": {
                        "unfinished_or_verify_count": 2,
                        "blocking_unfinished_count": 1,
                        "verification_only_count": 1,
                    },
                    "items": [{"task_id": "prob_11_6"}],
                }
            )
        )

    def test_task_filter_limits_inventory_and_build_checks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            for task_id in ["prob_11_6", "prob_11_7"]:
                (output / f"{task_id}.lean").write_text(
                    "theorem dummy : True := by exact True.intro\n",
                    encoding="utf-8",
                )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            task_id: {
                                "block_id": task_id,
                                "type": "Problem",
                                "status": "FAILED_LOCAL",
                                "proof_obligation_summary": {
                                    "open_blocking_ids": ["tail_support"],
                                },
                            }
                            for task_id in ["prob_11_6", "prob_11_7"]
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            calls = []

            def fake_build(_root, task_id, _timeout):
                calls.append(task_id)
                return {"checked": True, "status": "ok"}

            payload = build_inventory(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
                check_build=True,
                only_tasks=["prob_11_7"],
                build_checker=fake_build,
            )

            self.assertEqual(calls, ["prob_11_7"])
            self.assertEqual([item["task_id"] for item in payload["items"]], ["prob_11_7"])

    def test_metadata_drift_fix_requires_successful_build_and_updates_symbols(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "ToyApollo" / "Output"
            output.mkdir(parents=True)
            (root / "docs").mkdir()
            (output / "prob_11_5.lean").write_text(
                """
private theorem prob_11_5_internal : True := by
  exact True.intro

theorem prob_11_5 : True := by
  exact True.intro
""",
                encoding="utf-8",
            )
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_11_5": {
                                "block_id": "prob_11_5",
                                "type": "Problem",
                                "status": "FAILED_LOCAL",
                                "output_hash": None,
                                "exported_symbols": ["old_symbol"],
                            }
                        },
                        "symbols": {"old_symbol": "prob_11_5", "other": "other_task"},
                    }
                ),
                encoding="utf-8",
            )
            payload = {
                "items": [
                    {
                        "task_id": "prob_11_5",
                        "action_bucket": "metadata_drift",
                    }
                ]
            }

            manifest = apply_metadata_drift_fixes(
                root,
                payload,
                build_timeout_seconds=5,
                build_checker=lambda _root, _task_id, _timeout: {
                    "checked": True,
                    "status": "ok",
                },
            )

            ledger = json.loads((root / "project_ledger.json").read_text(encoding="utf-8"))
            task = ledger["tasks"]["prob_11_5"]
            self.assertEqual(manifest["changed_task_count"], 1)
            self.assertEqual(task["status"], "COMPLETED")
            self.assertEqual(task["exported_symbols"], ["prob_11_5"])
            self.assertIn("prob_11_5", ledger["symbols"])
            self.assertNotIn("old_symbol", ledger["symbols"])
            self.assertEqual(ledger["symbols"]["other"], "other_task")

    def test_sync_ledger_proof_obligation_summaries_reopens_stale_completed_pack(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "phase2_prompt_packs" / "prob_14_8").mkdir(parents=True)
            (root / "phase2_prompt_packs" / "obl_prob_14_8_obligation_4").mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_14_8": {
                                "block_id": "prob_14_8",
                                "type": "Problem",
                                "status": "FAILED_LOCAL",
                                "proof_obligation_summary": {
                                    "open_blocking_ids": ["obligation_3", "obligation_4"],
                                    "status_counts": {"proved": 3, "open": 2},
                                },
                            },
                            "obl_prob_14_8_obligation_4": {
                                "block_id": "obl_prob_14_8_obligation_4",
                                "parent_task_id": "prob_14_8",
                                "type": "Phase2ObligationTask",
                                "status": "COMPLETED",
                                "proof_obligation_summary": {
                                    "open_blocking_ids": [],
                                    "status_counts": {"proved": 1},
                                },
                            },
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "prob_14_8" / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.proof_obligations.v1",
                        "task_id": "prob_14_8",
                        "obligations": [
                            {
                                "id": "obligation_3",
                                "kind": "proof_debt_support",
                                "status": "obsolete",
                                "review_status": "accepted",
                                "blocking": True,
                            },
                            {
                                "id": "obligation_4",
                                "kind": "proof_debt_support",
                                "status": "open",
                                "review_status": "needs_review",
                                "blocking": True,
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (
                root
                / "phase2_prompt_packs"
                / "obl_prob_14_8_obligation_4"
                / "proof_obligations.json"
            ).write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.proof_obligations.v1",
                        "task_id": "obl_prob_14_8_obligation_4",
                        "classification": {
                            "evidence": ["parent_task_id=prob_14_8"],
                        },
                        "obligations": [
                            {
                                "id": "obligation_4",
                                "kind": "proof_debt_support",
                                "status": "open",
                                "review_status": "needs_review",
                                "blocking": True,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            manifest = sync_ledger_proof_obligation_summaries(
                root,
                start_chapter=9,
                end_chapter=14,
                include_tasks=[],
            )

            ledger = json.loads((root / "project_ledger.json").read_text(encoding="utf-8"))
            parent_summary = ledger["tasks"]["prob_14_8"]["proof_obligation_summary"]
            child = ledger["tasks"]["obl_prob_14_8_obligation_4"]
            self.assertEqual(manifest["changed_task_count"], 2)
            self.assertEqual(manifest["status_changed_task_count"], 1)
            self.assertEqual(parent_summary["open_blocking_ids"], ["obligation_4"])
            self.assertEqual(parent_summary["status_counts"], {"obsolete": 1, "open": 1})
            self.assertEqual(child["status"], "FAILED_LOCAL")
            self.assertEqual(
                child["proof_obligation_summary"]["open_blocking_ids"],
                ["obligation_4"],
            )


if __name__ == "__main__":
    unittest.main()
