import asyncio
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_batch_controller import COMPLETED, NONTERMINAL  # noqa: E402
from src.toy_apollo.phase2_batch_runner import (  # noqa: E402
    _dependencies_from_record,
    _obligation_fingerprint,
    build_live_batch_state,
    plan_batch_from_ledger,
    render_batch_runner_plan,
    run_batch_actions,
)


class FakeLedger:
    def __init__(self, tasks):
        self.ledger = {"tasks": tasks}


class Phase2BatchRunnerTests(unittest.TestCase):
    def _settings(self, root: Path):
        output_dir = root / "ToyApollo" / "Output"
        output_dir.mkdir(parents=True)
        return SimpleNamespace(
            toyapollo_output_dir=output_dir,
            phase2_prompt_packs_dir=root / "phase2_prompt_packs",
        )

    def test_completed_without_phase2_status_requires_fresh_existing_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            (settings.toyapollo_output_dir / "thm_1_1.lean").write_text("-- ok\n", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": COMPLETED,
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_1_1"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--phase2-mode review-now", plan.actions[0].command)
        self.assertIn("--review-subject existing", plan.actions[0].command)
        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")

    def test_failed_task_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing Darboux tagged bridge",
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("--tasks def_1_2", plan.actions[0].command)

    def test_family_consumable_downstream_blocked_review_is_not_auto_looped(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            review_result = root / "phase2_prompt_packs" / "thm_7_8" / "semantic_review_result_v6.json"
            review_result.parent.mkdir(parents=True)
            review_result.write_text(
                json.dumps(
                    {
                        "verdict": "fail",
                        "proof_class": "source_route_support_completed_downstream_blocked",
                        "completion_class": "not_completed_downstream_blocked",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_review_expected_result_file": str(review_result),
                        "proof_obligation_summary": {
                            "open_blocking_ids": [],
                            "needs_concrete_decomposition": False,
                        },
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_7_8"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "inspect")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("direct downstream obligations", plan.actions[0].reason)

    def test_semantic_fail_triage_requiring_diagnoser_is_not_auto_looped(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "def_1_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(triage_path.with_name("prepared_diagnoser_prompt.txt")),
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "core obligation moved into a public premise",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "diagnoser_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("public_premise", plan.actions[0].reason)
        self.assertIn("read-only diagnoser", plan.actions[0].reason)

    def test_obligation_pack_manifest_overrides_stale_batch_plan_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "obl_obl_prob_14_1_obligation_1_concrete_child"
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            (pack_dir / "task.json").write_text(
                json.dumps(
                    {
                        "block_id": task_id,
                        "type": "Phase2ObligationTask",
                        "content": "Focused child.",
                        "dependencies": ["prob_13_11"],
                        "soft_imports": ["prob_14_1"],
                        "final_import_union": ["prob_13_11", "prob_14_1"],
                    }
                ),
                encoding="utf-8",
            )
            stale_record = {
                "block_id": task_id,
                "type": "Phase2ObligationTask",
                "dependencies": ["prob_14_1", "old_nonimportable_child"],
                "soft_imports": ["prob_14_1"],
                "final_import_union": ["prob_14_1", "old_nonimportable_child"],
            }

            deps = _dependencies_from_record(stale_record, task_id=task_id, settings=settings)

        self.assertEqual(deps, ["prob_13_11"])

    def test_diagnoser_result_requiring_source_rewrite_returns_author_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "thm_1_2"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "wrong_route",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "rewrite the source-facing proof decomposition",
                        "forbidden_shortcuts": ["do not continue patching private axioms"],
                        "required_local_checks": [],
                        "rationale": "The current route hides the source spine and needs decomposition first.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "current route hides the source spine",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_1_2"],
                ledger,
                settings,
                task_kinds=["theorem"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)
        self.assertIn("source-facing rewrite/decomposition", plan.actions[0].reason)
        self.assertNotIn("subagent-dispatch-required", rendered)

    def test_math_review_gate_blocks_risky_task_before_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "write a source-facing proof skeleton before Lean authoring",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.all_actions[0].action, "math_review_gate_required")
        self.assertEqual(plan.all_actions[0].command, "")
        self.assertIn("Math Review Gate", plan.all_actions[0].reason)
        self.assertIn("public_premise", plan.all_actions[0].reason)
        self.assertNotIn("--phase2-mode auto-loop", rendered)
        self.assertIn("math_review_gate_required", rendered)

    def test_math_review_gate_go_allows_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "rewrite from the source-facing proof skeleton",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "math_proof_skeleton_v1.md").write_text(
                "# Math Proof Skeleton\n\nSource-faithful proof route.",
                encoding="utf-8",
            )
            (pack_dir / "math_review_result_v1.json").write_text(
                json.dumps({"verdict": "go", "rounds": [{"round": 1}, {"round": 2}, {"round": 3}]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)

    def test_math_review_gate_stop_blocking_proof_surfaces_blocker_not_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            (pack_dir / "math_proof_skeleton_v8.md").write_text(
                "# Math Proof Skeleton\n\nAnalytic convergence is the remaining blocker.",
                encoding="utf-8",
            )
            (pack_dir / "math_review_result_v8.json").write_text(
                json.dumps(
                    {
                        "verdict": "stop",
                        "stop_mode": "blocking_proof",
                        "blocking_theorems": [
                            "prob_14_1_stirling_beta_cdf_convergence_internal"
                        ],
                        "allowed_next_targets": [
                            "gamma_ratio_global_power_bound",
                            "left_tail_eventually_small",
                            "scaled_mass_uniform_on_compact",
                        ],
                        "forbidden_work": ["ToyApollo/Output promotion", "semantic review"],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "private_axiom_or_open_math_debt",
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.all_actions[0].action, "blocking_proof_required")
        self.assertEqual(plan.all_actions[0].command, "")
        self.assertIn("blocking_proof", plan.all_actions[0].reason)
        self.assertIn("prob_14_1_stirling_beta_cdf_convergence_internal", plan.all_actions[0].reason)
        self.assertIn("gamma_ratio_global_power_bound", plan.all_actions[0].reason)
        self.assertIn("pre-author checklist", plan.all_actions[0].reason)
        self.assertIn("source statement identified", plan.all_actions[0].reason)
        self.assertIn("no public premise relocation", plan.all_actions[0].reason)
        self.assertIn("math proof skeleton reviewed go", plan.all_actions[0].reason)
        self.assertIn("independent semantic review after build", plan.all_actions[0].reason)
        self.assertNotIn("--phase2-mode auto-loop", rendered)

    def test_math_review_gate_missing_skeleton_surfaces_pre_author_checklist(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "math_review_gate_required")
        self.assertIn("pre-author checklist", plan.actions[0].reason)
        self.assertIn("source statement identified", plan.actions[0].reason)
        self.assertIn("no public premise relocation", plan.actions[0].reason)
        self.assertIn("math proof skeleton reviewed go", plan.actions[0].reason)
        self.assertIn("independent semantic review after build", plan.actions[0].reason)

    def test_diagnoser_result_requiring_obligation_promotion_routes_to_absorption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations for the unresolved source bridges",
                        "forbidden_shortcuts": ["do not keep public bridge premises"],
                        "required_local_checks": [],
                        "rationale": "The route is right but the unresolved bridges must be split into child obligations.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "source bridges are open debt",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                ["ex_14_4_1"],
                ledger,
                settings,
                task_kinds=["exercise"],
                limit=1,
                worker_slots=1,
            )

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)
        self.assertIn("obligation child promotion is disabled", plan.actions[0].reason)
        self.assertIn("absorb proof obligations into parent/support files", plan.actions[0].reason)

    def test_deeper_child_obligation_promotion_diagnosis_routes_to_absorption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "obl_obl_prob_14_12_obligation_5_obligation_5_limit_truncation_tail"
            pack_dir = root / "phase2_prompt_packs" / task_id
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_kind": "deeper_child_obligation_promotion",
                        "diagnosis_verdict": "promotion_required_not_ordinary_local_repair",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": (
                            "Promote or prove the missing bridge obligations before semantic review."
                        ),
                        "required_child_obligations": [
                            {
                                "id": "convergence_probability_extracts_ae_subsequence",
                                "status": "open",
                            }
                        ],
                        "forbidden_shortcuts": ["do not expose missing bridges as public hypotheses"],
                        "required_local_checks": [],
                        "rationale": "The source route is right but needs deeper child obligations.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "limit_truncation_tail_assembly",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "limit truncation tail route",
                "lean_landing": "prob_14_12_limit_truncation_tail_obligation",
                "notes": "promote deeper route obligations",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "limit truncation tail still exposes public bridge premises",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                [task_id],
                ledger,
                settings,
                limit=1,
                worker_slots=1,
                include_legacy=True,
            )

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("deeper_child_obligation_promotion", plan.actions[0].reason)
        self.assertIn("obligation child promotion is disabled", plan.actions[0].reason)

    def test_existing_child_obligations_do_not_drive_parent_promotion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Split the open debt into child tasks.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_ex_14_4_1_bridge": {
                        "block_id": "obl_ex_14_4_1_bridge",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "parent_block_id": "ex_14_4_1",
                        "obligation_fingerprint": _obligation_fingerprint("ex_14_4_1", obligation),
                    },
                }
            )

            unfiltered = plan_batch_from_ledger(["ex_14_4_1"], ledger, settings)
            queued = plan_batch_from_ledger(
                ["ex_14_4_1"],
                ledger,
                settings,
                task_kinds=["exercise"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(queued)

        self.assertEqual(unfiltered.actions[0].action, "foundation_absorb_required")
        self.assertEqual(unfiltered.actions[0].command, "")
        self.assertIn("obligation child promotion is disabled", unfiltered.actions[0].reason)
        self.assertEqual(len(queued.actions), 1)
        self.assertEqual(queued.actions[0].action, "foundation_absorb_required")
        self.assertIn("| 1 | ex_14_4_1 | exercise", rendered)
        self.assertIn("| fail | fail | foundation_absorb_required |", rendered)

    def test_diagnoser_result_allowing_local_repair_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "def_1_2"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "unclear_semantic_failure",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "ordinary_missing_step",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": True,
                        "recommended_next_action": "continue ordinary local proof repair",
                        "forbidden_shortcuts": [],
                        "required_local_checks": ["verify the helper lemma name locally"],
                        "rationale": "The route is accepted; one local bridge lemma is missing.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing accepted-route bridge lemma",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=true", plan.actions[0].reason)
        self.assertIn("ordinary repair", plan.actions[0].reason)

    def test_diagnoser_result_statement_mismatch_is_not_author_queue_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_7"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise_statement_weakened",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "statement_mismatch",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                        "forbidden_shortcuts": ["do not keep repairing the strengthened public statement"],
                        "required_local_checks": [],
                        "rationale": "The theorem proves a corrected statement with an extra public premise.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_7": {
                        "block_id": "prob_14_7",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "extra public premise on the limit objects",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            unfiltered = plan_batch_from_ledger(["prob_14_7"], ledger, settings)
            queued = plan_batch_from_ledger(
                ["prob_14_7"],
                ledger,
                settings,
                task_kinds=["problem"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(queued)

        self.assertEqual(unfiltered.actions[0].action, "source_statement_decision_required")
        self.assertEqual(unfiltered.actions[0].command, "")
        self.assertEqual(queued.actions, ())
        self.assertIn("source_statement_decision_required=1", rendered)

    def test_child_obligation_is_blocked_by_parent_source_statement_decision(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            parent_pack = root / "phase2_prompt_packs" / "thm_7_8"
            parent_pack.mkdir(parents=True)
            triage_path = parent_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_mismatch",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "source_statement_decision_required",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_thm_7_8_t7_8_rs_exists": {
                        "block_id": "obl_thm_7_8_t7_8_rs_exists",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "parent_task_id": "thm_7_8",
                        "target_task_id": "thm_7_8",
                        "obligation_id": "t7_8_rs_exists",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["obl_thm_7_8_t7_8_rs_exists"],
                ledger,
                settings,
                include_legacy=True,
            )

        self.assertEqual(plan.actions[0].action, "skip_blocked")
        self.assertIn("parent source/statement decision", plan.actions[0].reason)

    def test_source_decision_resolution_routes_remaining_obligations_to_absorption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            parent_pack = root / "phase2_prompt_packs" / "thm_7_8"
            parent_pack.mkdir(parents=True)
            triage_path = parent_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_mismatch",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "source_statement_decision_required",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "source_decision_resolution.json").write_text(
                json.dumps(
                    {
                        "status": "resolved",
                        "decision": "Use the strict finite-interval route: require a < b under def_1_2.",
                        "resolves_diagnoser_result": "diagnoser_result_v2.json",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.proof_obligations.v1",
                        "task_id": "thm_7_8",
                        "obligations": [
                            {
                                "id": "t7_8_rs_exists",
                                "status": "open",
                                "ledger_task_id": "obl_thm_7_8_t7_8_rs_exists",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "obl_thm_7_8_t7_8_rs_exists").mkdir(parents=True)
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_thm_7_8_t7_8_rs_exists": {
                        "block_id": "obl_thm_7_8_t7_8_rs_exists",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_task_id": "thm_7_8",
                        "target_task_id": "thm_7_8",
                        "obligation_id": "t7_8_rs_exists",
                    },
                }
            )

            parent_plan = plan_batch_from_ledger(["thm_7_8"], ledger, settings)
            child_plan = plan_batch_from_ledger(
                ["obl_thm_7_8_t7_8_rs_exists"],
                ledger,
                settings,
                include_legacy=True,
            )

        self.assertEqual(parent_plan.actions[0].action, "foundation_absorb_required")
        self.assertIn("source decision resolved", parent_plan.actions[0].reason)
        self.assertIn("absorb remaining concrete obligations", parent_plan.actions[0].reason)
        self.assertEqual(child_plan.actions[0].action, "auto_loop")

    def test_default_plan_hides_legacy_obligation_noise_when_parent_passed(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "source_route_proof_completed",
                        "phase2_completion_class": "source_route_proof_completed",
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                    "thm_7_9": {
                        "block_id": "thm_7_9",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing source-facing bridge",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["prob_14_1", "obl_prob_14_1_obligation_1", "thm_7_9"],
                ledger,
                settings,
                limit=20,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_7_9"])
        self.assertIn("hidden legacy/audit items", rendered)
        self.assertIn("legacy_obligation=1", rendered)
        self.assertNotIn("| obl_prob_14_1_obligation_1 |", rendered)

    def test_hidden_legacy_obligation_diagnoser_is_not_current_dispatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(["obl_prob_14_1_obligation_1"], ledger, settings)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertIn("legacy_obligation=1", rendered)
        self.assertNotIn("subagent-dispatch-required", rendered)
        self.assertNotIn("diagnoser_required=1", rendered)

    def test_legacy_mode_can_show_obligation_items_explicitly(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "phase2_review_verdict": "pass",
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["prob_14_1", "obl_prob_14_1_obligation_1"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertIn("obl_prob_14_1_obligation_1", [action.task_id for action in plan.actions])
        self.assertIn("| obl_prob_14_1_obligation_1 |", rendered)
        self.assertIn("hidden legacy/audit items: `0`", rendered)

    def test_restore_or_rebuild_output_is_diagnostic_when_draft_can_be_built(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "thm_1_1"
            pack_dir.mkdir(parents=True)
            (pack_dir / "draft.lean").write_text("-- buildable candidate\n", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": COMPLETED,
                    },
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "ordinary parent-facing failure",
                    },
                }
            )

            plan = plan_batch_from_ledger(["thm_1_1", "thm_1_2"], ledger, settings, limit=20)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_1_2"])
        self.assertIn("diagnostic_restore_or_rebuild_output=1", rendered)
        self.assertNotIn("| thm_1_1 |", rendered)

    def test_worker_queue_hides_section_intro_restore_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "thm_7_9"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "absorb obligations into parent/support files",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Former obligation material must not be re-promoted.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "intro_9_1": {
                        "block_id": "intro_9_1",
                        "type": "Remark",
                        "status": COMPLETED,
                    },
                    "thm_7_9": {
                        "block_id": "thm_7_9",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                }
            )

            plan = plan_batch_from_ledger(["intro_9_1", "thm_7_9"], ledger, settings, limit=2)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_7_9"])
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertIn("section_intro_remark=1", rendered)
        self.assertNotIn("| intro_9_1 |", rendered)

    def test_include_legacy_still_hides_section_intro_remarks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            ledger = FakeLedger(
                {
                    "intro_9_1": {
                        "block_id": "intro_9_1",
                        "type": "Remark",
                        "status": COMPLETED,
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["intro_9_1", "obl_prob_14_1_obligation_1"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertIn("obl_prob_14_1_obligation_1", [action.task_id for action in plan.actions])
        self.assertNotIn("intro_9_1", [action.task_id for action in plan.actions])
        self.assertIn("section_intro_remark=1", rendered)
        self.assertNotIn("| intro_9_1 |", rendered)

    def test_include_legacy_still_hides_skipped_source_statement_risks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "ex_1_3_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_or_source_mismatch",
                        "prompt_path": str(triage_path.with_name("prepared_diagnoser_prompt.txt")),
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem_Statement",
                        "status": NONTERMINAL,
                        "phase2_status": "blocked",
                        "phase2_status_reason": "proof_class dependency_blocked_pending_statement_decision",
                    },
                    "ex_1_3_2": {
                        "block_id": "ex_1_3_2",
                        "type": "Example_Proof",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_1_2", "ex_1_3_2"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertEqual({action.task_id for action in plan.hidden_actions}, {"thm_1_2", "ex_1_3_2"})
        self.assertIn("source_statement_risk=2", rendered)
        self.assertIn("ordinary_action_queue_clear: `true`", rendered)
        self.assertIn(
            "deferred_source_statement_risk_exceptions: `2` (`ex_1_3_2`, `thm_1_2`)",
            rendered,
        )
        self.assertNotIn("subagent-dispatch-required", rendered)
        self.assertNotIn("| thm_1_2 |", rendered)
        self.assertNotIn("| ex_1_3_2 |", rendered)

    def test_batch_run_skips_diagnoser_required_and_dispatches_next_executable_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "def_1_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "def_1_3": {
                        "block_id": "def_1_3",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                }
            )

            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["def_1_2", "def_1_3"], ledger, settings, max_actions=1))

        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_3")

    def test_batch_run_skips_reviewer_required_and_dispatches_next_executable_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            waiting_pack = settings.phase2_prompt_packs_dir / "prob_14_2"
            waiting_pack.mkdir(parents=True)
            expected_result = waiting_pack / "semantic_review_result_v6.json"
            review_request = waiting_pack / "semantic_review_request_v6.json"
            review_request.write_text("{}", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "prob_14_2": {
                        "block_id": "prob_14_2",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "current_auto_loop_phase": "reviewing",
                        "current_auto_loop_status": "active",
                        "current_review_request_file": str(review_request),
                        "current_review_expected_result_file": str(expected_result),
                    },
                    "def_1_3": {
                        "block_id": "def_1_3",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                }
            )

            plan = plan_batch_from_ledger(["prob_14_2", "def_1_3"], ledger, settings)
            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["prob_14_2", "def_1_3"], ledger, settings, max_actions=1))

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["prob_14_2"].action, "reviewer_required")
        self.assertIn("semantic_review_result_v6.json", actions["prob_14_2"].reason)
        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_3")

    def test_batch_run_does_not_execute_obligation_promotion_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Split the open debt into child tasks.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            with patch(
                "src.toy_apollo.phase2_obligation_tasks.promote_all_obligation_tasks",
                return_value={
                    "parents_scanned": ["ex_14_4_1"],
                    "created": ["obl_ex_14_4_1_bridge"],
                    "updated": [],
                    "skipped": [],
                    "created_count": 1,
                    "updated_count": 0,
                },
            ) as promote_mock:
                result = asyncio.run(run_batch_actions(["ex_14_4_1"], ledger, settings, max_actions=1))

        promote_mock.assert_not_called()
        self.assertEqual(len(result.executed), 0)
        self.assertEqual(result.details, ())
        self.assertEqual(result.plan.actions[0].action, "foundation_absorb_required")

    def test_current_review_request_without_auto_loop_phase_requires_reviewer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "thm_11_6"
            pack_dir.mkdir(parents=True)
            request_path = pack_dir / "semantic_review_request_v29.json"
            result_path = pack_dir / "semantic_review_result_v29.json"
            request_path.write_text("{}", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_11_6": {
                        "block_id": "thm_11_6",
                        "type": "Theorem",
                        "status": COMPLETED,
                        "current_review_request_file": str(request_path),
                        "current_review_expected_result_file": str(result_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_11_6"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "reviewer_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("semantic_review_result_v29.json", plan.actions[0].reason)

    def test_blocked_downstream_is_skipped_until_root_repairs(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "root": {
                        "block_id": "root",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "blocked",
                        "phase2_status_reason": "dependency gate",
                    },
                    "downstream": {
                        "block_id": "downstream",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["root"],
                    },
                }
            )

            plan = plan_batch_from_ledger(["root", "downstream"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["root"].action, "blocked")
        self.assertEqual(actions["downstream"].action, "skip_blocked")
        self.assertEqual(actions["downstream"].command, "")
        self.assertIn("root", actions["downstream"].reason)

    def test_pack_metadata_final_import_union_feeds_dependency_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "ex_14_4_3"
            pack_dir.mkdir(parents=True)
            (pack_dir / "metadata.json").write_text(
                json.dumps({"final_import_union": ["thm_14_8"]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_14_8": {
                        "block_id": "thm_14_8",
                        "type": "Theorem",
                        "status": "COMPLETED_WITH_PROOF_DEBT",
                        "proof_obligation_summary": {
                            "status_counts": {"accepted_as_proof_debt": 1},
                            "needs_concrete_decomposition": False,
                        },
                    },
                    "ex_14_4_3": {
                        "block_id": "ex_14_4_3",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                    },
                }
            )

            plan = plan_batch_from_ledger(["thm_14_8", "ex_14_4_3"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["ex_14_4_3"].action, "skip_blocked")
        self.assertIn("thm_14_8", actions["ex_14_4_3"].reason)

    def test_diagnoser_required_dependency_blocks_downstream_from_metadata_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            upstream_pack = settings.phase2_prompt_packs_dir / "prob_14_8"
            downstream_pack = settings.phase2_prompt_packs_dir / "prob_14_10"
            upstream_pack.mkdir(parents=True)
            downstream_pack.mkdir(parents=True)
            triage_path = upstream_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (downstream_pack / "metadata.json").write_text(
                json.dumps({"final_import_union": ["prob_14_8"]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_8": {
                        "block_id": "prob_14_8",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "prob_14_10": {
                        "block_id": "prob_14_10",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_verify_result_file": str(downstream_pack / "verify_result_v1.json"),
                    },
                }
            )

            plan = plan_batch_from_ledger(["prob_14_8", "prob_14_10"], ledger, settings)
            external_dependency_plan = plan_batch_from_ledger(["prob_14_10"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["prob_14_8"].action, "diagnoser_required")
        self.assertEqual(actions["prob_14_10"].action, "skip_blocked")
        self.assertIn("prob_14_8", actions["prob_14_10"].reason)
        self.assertIn("diagnoser", actions["prob_14_10"].reason)
        external_actions = {action.task_id: action for action in external_dependency_plan.actions}
        self.assertEqual(external_actions["prob_14_10"].action, "skip_blocked")
        self.assertIn("prob_14_8", external_actions["prob_14_10"].reason)

    def test_live_batch_state_is_read_only_projection(self):
        ledger = FakeLedger(
            {
                "prob_11_6": {
                    "block_id": "prob_11_6",
                    "type": "Problem",
                    "status": COMPLETED,
                    "phase2_status": "pass",
                    "proof_class": "textbook_problem_completed",
                    "review_verdict": "pass",
                }
            }
        )

        state = build_live_batch_state(["prob_11_6"], ledger)

        self.assertEqual(state["batch_id"], "live-ledger")
        self.assertEqual(state["tasks"][0]["task_id"], "prob_11_6")
        self.assertEqual(state["tasks"][0]["phase2_status"], "pass")

    def test_batch_run_dispatches_only_bounded_executable_actions(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing bridge",
                    },
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["def_1_2"],
                    },
                }
            )

            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["def_1_2", "thm_1_1"], ledger, settings, max_actions=1))

        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_2")

    def test_latest_verify_build_failure_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            verify_path = root / "phase2_prompt_packs" / "def_1_4" / "verify_result_v1.json"
            verify_path.parent.mkdir(parents=True)
            verify_path.write_text(
                json.dumps(
                    {
                        "success": False,
                        "disposition": "review_existing_build_failed_no_review",
                        "primary_failure_kind": "unknown_identifier",
                        "diagnostics": [
                            {
                                "kind": "unknown_identifier",
                                "message": "Unknown identifier `RSCore.RSIntegral`",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_4": {
                        "block_id": "def_1_4",
                        "type": "Definition",
                        "status": "PACKED",
                        "latest_verify_result_file": str(verify_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_4"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("unknown_identifier", plan.actions[0].reason)

    def test_completed_missing_status_with_verify_build_failure_routes_to_auto_loop_before_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            (settings.toyapollo_output_dir / "thm_13_3.lean").write_text("-- stale official output\n", encoding="utf-8")
            verify_path = root / "phase2_prompt_packs" / "thm_13_3" / "verify_result_v1.json"
            verify_path.parent.mkdir(parents=True)
            verify_path.write_text(
                json.dumps(
                    {
                        "success": False,
                        "disposition": "review_existing_build_failed_no_review",
                        "primary_failure_kind": "type_mismatch",
                        "diagnostics": [
                            {
                                "kind": "type_mismatch",
                                "message": "l2Norm now requires an L2Function proof argument",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_13_3": {
                        "block_id": "thm_13_3",
                        "type": "Theorem",
                        "status": COMPLETED,
                        "latest_verify_result_file": str(verify_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_13_3"], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("type_mismatch", plan.actions[0].reason)

    def test_worker_queue_prefers_non_problem_roots_by_fanout_and_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "thm_low": {
                        "block_id": "thm_low",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "thm_high": {
                        "block_id": "thm_high",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "def_root": {
                        "block_id": "def_root",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "prob_root": {
                        "block_id": "prob_root",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "downstream_a": {
                        "block_id": "downstream_a",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_high"],
                    },
                    "downstream_b": {
                        "block_id": "downstream_b",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_high"],
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_low", "thm_high", "def_root", "prob_root", "downstream_a", "downstream_b"],
                ledger,
                settings,
                task_kinds=["theorem", "definition"],
                limit=2,
                worker_slots=2,
            )

        self.assertEqual([action.task_id for action in plan.actions], ["thm_high", "def_root"])
        self.assertEqual(plan.actions[0].fanout, 2)
        self.assertEqual(plan.actions[0].worker_slot, 1)
        self.assertEqual(plan.actions[1].worker_slot, 2)
        self.assertEqual(plan.actions[0].conflict_group, "task:thm_high")

    def test_empty_worker_queue_reports_subagent_dispatch_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "thm_root" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "mathlib_adapter",
                    }
                ),
                encoding="utf-8",
            )
            review_pack = settings.phase2_prompt_packs_dir / "thm_review"
            review_pack.mkdir(parents=True)
            request_path = review_pack / "semantic_review_request_v1.json"
            result_path = review_pack / "semantic_review_result_v1.json"
            request_path.write_text("{}", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_root": {
                        "block_id": "thm_root",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "thm_review": {
                        "block_id": "thm_review",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "current_review_request_file": str(request_path),
                        "current_review_expected_result_file": str(result_path),
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_root", "thm_review"],
                ledger,
                settings,
                task_kinds=["theorem"],
                limit=5,
                worker_slots=2,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertIn("subagent-dispatch-required", rendered)
        self.assertIn("reviewer_required=1", rendered)
        self.assertIn("diagnoser_required=1", rendered)


if __name__ == "__main__":
    unittest.main()
