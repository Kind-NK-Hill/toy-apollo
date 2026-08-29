import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_batch_controller import analyze_batch_state  # noqa: E402
from src.toy_apollo.phase2_batch_runner import (  # noqa: E402
    build_live_batch_state,
    plan_batch_from_ledger,
)


class FakeLedger:
    def __init__(self, tasks):
        self.ledger = {"tasks": tasks}


class Phase2DependencyGateTests(unittest.TestCase):
    def _settings(self, root: Path):
        output_dir = root / "ToyApollo" / "Output"
        output_dir.mkdir(parents=True)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True)
        return SimpleNamespace(
            toyapollo_output_dir=output_dir,
            phase2_prompt_packs_dir=root / "phase2_prompt_packs",
            plans_dir=plans_dir,
        )

    @staticmethod
    def _write_plan(settings, tasks):
        (settings.plans_dir / "dependency_gate_plan.json").write_text(
            json.dumps(tasks),
            encoding="utf-8",
        )

    @staticmethod
    def _plan_task(task_id, task_type, dependencies=None):
        return {
            "block_id": task_id,
            "type": task_type,
            "content": f"Test task {task_id}.",
            "dependencies": list(dependencies or []),
            "source_plan": "dependency_gate",
        }

    def test_batch_external_unregistered_nonterminal_and_blank_status_dependencies_fail_closed(self):
        cases = [
            ("unregistered", None),
            (
                "nonterminal",
                {
                    "block_id": "def_4_1",
                    "type": "Definition",
                    "status": "NONTERMINAL",
                    "phase2_status": "",
                },
            ),
            (
                "completed_without_phase2_status",
                {
                    "block_id": "def_4_1",
                    "type": "Definition",
                    "status": "COMPLETED",
                    "phase2_status": "",
                },
            ),
        ]
        for label, dependency_record in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                settings = self._settings(Path(tmp))
                self._write_plan(
                    settings,
                    [self._plan_task("thm_5_1", "Theorem_Statement", ["def_4_1"])],
                )
                tasks = {
                    "thm_5_1": {
                        "block_id": "thm_5_1",
                        "type": "Theorem_Statement",
                        "status": "NONTERMINAL",
                        "dependencies": ["def_4_1"],
                    }
                }
                if dependency_record is not None:
                    tasks["def_4_1"] = dependency_record
                ledger = FakeLedger(tasks)
                before = copy.deepcopy(ledger.ledger)

                state = build_live_batch_state(["thm_5_1"], ledger, settings)
                plan = plan_batch_from_ledger(["thm_5_1"], ledger, settings)

                projected_ids = {task["task_id"] for task in state["tasks"]}
                selected_row = next(row for row in plan.report.rows if row.task_id == "thm_5_1")
                self.assertIn("def_4_1", projected_ids)
                self.assertEqual(selected_row.blocked_dependency, "def_4_1")
                self.assertEqual(plan.actions[0].action, "skip_blocked")
                self.assertEqual(ledger.ledger, before)

    def test_actual_formal_imports_are_unioned_with_resolver_edges_for_requested_mappings(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            mappings = {
                "def_6_4": "thm_4_5",
                "def_7_2": "thm_7_10",
                "def_7_3": "thm_7_13",
            }
            plan_tasks = [self._plan_task("def_5_1", "Definition")]
            plan_tasks.extend(
                self._plan_task(dependency_id, "Theorem_Statement")
                for dependency_id in mappings.values()
            )
            plan_tasks.extend(
                self._plan_task(task_id, "Definition", ["def_5_1"])
                for task_id in mappings
            )
            self._write_plan(settings, plan_tasks)
            ledger_tasks = {}
            for task_id, imported_task_id in mappings.items():
                (settings.toyapollo_output_dir / f"{task_id}.lean").write_text(
                    f"import Mathlib\nimport ToyApollo.Output.{imported_task_id}\n",
                    encoding="utf-8",
                )
                ledger_tasks[task_id] = {
                    "block_id": task_id,
                    "type": "Definition",
                    "status": "NONTERMINAL",
                    "dependencies": ["def_5_1"],
                }
            ledger = FakeLedger(ledger_tasks)
            before = copy.deepcopy(ledger.ledger)

            state = build_live_batch_state(list(mappings), ledger, settings)

            projected = {task["task_id"]: task for task in state["tasks"]}
            for task_id, imported_task_id in mappings.items():
                with self.subTest(task_id=task_id):
                    self.assertEqual(
                        set(projected[task_id]["dependencies"]),
                        {"def_5_1", imported_task_id},
                    )
                    self.assertIn(imported_task_id, projected)
            self.assertEqual(ledger.ledger, before)

    def test_selected_task_expands_complete_transitive_dependency_closure_before_analysis(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    self._plan_task("thm_5_2", "Theorem_Statement", ["thm_5_1"]),
                    self._plan_task("thm_5_1", "Theorem_Statement", ["def_4_1"]),
                    self._plan_task("def_4_1", "Definition"),
                ],
            )
            ledger = FakeLedger(
                {
                    "thm_5_2": {
                        "block_id": "thm_5_2",
                        "status": "NONTERMINAL",
                        "dependencies": ["thm_5_1"],
                    },
                    "thm_5_1": {
                        "block_id": "thm_5_1",
                        "status": "NONTERMINAL",
                        "dependencies": ["def_4_1"],
                    },
                }
            )

            state = build_live_batch_state(["thm_5_2"], ledger, settings)
            plan = plan_batch_from_ledger(["thm_5_2"], ledger, settings)

            self.assertEqual(
                {task["task_id"] for task in state["tasks"]},
                {"thm_5_2", "thm_5_1", "def_4_1"},
            )
            self.assertEqual(
                {row.task_id for row in plan.report.rows},
                {"thm_5_2", "thm_5_1", "def_4_1"},
            )
            selected_row = next(row for row in plan.report.rows if row.task_id == "thm_5_2")
            self.assertEqual(selected_row.blocked_dependency, "thm_5_1")

    def test_support_module_closure_projects_recursive_formal_task_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    self._plan_task("prob_7_3", "Problem"),
                    self._plan_task("def_1_2", "Definition"),
                    self._plan_task("thm_7_8", "Theorem_Statement"),
                ],
            )
            (settings.toyapollo_output_dir / "prob_7_3.lean").write_text(
                "import ToyApollo.Output.prob_7_3_proof_support\n",
                encoding="utf-8",
            )
            (settings.toyapollo_output_dir / "prob_7_3_proof_support.lean").write_text(
                "\n".join(
                    [
                        "import ToyApollo.Output.prob_7_3_nested_support",
                        "import ToyApollo.Output.def_1_2",
                    ]
                ),
                encoding="utf-8",
            )
            (settings.toyapollo_output_dir / "prob_7_3_nested_support.lean").write_text(
                "import ToyApollo.Output.thm_7_8\n",
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_7_3": {
                        "block_id": "prob_7_3",
                        "type": "Problem",
                        "status": "NONTERMINAL",
                        "dependencies": [],
                    }
                }
            )

            state = build_live_batch_state(["prob_7_3"], ledger, settings)
            plan = plan_batch_from_ledger(["prob_7_3"], ledger, settings)

            projected = {task["task_id"]: task for task in state["tasks"]}
            selected_row = next(row for row in plan.report.rows if row.task_id == "prob_7_3")
            self.assertEqual(set(projected["prob_7_3"]["dependencies"]), {"def_1_2", "thm_7_8"})
            self.assertTrue({"def_1_2", "thm_7_8"}.issubset(projected))
            self.assertIn(selected_row.blocked_dependency, {"def_1_2", "thm_7_8"})
            self.assertEqual(plan.actions[0].action, "skip_blocked")

    def test_existing_pass_is_invalidated_when_hard_dependency_loses_current_pass(self):
        report = analyze_batch_state(
            {
                "batch_id": "pass-invalidation",
                "tasks": [
                    {
                        "task_id": "def_5_1",
                        "type": "Definition",
                        "status": "COMPLETED",
                        "phase2_status": "needs_fresh_review",
                    },
                    {
                        "task_id": "thm_5_1",
                        "type": "Theorem_Statement",
                        "status": "COMPLETED",
                        "phase2_status": "pass",
                        "dependencies": ["def_5_1"],
                    },
                ],
            }
        )

        row = next(item for item in report.rows if item.task_id == "thm_5_1")
        self.assertEqual(row.blocked_dependency, "def_5_1")
        self.assertEqual(row.task_status, "blocked")
        self.assertEqual(row.report_status, "needs_fresh_review")
        self.assertEqual(row.task_status_evidence_type, "dependency_authority_invalidated")
        self.assertFalse(row.clean_or_allowed_exception)

    def test_controller_fails_closed_when_dependency_node_is_absent(self):
        report = analyze_batch_state(
            {
                "batch_id": "missing-node",
                "tasks": [
                    {
                        "task_id": "thm_5_1",
                        "status": "NONTERMINAL",
                        "dependencies": ["def_4_1"],
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.blocked_dependency, "def_4_1")
        self.assertEqual(row.task_status, "blocked")

    def test_completed_current_pass_dependency_remains_consumable(self):
        report = analyze_batch_state(
            {
                "batch_id": "current-pass",
                "tasks": [
                    {
                        "task_id": "def_5_1",
                        "status": "COMPLETED",
                        "phase2_status": "pass",
                    },
                    {
                        "task_id": "thm_5_1",
                        "status": "NONTERMINAL",
                        "dependencies": ["def_5_1"],
                    },
                ],
            }
        )

        row = next(item for item in report.rows if item.task_id == "thm_5_1")
        self.assertEqual(row.blocked_dependency, "")


if __name__ == "__main__":
    unittest.main()
