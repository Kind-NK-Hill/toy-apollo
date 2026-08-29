import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_obligation_tasks import (  # noqa: E402
    MAX_OBLIGATION_TASK_ID_LENGTH,
    obligation_task_id,
    promote_all_obligation_tasks,
    promote_obligation_tasks_for_task,
)


class Phase2ObligationTaskTests(unittest.TestCase):
    def test_obligation_task_id_shortens_deep_nested_names(self):
        parent = (
            "obl_obl_obl_prob_7_3_p7_3_a_rs_lebesgue_criterion_"
            "rs_integrable_implies_ae_continuity_discontinuity_implies_positive_local_oscillation"
        )
        child_a = obligation_task_id(parent, "p7_3_relative_local_oscillation_predicate")
        child_b = obligation_task_id(parent, "p7_3_largeOscillationSet_definition")

        self.assertLessEqual(len(child_a), MAX_OBLIGATION_TASK_ID_LENGTH)
        self.assertLessEqual(len(child_b), MAX_OBLIGATION_TASK_ID_LENGTH)
        self.assertTrue(child_a.startswith("obl_obl_obl_obl_prob_7_3"))
        self.assertNotEqual(child_a, child_b)

    def test_promote_obligation_tasks_for_task_is_disabled(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = SimpleNamespace(phase2_prompt_packs_dir=Path(tmp) / "phase2_prompt_packs")
            settings.phase2_prompt_packs_dir.mkdir(parents=True)
            ledger = SimpleNamespace(ledger={"tasks": {"thm_10_8": {"block_id": "thm_10_8"}}})

            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)

        self.assertEqual(report.parent_task_id, "thm_10_8")
        self.assertEqual(report.created, [])
        self.assertEqual(report.updated, [])
        self.assertEqual(
            report.skipped,
            ["obligation child promotion is disabled; absorb proof obligations into parent/support files"],
        )

    def test_promote_all_obligation_tasks_is_disabled(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = SimpleNamespace(phase2_prompt_packs_dir=Path(tmp) / "phase2_prompt_packs")
            settings.phase2_prompt_packs_dir.mkdir(parents=True)
            ledger = SimpleNamespace(ledger={"tasks": {}})

            report = promote_all_obligation_tasks(ledger, settings, ["thm_10_8", "prob_14_1"])

        self.assertEqual(report["parents_scanned"], ["thm_10_8", "prob_14_1"])
        self.assertEqual(report["created"], [])
        self.assertEqual(report["updated"], [])
        self.assertEqual(report["created_count"], 0)
        self.assertEqual(report["updated_count"], 0)
        self.assertEqual(
            report["skipped"],
            [
                "thm_10_8:obligation child promotion is disabled; absorb proof obligations into parent/support files",
                "prob_14_1:obligation child promotion is disabled; absorb proof obligations into parent/support files",
            ],
        )


if __name__ == "__main__":
    unittest.main()
