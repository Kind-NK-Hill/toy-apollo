import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.snapshot_phase2_current_status import (  # noqa: E402
    build_snapshot,
    write_snapshot,
)


class Phase2CurrentStatusSnapshotTests(unittest.TestCase):
    def test_snapshot_summarizes_current_ledger_without_promoting_obl_tasks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger = {
                "tasks": {
                    "prob_13_10": {
                        "block_id": "prob_13_10",
                        "type": "Problem",
                        "status": "COMPLETED",
                        "phase2_status": "pass",
                    },
                    "ex_1_3_2": {
                        "block_id": "ex_1_3_2",
                        "type": "Example",
                        "status": "PACKED",
                        "phase2_status": "fail",
                        "phase2_status_reason": "statement_or_source_mismatch",
                    },
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem",
                        "status": "DISCOVERED",
                        "phase2_status": "blocked",
                    },
                    "thm_14_8": {
                        "block_id": "thm_14_8",
                        "type": "Theorem",
                        "status": "COMPLETED_WITH_PROOF_DEBT",
                        "phase2_status": "allowed_exception",
                    },
                    "intro_10": {
                        "block_id": "intro_10",
                        "type": "Intro",
                        "status": "DISCOVERED",
                    },
                    "obl_prob_13_10_bridge": {
                        "block_id": "obl_prob_13_10_bridge",
                        "type": "ProofObligation",
                        "status": "COMPLETED",
                        "phase2_status": "pass",
                    },
                },
                "symbols": {
                    "Prob13_10.wald": {"owner": "prob_13_10"},
                    "OldObl.bridge": {"owner": "obl_prob_13_10_bridge"},
                },
            }
            ledger_path = root / "project_ledger.json"
            ledger_path.write_text(json.dumps(ledger, sort_keys=True), encoding="utf-8")

            snapshot = build_snapshot(root, generated_at="2026-06-19T00:00:00Z")

            self.assertEqual(snapshot["generated_at"], "2026-06-19T00:00:00Z")
            self.assertEqual(snapshot["ledger"]["path"], "project_ledger.json")
            self.assertEqual(snapshot["summary"]["task_count"], 5)
            self.assertEqual(snapshot["summary"]["symbol_count"], 2)
            self.assertEqual(snapshot["summary"]["legacy_obligation_task_count"], 1)
            self.assertEqual(snapshot["summary"]["legacy_obligation_symbol_owner_count"], 1)
            self.assertEqual(snapshot["summary"]["status_counts"]["COMPLETED"], 1)
            self.assertEqual(snapshot["summary"]["phase2_status_counts"]["pass"], 1)
            self.assertEqual(snapshot["summary"]["phase2_status_counts"]["missing"], 1)
            self.assertEqual(snapshot["exceptions"]["fail"][0]["task_id"], "ex_1_3_2")
            self.assertEqual(snapshot["exceptions"]["blocked"][0]["task_id"], "thm_1_2")
            self.assertEqual(snapshot["exceptions"]["allowed_exception"][0]["task_id"], "thm_14_8")
            self.assertEqual(snapshot["missing_phase2_status_sample"][0]["task_id"], "intro_10")

    def test_write_snapshot_writes_json_and_markdown_reports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "project_ledger.json").write_text(
                json.dumps(
                    {
                        "tasks": {
                            "prob_13_10": {
                                "block_id": "prob_13_10",
                                "type": "Problem",
                                "status": "COMPLETED",
                                "phase2_status": "pass",
                            }
                        },
                        "symbols": {},
                    }
                ),
                encoding="utf-8",
            )

            payload = write_snapshot(root, generated_at="2026-06-19T00:00:00Z")

            json_path = root / "docs" / "phase2_current_status_snapshot.json"
            md_path = root / "docs" / "phase2_current_status_snapshot.md"
            self.assertTrue(json_path.exists())
            self.assertTrue(md_path.exists())
            self.assertEqual(json.loads(json_path.read_text(encoding="utf-8")), payload)
            self.assertIn("Phase2 Current Status Snapshot", md_path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
