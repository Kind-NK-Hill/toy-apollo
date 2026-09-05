"""Synthetic protocol tests; their outcomes are not review-quality measurements."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from formalization_engine.review_comparison_pilot import (
    digest, load_manifest, prepare, read_json, score, seal_translation,
)


class ReviewComparisonPilotTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.manifest_path = self.root / "manifest.json"
        self.prepared = self.root / "prepared"
        self.results_path = self.root / "results.json"
        self.truth_path = self.root / "adjudications.json"
        tasks = []
        for task_id in ("case01", "case02"):
            task = {"task_id": task_id}
            for kind, text in (("source", "For all natural numbers n, n + 0 = n.\n"),
                               ("lean", "example (n : Nat) : n + 0 = n := rfl\n")):
                path = self.root / f"{task_id}.{kind}"
                path.write_bytes(text.encode())
                task[kind] = {"path": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            tasks.append(task)
        self.write(self.manifest_path, {"schema_version": 1, "pilot_id": "unit-fixture",
            "model": "fixture-model", "model_config": {"temperature": 0}, "budget": {"input_tokens": 100,
            "output_tokens": 100, "elapsed_seconds": 100}, "tasks": tasks})
        prepare(self.manifest_path, self.prepared)
        self.records = []
        self.truths = []
        for task_id in ("case01", "case02"):
            translation_request = read_json(self.prepared / task_id / "translate.request.json")
            translation = {"request_sha256": digest(translation_request), "model": "fixture-model",
                "model_config": {"temperature": 0},
                "session_id": f"translate-{task_id}", "text": "Fixture translation.",
                "usage": self.usage(10)}
            path = self.root / f"{task_id}.translation.json"
            self.write(path, translation)
            seal_translation(self.manifest_path, self.prepared, task_id, path)
            for arm in ("ordinary", "reverse_translation"):
                request = read_json(self.prepared / task_id / f"{arm}.request.json")
                self.records.append({"task_id": task_id, "arm": arm,
                    "request_sha256": digest(request), "subject_sha256": request["subject_sha256"],
                    "model": "fixture-model", "session_id": f"{arm}-{task_id}",
                    "model_config": {"temperature": 0},
                    "verdict": "pass", "rationale": "Artificial scoring test only.",
                    "usage": self.usage(20)})
            self.truths.append({"task_id": task_id, "subject_sha256": request["subject_sha256"],
                "provenance": "synthetic_test_only", "verdict": "pass",
                "rationale": "Artificial scoring fixture; not a source-fidelity finding."})

    @staticmethod
    def usage(n):
        return {"input_tokens": n, "output_tokens": n, "elapsed_seconds": n, "cost_usd": n / 1000}

    @staticmethod
    def write(path, value):
        path.write_text(json.dumps(value), encoding="utf-8")

    def run_score(self):
        self.write(self.results_path, self.records)
        self.write(self.truth_path, self.truths)
        return score(self.manifest_path, self.prepared, self.results_path, self.truth_path)

    def test_translation_is_source_blind_and_budget_is_shared(self):
        request = read_json(self.prepared / "case01" / "translate.request.json")
        self.assertNotIn("source", request)
        self.assertNotIn("subject_sha256", request)
        self.assertNotIn("manifest_sha256", request)
        assisted = read_json(self.prepared / "case01" / "reverse_translation.request.json")
        self.assertEqual(assisted["budget"]["input_tokens"], 90)
        self.assertNotIn("verdict", assisted)
        result = self.run_score()
        self.assertEqual(result["qa_status"], "valid")
        self.assertEqual(result["groups"]["synthetic_test_only"]["arms"]["reverse_translation"]["usage"]["input_tokens"], 60)
        self.assertEqual(result["empirical_status"], "pending_independent_human_adjudication")

    def test_missing_truth_reports_pending_without_accuracy(self):
        for truth in self.truths:
            truth["provenance"] = "independent_human"
            truth["verdict"] = "pending"
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertEqual(result["unadjudicated_tasks"], ["case01", "case02"])
        self.assertEqual(len(result["paired_process"]["tasks"]), 2)
        self.assertNotIn("accuracy", json.dumps(result))

    def test_duplicate_excludes_all_versions_and_reports_missing(self):
        self.records.append(self.records[0].copy())
        self.records = [r for r in self.records if not (r["task_id"] == "case02" and r["arm"] == "ordinary")]
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertEqual({i["kind"] for i in result["issues"]}, {"duplicate", "missing"})

    def test_tampered_hash_model_and_budget_rejected(self):
        for field, value in (("request_sha256", "wrong"), ("subject_sha256", "wrong"),
                             ("model", "other-model"), ("model_config", {"temperature": 1}),
                             ("usage", self.usage(95))):
            with self.subTest(field=field):
                old = self.records[1][field]
                self.records[1][field] = value
                result = self.run_score()
                self.assertIn("case01", result["unpaired_tasks"])
                self.assertTrue(any(i["kind"] == "invalid_record" for i in result["issues"]))
                self.records[1][field] = old

    def test_metrics_and_human_truth_are_separate(self):
        self.truths[0]["verdict"] = "fail"
        self.records[1]["verdict"] = "abstain"
        self.truths[1].update(provenance="independent_human", adjudicator_id="human-fixture",
            independent_of_review_arms=True, blinded_to_arm_results=True)
        self.records[2]["verdict"] = "fail"
        result = self.run_score()
        synthetic = result["groups"]["synthetic_test_only"]
        human = result["groups"]["independent_human"]
        self.assertEqual(synthetic["arms"]["ordinary"]["false_accept"], 1)
        self.assertEqual(synthetic["arms"]["reverse_translation"]["abstain"], 1)
        self.assertEqual(human["arms"]["ordinary"]["false_reject"], 1)
        self.assertEqual(human["paired_tasks"], ["case02"])

    def test_historical_or_unattested_truth_cannot_score(self):
        self.truths[0]["provenance"] = "historical_review_pass"
        self.truths[1]["provenance"] = "independent_human"
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertEqual(len(result["unadjudicated_tasks"]), 2)

    def test_session_reuse_and_adjudicator_overlap_rejected(self):
        self.records[1]["session_id"] = self.records[0]["session_id"]
        self.truths[1].update(provenance="independent_human", adjudicator_id=self.records[2]["session_id"],
            independent_of_review_arms=True, blinded_to_arm_results=True)
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertIn("case01", result["unpaired_tasks"])
        self.assertIn("case02", result["unadjudicated_tasks"])
        self.assertEqual(result["valid_review_records"], 2)

    def test_session_reuse_across_tasks_excludes_both_pairs(self):
        # A case02 ordinary reviewer reuses the case01 translator's context.
        self.records[2]["session_id"] = "translate-case01"
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertEqual(result["unpaired_tasks"], ["case01", "case02"])
        self.assertEqual(result["valid_review_records"], 0)
        self.assertEqual(result["paired_process"]["tasks"], [])
        self.assertEqual(len([i for i in result["issues"] if i["kind"] == "invalid_pair"]), 2)

    def test_mutated_translation_or_request_cannot_score(self):
        path = self.prepared / "case01" / "translation.sealed.json"
        translation = read_json(path)
        translation["text"] = "Edited after sealing"
        self.write(path, translation)
        result = self.run_score()
        self.assertIn("case01", result["unpaired_tasks"])

    def test_input_changes_rejected_and_outputs_never_overwritten(self):
        with self.assertRaisesRegex(ValueError, "must not already exist"):
            prepare(self.manifest_path, self.prepared)
        with self.assertRaisesRegex(ValueError, "already sealed"):
            seal_translation(self.manifest_path, self.prepared, "case01", self.root / "case01.translation.json")
        (self.root / "case01.lean").write_text("changed", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "input hash mismatch"):
            load_manifest(self.manifest_path)

    def test_nonfinite_usage_and_duplicate_truth_rejected(self):
        self.records[0]["usage"]["cost_usd"] = float("nan")
        self.truths.append(self.truths[1].copy())
        result = self.run_score()
        self.assertEqual(result["groups"], {})
        self.assertTrue(any("cost_usd" in item["detail"] for item in result["issues"]))
        self.assertTrue(any("duplicate adjudications" in item["detail"] for item in result["issues"]))

    def test_unknown_cost_propagates_without_becoming_zero(self):
        self.records[0]["usage"]["cost_usd"] = None
        sealed_path = self.prepared / "case01" / "translation.sealed.json"
        translation = read_json(sealed_path)
        translation["usage"]["cost_usd"] = None
        self.write(sealed_path, translation)
        request_path = self.prepared / "case01" / "reverse_translation.request.json"
        request = read_json(request_path)
        request["translation_sha256"] = digest(translation)
        self.write(request_path, request)
        self.records[1]["request_sha256"] = digest(request)
        result = self.run_score()
        self.assertEqual(result["qa_status"], "valid")
        for arm in ("ordinary", "reverse_translation"):
            self.assertIsNone(result["paired_process"]["arms"][arm]["usage"]["cost_usd"])
        self.assertIsNone(result["groups"]["synthetic_test_only"]["cost_usd_difference"])
        self.assertEqual(result["paired_process"]["same_verdict"], 2)


if __name__ == "__main__":
    unittest.main()
