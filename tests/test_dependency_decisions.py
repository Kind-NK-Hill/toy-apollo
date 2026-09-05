import json
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.core.settings import Settings  # noqa: E402
from formalization_engine.dependency_decisions import (  # noqa: E402
    DependencyDecision,
    load_dependency_decisions,
    record_dependency_decision,
)


def make_settings(root: Path) -> Settings:
    return Settings(
        runtime_root=root,
        artifact_root=root,
        plans_dir=root / "plans",
        reports_dir=root / "reports",
        formalized_chapters_dir=root / "formalized_chapters",
        output_lean_files_dir=root / "output_lean_files",
        phase2_prompt_packs_dir=root / "phase2_prompt_packs",
        phase2_softdep_packs_dir=root / "phase2_softdep_packs",
        error_logs_dir=root / "error_logs",
        canonical_lean_dir=root / "ProbabilityTheory",
        canonical_manifest_required=False,
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
        dependency_decisions_dir=root / "dependency_decisions",
    )


class DependencyDecisionTests(unittest.TestCase):
    def test_record_is_jsonl_and_idempotent(self):
        root = REPO_ROOT / "tests" / "_tmp_dependency_decisions"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            decision = DependencyDecision(
                task_id="thm_9_1",
                dep_id="thm_7_12",
                kind="hard",
                phase="phase1_apply",
                criterion="explicit_text_reference",
                evidence="By Theorem 7.12",
                source_plan="chapter9-moments-mgf",
                source_file="plans/chapter9-moments-mgf_plan.json",
            )

            record_dependency_decision(settings, decision)
            record_dependency_decision(settings, decision)

            decision_file = settings.dependency_decisions_dir / "thm_9_1.jsonl"
            lines = decision_file.read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(lines), 1)
            payload = json.loads(lines[0])
            self.assertEqual(payload["decision_id"], "thm_9_1|thm_7_12|hard|phase1_apply|explicit_text_reference")
            self.assertEqual(payload["schema_version"], 1)
            self.assertIn("recorded_at", payload)
            self.assertEqual(payload["evidence"], "By Theorem 7.12")

            loaded = load_dependency_decisions(settings, "thm_9_1")
            self.assertEqual(len(loaded), 1)
            self.assertEqual(loaded[0]["dep_id"], "thm_7_12")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_records_translation_and_proof_debt_support_decisions(self):
        root = REPO_ROOT / "tests" / "_tmp_dependency_decisions_translation_names"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)

            translation = DependencyDecision(
                task_id="thm_10_8",
                dep_id="def_10_4",
                kind="translation",
                phase="phase2_pack",
                criterion="interface_translation",
                evidence="Connects textbook convergence-in-distribution notation to the exported Lean interface.",
            )
            proof_debt = DependencyDecision(
                task_id="thm_10_8",
                dep_id="skorokhod_quantile_support",
                kind="proof_debt_support",
                phase="phase2_pack",
                criterion="proof_debt_support",
                evidence="Explicit support assumption for the generalized quantile construction.",
            )

            record_dependency_decision(settings, translation)
            record_dependency_decision(settings, proof_debt)

            loaded = load_dependency_decisions(settings, "thm_10_8")
            self.assertEqual([item["kind"] for item in loaded], ["translation", "proof_debt_support"])
            self.assertEqual([item["criterion"] for item in loaded], ["interface_translation", "proof_debt_support"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_invalid_kind_and_criterion_are_rejected(self):
        root = REPO_ROOT / "tests" / "_tmp_dependency_decisions_invalid"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            with self.assertRaises(ValueError):
                record_dependency_decision(
                    settings,
                    DependencyDecision(
                        task_id="thm_9_1",
                        dep_id="thm_7_12",
                        kind="optional",
                        phase="phase1_apply",
                        criterion="explicit_text_reference",
                    ),
                )
            with self.assertRaises(ValueError):
                record_dependency_decision(
                    settings,
                    DependencyDecision(
                        task_id="thm_9_1",
                        dep_id="thm_7_12",
                        kind="hard",
                        phase="phase1_apply",
                        criterion="nearby_text",
                    ),
                )
            with self.assertRaises(ValueError):
                record_dependency_decision(
                    settings,
                    DependencyDecision(
                        task_id="thm_9_1",
                        dep_id="thm_7_12",
                        kind="bridge",
                        phase="phase1_apply",
                        criterion="interface_translation",
                    ),
                )
            with self.assertRaises(ValueError):
                record_dependency_decision(
                    settings,
                    DependencyDecision(
                        task_id="thm_9_1",
                        dep_id="thm_7_12",
                        kind="translation",
                        phase="phase1_apply",
                        criterion="interface_bridge",
                    ),
                )
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
