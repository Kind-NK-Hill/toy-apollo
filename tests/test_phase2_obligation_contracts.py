import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.validate_phase2_obligation_contracts import (  # noqa: E402
    main,
    validate_obligation_contracts,
)


def _base_obligation(**overrides):
    obligation = {
        "id": "source_step",
        "kind": "source_step",
        "status": "proved",
        "review_status": "accepted",
        "blocking": True,
        "lean_landing": "real_landing",
        "expected_theorem_signature": "theorem real_landing : True",
        "landing_kind": "theorem",
        "proof_contract_status": "verified",
        "signature_match": "passed",
        "body_reassumption_check": "passed",
        "public_premise_check": "passed",
    }
    obligation.update(overrides)
    return obligation


def _write_task(root, task_id="thm_test", lean_text=None, obligation=None):
    output = root / "ProbabilityTheory"
    pack = root / "phase2_prompt_packs" / task_id
    output.mkdir(parents=True, exist_ok=True)
    pack.mkdir(parents=True, exist_ok=True)
    if lean_text is None:
        lean_text = "theorem real_landing : True := by\n  exact True.intro\n"
    (output / f"{task_id}.lean").write_text(lean_text, encoding="utf-8")
    payload = {
        "schema_version": "phase2.proof_obligations.v1",
        "task_id": task_id,
        "obligations": [obligation or _base_obligation()],
    }
    (pack / "proof_obligations.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return pack / "proof_obligations.json"


def _write_textbook_selection(root, task_id):
    path = root / "docs" / "phase2"
    path.mkdir(parents=True, exist_ok=True)
    (path / "textbook_complete_targets.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "selected_textbook_targets": [
                    {"task_id": task_id, "target_class": "textbook_proof_completed"}
                ],
                "decision_records": [
                    {
                        "task_id": task_id,
                        "target_class": "textbook_proof_completed",
                        "decision_status": "accepted_for_textbook_complete",
                    }
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def _categories(findings):
    return {finding["category"] for finding in findings}


class Phase2ObligationContractValidatorTests(unittest.TestCase):
    def test_proved_obligation_requires_expected_signature(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(root, obligation=_base_obligation(expected_theorem_signature=""))

            findings = validate_obligation_contracts(root)

            self.assertIn("proved_missing_expected_signature", _categories(findings))

    def test_proved_obligation_rejects_field_projection_landing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(
                root,
                lean_text="""
structure SomeSourceSpine where
  some_field : True
""",
                obligation=_base_obligation(lean_landing="SomeSourceSpine.some_field"),
            )

            findings = validate_obligation_contracts(root)

            self.assertIn("proved_field_projection_landing", _categories(findings))

    def test_proved_obligation_rejects_private_axiom_landing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(
                root,
                lean_text="private axiom private_gap : True\n",
                obligation=_base_obligation(lean_landing="private_gap"),
            )

            findings = validate_obligation_contracts(root)

            self.assertIn("proved_forbidden_landing_kind", _categories(findings))

    def test_proved_obligation_rejects_support_constructor_landing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(
                root,
                obligation=_base_obligation(
                    lean_landing="build_support",
                    landing_kind="support_constructor",
                ),
            )

            findings = validate_obligation_contracts(root)

            categories = _categories(findings)
            self.assertIn("proved_forbidden_landing_kind", categories)
            self.assertIn("constructor_return_needs_review", categories)

    def test_proved_obligation_rejects_adapter_for_textbook_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_textbook"
            _write_task(
                root,
                task_id=task_id,
                obligation=_base_obligation(landing_kind="adapter"),
            )
            _write_textbook_selection(root, task_id)

            findings = validate_obligation_contracts(root)

            self.assertIn("textbook_target_adapter_landing", _categories(findings))

    def test_verified_theorem_landing_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(root)

            findings = validate_obligation_contracts(root)

            self.assertEqual(findings, [])

    def test_proved_obligation_missing_local_landing_is_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(
                root,
                lean_text="theorem other_landing : True := by\n  exact True.intro\n",
                obligation=_base_obligation(lean_landing="missing_landing"),
            )

            findings = validate_obligation_contracts(root)

            matching = [
                finding for finding in findings if finding["category"] == "landing_not_found_in_output"
            ]
            self.assertEqual(len(matching), 1)
            self.assertEqual(matching[0]["severity"], "error")

    def test_write_report_creates_markdown_and_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_task(root, obligation=_base_obligation(expected_theorem_signature=""))

            exit_code = main(["--root", str(root), "--write-report"])

            report_base = root / "docs" / "phase2" / "reports" / "obligation_contract_audit"
            report_json = json.loads(report_base.with_suffix(".json").read_text(encoding="utf-8"))
            report_md = report_base.with_suffix(".md").read_text(encoding="utf-8")
            self.assertEqual(exit_code, 0)
            self.assertIn("findings", report_json)
            self.assertIn("proved_missing_expected_signature", report_md)
            self.assertIn("Contract audit result", report_md)

    def test_legacy_textbook_selection_path_is_fallback_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_textbook"
            _write_task(
                root,
                task_id=task_id,
                obligation=_base_obligation(landing_kind="adapter"),
            )
            legacy = root / "docs" / "modification_0525_steps"
            legacy.mkdir(parents=True, exist_ok=True)
            (legacy / "phase2_step5_textbook_complete_target_selection.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "selected_step6_targets": [
                            {"task_id": task_id, "target_class": "textbook_proof_completed"}
                        ],
                    }
                ),
                encoding="utf-8",
            )

            findings = validate_obligation_contracts(root)

            self.assertIn("textbook_target_adapter_landing", _categories(findings))


if __name__ == "__main__":
    unittest.main()
