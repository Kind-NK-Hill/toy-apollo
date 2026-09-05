import asyncio
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_pack_generation import (  # noqa: E402
    build_check_prompt_pack_candidate,
    write_codex_review_pack,
    write_existing_output_review_pack,
    write_existing_output_review_queue,
    write_prompt_pack,
)
from formalization_engine.phase2_prompt_pack import (  # noqa: E402
    _build_build_result_payload,
    _run_staged_official_build,
    resolve_phase2_task,
    validate_candidate_hard_checks,
)
from formalization_engine.phase2_pack_shared.io import (  # noqa: E402
    fs_path,
    make_dirs,
    path_exists,
    read_file_safely,
    write_text,
)
from formalization_engine.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from formalization_engine.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
)
from formalization_engine.phase2_task_status import PROOF_BEARING_PASS_PREFIXES  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2PackGenerationTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_resolve_phase2_task_fills_only_missing_plan_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True)
            settings = self._make_settings(root, plans_dir)
            (plans_dir / "chapter5_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "thm_5_missing_deps",
                            "type": "Theorem_Statement",
                            "title": "Missing dependencies",
                            "content": "Plan content A.",
                            "source_plan": "chapter5",
                            "dependencies": ["def_5_1"],
                        },
                        {
                            "block_id": "thm_5_explicit_empty",
                            "type": "Theorem_Statement",
                            "title": "Explicit empty dependencies",
                            "content": "Plan content B.",
                            "source_plan": "chapter5",
                            "dependencies": ["def_5_1"],
                        },
                    ]
                ),
                encoding="utf-8",
            )
            ledger = LedgerManager(str(root / "project_ledger.json"))
            ledger.ledger["tasks"] = {
                "thm_5_missing_deps": {
                    "block_id": "thm_5_missing_deps",
                    "type": "Theorem_Statement",
                    "content": "Imported content A.",
                },
                "thm_5_explicit_empty": {
                    "block_id": "thm_5_explicit_empty",
                    "type": "Theorem_Statement",
                    "content": "Imported content B.",
                    "dependencies": [],
                },
            }

            missing = resolve_phase2_task("thm_5_missing_deps", ledger, settings)
            explicit_empty = resolve_phase2_task("thm_5_explicit_empty", ledger, settings)

        self.assertEqual(missing["dependencies"], ["def_5_1"])
        self.assertEqual(explicit_empty["dependencies"], [])

    def test_staged_official_build_uses_short_backup_names_for_long_child_obligation_paths(self):
        root = Path(tempfile.gettempdir()) / "formalization_engine_staged_long_backup"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            settings = self._make_settings(root, plans_dir)
            child_id = (
                "obl_obl_obl_prob_14_12_obligation_5_obligation_5_limit_truncation_tail_"
                "sequence_ui_supplies_subsequence_tail_bound"
            )
            owner_id = "obl_obl_prob_14_12_obligation_5_obligation_5_limit_truncation_tail"
            pack_dir = settings.phase2_prompt_packs_dir / child_id
            pack_dir.mkdir(parents=True, exist_ok=True)
            owner_pack_dir = settings.phase2_prompt_packs_dir / owner_id
            owner_pack_dir.mkdir(parents=True, exist_ok=True)
            output_path = settings.canonical_lean_dir / f"{owner_id}.lean"
            output_path.parent.mkdir(parents=True, exist_ok=True)
            old_code = f"import Mathlib\n\ntheorem {owner_id} : True := by\n  trivial\n"
            new_code = old_code.replace("trivial", "trivial")
            output_path.write_text(old_code, encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = _run_staged_official_build(
                    child_id,
                    "chapter14-problems",
                    settings,
                    pack_dir,
                    new_code,
                    attempt=2,
                    mode="review-apply",
                    restore_on_success=False,
                    output_owner_task_id=owner_id,
                )

            self.assertTrue(success, detail)
            self.assertEqual(output_path.read_text(encoding="utf-8"), new_code)
            self.assertFalse((pack_dir / ".staging" / "review-apply-2").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_staged_official_build_handles_long_owner_pack_staging_path(self):
        root = Path(tempfile.gettempdir()) / "formalization_engine_staged_long_owner_pack"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            make_dirs(plans_dir, exist_ok=True)
            settings = self._make_settings(root, plans_dir)
            owner_id = (
                "obl_obl_obl_obl_obl_prob_14_8_obligation_4_obligation_4_analytic_continuation_"
                "vitali_montel_convergence_general_vitali_montel_foundation_montel_extract"
            )
            initial_staging_dir = settings.phase2_prompt_packs_dir / owner_id / ".staging" / "review-apply-1"
            # /tmp is shorter than the Windows user temp directory. Ensure the
            # same long-path condition on either host without weakening it.
            owner_id += "x" * max(0, 261 - len(str(initial_staging_dir)))
            child_id = f"{owner_id}_compact_stage_sequence_data_5f911e86badd"
            pack_dir = settings.phase2_prompt_packs_dir / child_id
            owner_pack_dir = settings.phase2_prompt_packs_dir / owner_id
            make_dirs(pack_dir, exist_ok=True)
            make_dirs(owner_pack_dir, exist_ok=True)
            output_path = settings.canonical_lean_dir / f"{owner_id}.lean"
            make_dirs(output_path.parent, exist_ok=True)
            old_code = f"import Mathlib\n\ntheorem {owner_id} : True := by\n  trivial\n"
            new_code = old_code + "\n-- landed through long owner staging path\n"
            write_text(output_path, old_code)

            staging_dir = owner_pack_dir / ".staging" / "review-apply-1"
            self.assertGreater(len(str(staging_dir)), 260)

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = _run_staged_official_build(
                    child_id,
                    "chapter14-problems",
                    settings,
                    pack_dir,
                    new_code,
                    attempt=1,
                    mode="review-apply",
                    restore_on_success=False,
                    output_owner_task_id=owner_id,
                )

            self.assertTrue(success, detail)
            self.assertEqual(read_file_safely(output_path), new_code)
            self.assertFalse(path_exists(staging_dir))
        finally:
            shutil.rmtree(fs_path(root), ignore_errors=True)

    def test_staged_official_build_recovers_empty_staging_dir_without_manifest(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_staged_empty_recovery"
        try:
            self._clean_root(root)
            task_id = "thm_4_staging_empty_recovery"
            _ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)
            stale_staging_dir = pack_dir / ".staging" / "review-apply-1"
            stale_staging_dir.mkdir(parents=True, exist_ok=True)
            candidate_code = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(candidate_code, encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = _run_staged_official_build(
                    task_id,
                    "08_chap4_measurable_functions",
                    settings,
                    pack_dir,
                    candidate_code,
                    attempt=1,
                    mode="review-apply",
                    restore_on_success=False,
                )

            self.assertTrue(success, detail)
            self.assertFalse(stale_staging_dir.exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def _setup_proof_debt_dependency_task(
        self,
        root: Path,
        *,
        legacy_completed_debt: bool = False,
        downstream_type: str = "Problem",
    ):
        self._clean_root(root)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        dep_id = "thm_10_8"
        task_id = "prob_10_10"
        (plans_dir / "chapter10-problems_plan.json").write_text(
            json.dumps(
                [
                    {
                        "block_id": dep_id,
                        "type": "Theorem",
                        "title": "Debt-bearing upstream",
                        "content": "Upstream theorem with accepted proof debt.",
                        "dependencies": [],
                    },
                    {
                        "block_id": task_id,
                        "type": downstream_type,
                        "title": "Downstream problem",
                        "content": "Downstream task that depends on the upstream theorem.",
                        "dependencies": [dep_id],
                    },
                ],
                indent=2,
            ),
            encoding="utf-8",
        )
        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        for block_id, dependencies in ((dep_id, []), (task_id, [dep_id])):
            ledger.add_or_update_task(
                {
                    "block_id": block_id,
                    "type": "Theorem" if block_id == dep_id else downstream_type,
                    "title": block_id,
                    "content": "test task",
                    "source_plan": "chapter10-problems",
                    "dependencies": dependencies,
                }
            )
        if legacy_completed_debt:
            ledger.update_status(dep_id, TaskStatus.COMPLETED)
        else:
            ledger.update_status(dep_id, TaskStatus.COMPLETED_WITH_PROOF_DEBT)
        ledger.update_runtime_metadata(
            dep_id,
            proof_obligation_summary={"status_counts": {"proved": 4, "accepted_as_proof_debt": 1}},
        )
        settings = self._make_settings(root, plans_dir)
        return ledger, settings, task_id, dep_id

    def _seed_build_failures(self, pack_dir: Path, task_id: str, count: int) -> None:
        (pack_dir / "attempt_history.json").write_text(
            json.dumps(
                {
                    "task_id": task_id,
                    "attempts": [
                        {
                            "attempt": index + 1,
                            "candidate_file": str(pack_dir / f"candidate_seed_{index + 1}.lean"),
                            "candidate_hash": f"build-fail-{index + 1}",
                            "success": False,
                            "primary_failure_kind": "repl_failed",
                            "stage": "build",
                            "disposition": "build_check_temp_build_failed",
                        }
                        for index in range(count)
                    ],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def test_write_prompt_pack_creates_intent_contract_file(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_intent_contract"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            (plans_dir / "14_chap5_discrete_continuous_type_plan.json").write_text(
                """
[
  {
    "block_id": "ex_5_2_2",
    "type": "Example_Proof",
    "title": "Example 5.2.2",
    "content": "The converse of Theorem 5.2 is false. X and Y are not independent. Their joint density is 1/4(1+xy), but X^2 and Y^2 are independent.",
    "dependencies": []
  }
]
                """.strip(),
                encoding="utf-8",
            )
            from formalization_engine.core import LedgerManager

            ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
            ledger.add_or_update_task(
                {
                    "block_id": "ex_5_2_2",
                    "type": "Example_Proof",
                    "title": "Example 5.2.2",
                    "content": "The converse of Theorem 5.2 is false. X and Y are not independent. Their joint density is 1/4(1+xy), but X^2 and Y^2 are independent.",
                    "source_plan": "14_chap5_discrete_continuous_type",
                    "dependencies": [],
                }
            )
            settings = self._make_settings(root, plans_dir)
            pack_dir = write_prompt_pack("ex_5_2_2", ledger, settings)
            contract = json.loads((pack_dir / "intent_contract.json").read_text(encoding="utf-8"))
            self.assertEqual(contract["task_role"], "counterexample_example")
            self.assertEqual(contract["coverage_mode"], "strict_source_alignment")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_generates_handoff_artifacts_without_reviewer_config(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_codex_review_pack"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_codex_review_pack"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            with patch.dict(os.environ, {"FORMALIZATION_ENGINE_PHASE2_REVIEWER_ARGV_JSON": ""}, clear=False), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "unexpected")),
            ) as repl_mock, patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "unexpected")),
            ) as build_mock:
                success, detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertEqual(repl_mock.await_count, 0)
            self.assertEqual(build_mock.await_count, 0)
            self.assertTrue((pack_dir / "candidate_v1.lean").exists())
            self.assertTrue((pack_dir / "semantic_review_input_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_prompt_v1.md").exists())
            self.assertTrue((pack_dir / "semantic_review_result_template_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request.json").exists())
            self.assertTrue((pack_dir / "semantic_review_input.json").exists())
            self.assertTrue((pack_dir / "semantic_review_prompt.md").exists())
            self.assertFalse((pack_dir / "proof_obligations.json").exists())
            self.assertFalse(output_path.exists())

            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(review_input["mode"], "review-pack")
            self.assertEqual(review_input["prompt_version"], SEMANTIC_REVIEW_PROMPT_VERSION)
            self.assertEqual(review_input["rubric_version"], SEMANTIC_REVIEW_RUBRIC_VERSION)
            for retired_field in (
                "proof_obligations",
                "proof_obligations_file",
                "proof_obligation_summary",
                "proof_obligations_evidence",
            ):
                self.assertNotIn(retired_field, review_input["review_basis"])
            route_gate = review_input["review_basis"]["route_inspection_gate"]
            self.assertEqual(route_gate["authority"], "review_context_only")
            self.assertEqual(
                route_gate["required_fields"],
                [
                    "source_route",
                    "expected_answer_or_statement",
                    "local_mathlib_search",
                    "public_interface_check",
                    "support_or_reassembly_decision",
                    "stop_go_verdict",
                ],
            )
            self.assertIn("semantic_fail_public_premise", route_gate["trigger_conditions"])

            review_template = json.loads((pack_dir / "semantic_review_result_template_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(review_template["proof_class"], "")
            self.assertEqual(review_template["completion_class"], "")
            self.assertEqual(
                review_template["route_inspection"],
                {
                    "status": "unclear",
                    "source_route": "",
                    "expected_answer_or_statement": "",
                    "local_mathlib_search": "",
                    "public_interface_check": "",
                    "support_or_reassembly_decision": "",
                    "stop_go_verdict": "unclear",
                    "notes": "",
                },
            )
            schema_hints = review_template["reviewer_schema_hints"]
            self.assertEqual(
                schema_hints["completion_class_contract"],
                {
                    "required_fields": ["proof_class", "completion_class"],
                    "must_be_non_empty": True,
                    "authority": "reviewer_classification_then_official_task_status_projection",
                    "task_role": "proof_bearing",
                    "clean_pass_prefixes": list(PROOF_BEARING_PASS_PREFIXES),
                    "allowed_exception_classes": [],
                    "projection_rule": (
                        "For clean pass, both class fields must use a clean pass prefix allowed for the projected task role; "
                        "task-specific allowed exceptions are non-clean."
                    ),
                },
            )
            self.assertEqual(schema_hints["section_status_values"], ["covered", "partial", "missing", "violated", "unclear"])
            self.assertEqual(
                schema_hints["route_inspection_fields"],
                [
                    "source_route",
                    "expected_answer_or_statement",
                    "local_mathlib_search",
                    "public_interface_check",
                    "support_or_reassembly_decision",
                    "stop_go_verdict",
                ],
            )
            self.assertNotIn("obligation_item_contract_fields", schema_hints)
            self.assertIn("source_step_entry_shape", schema_hints)
            self.assertIn("source_step", schema_hints["source_step_entry_shape"])
            self.assertIn("lean_landing", schema_hints["source_step_entry_shape"])
            self.assertNotIn("obligation_review", review_template)
            self.assertEqual(review_template["spine_alignment"]["source_steps_checked"], [])
            self.assertEqual(review_template["spine_alignment"]["missing_source_steps"], [])
            self.assertEqual(
                schema_hints["downstream_consumer_entry_shape"],
                {
                    "block_id": "<direct downstream block_id>",
                    "status": "covered | not_applicable | blocked",
                    "evidence": "<why this exported interface is adequate or not applicable>",
                },
            )
            self.assertEqual(schema_hints["forbidden_weakening_status_values"], ["not_present", "present", "not_applicable"])

            review_prompt = (pack_dir / "semantic_review_prompt_v1.md").read_text(encoding="utf-8")
            self.assertIn("Status enum fields", review_prompt)
            self.assertIn("textbook-first, bridge-then-Mathlib", review_prompt)
            self.assertIn("A reviewed equivalence bridge may use Mathlib", review_prompt)
            self.assertIn("adapter-only shortcut", review_prompt)
            self.assertIn("## Task-Level Pass Class Contract", review_prompt)
            self.assertIn("Projected task role: `proof_bearing`", review_prompt)
            self.assertIn("source_route_proof_completed", review_prompt)
            self.assertIn("both `proof_class` and `completion_class`", review_prompt)
            self.assertIn("spine_alignment.source_steps_checked", review_prompt)
            self.assertIn("route_inspection", review_prompt)
            self.assertIn("source_route", review_prompt)
            self.assertIn("public_interface_check", review_prompt)
            self.assertIn("downstream_adequacy.consumers_checked entries must be objects", review_prompt)
            self.assertIn("forbidden_weakenings entries use status not_present/present/not_applicable", review_prompt)

            review_context = (pack_dir / "semantic_review_context_v1.md").read_text(encoding="utf-8")
            self.assertNotIn("obligation_review", review_prompt)
            self.assertNotIn("proof_obligations", review_prompt)
            self.assertNotIn("Proof obligation tracking", review_context)
            self.assertNotIn("## Proof Obligation Ledger", review_context)
            self.assertNotIn("proof_obligations.json", review_context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_writes_template_for_long_nested_obligation_path(self):
        root = Path(tempfile.gettempdir()) / "formalization_engine_pack_generation_long_review_path"
        try:
            self._clean_root(root)
            task_id = (
                "obl_obl_obl_obl_obl_prob_14_1_obligation_1_obligation_1_"
                "whitecountlaws_atom_mass_constant_mass_on_k_white_paths_"
                "exchangeability_mass_to_rising_factorial_mass"
            )
            ledger, settings, pack_dir, _output_path = self._setup_trivial_phase2_task(root, task_id)

            template_path = pack_dir / "semantic_review_result_template_v1.json"
            self.assertGreater(len(str(template_path)), 260)
            write_text(
                pack_dir / "math_proof_skeleton_v1.md",
                "# Math Proof Skeleton\n\nFixture route is approved so this test can exercise long review paths.",
            )
            write_text(
                pack_dir / "math_review_result_v1.json",
                json.dumps({"verdict": "go", "rounds": [{"round": 1}, {"round": 2}, {"round": 3}]}),
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            success, detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertTrue(path_exists(template_path))
            self.assertTrue(path_exists(pack_dir / "semantic_review_result_template.json"))
            self.assertTrue(path_exists(pack_dir / "semantic_review_request_v1.json"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_includes_required_review_evidence_manifest(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_review_evidence_manifest"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_review_evidence_manifest"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            classification_path = root / "docs" / "phase2_completion_classification.json"
            classification_path.parent.mkdir(parents=True, exist_ok=True)
            classification_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "tasks": [
                            {
                                "task_id": task_id,
                                "primary_class": "open_math_debt",
                                "classification_source": "test fixture",
                            }
                        ],
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            audit_path = pack_dir / "verify_result_v99.json"
            audit_path.write_text(
                json.dumps(
                    {
                        "mode": "audit",
                        "disposition": "audit_semantic_fail",
                        "diagnostics": [{"severity": "error", "message": "fixture audit finding"}],
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            success, detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)

            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            basis = review_input["review_basis"]
            self.assertEqual(
                basis["required_evidence_classes"],
                [
                    "source_tex",
                    "lean_subject",
                    "audit",
                    "classification",
                    "dependency_status",
                    "downstream",
                    "ledger_status",
                    "hashes",
                ],
            )
            self.assertNotIn("proof_obligations_evidence", basis)
            self.assertNotIn("proof_obligations", basis)
            self.assertNotIn("proof_obligations_file", basis)
            self.assertNotIn("proof_obligation_summary", basis)
            self.assertEqual(basis["audit_evidence"]["latest_audit_result_file"], str(audit_path))
            self.assertEqual(basis["classification_history"]["entries"][0]["primary_class"], "open_math_debt")
            self.assertEqual(basis["ledger_status"]["task_status"], "PACKED")
            self.assertIn("build_result_hash", basis["hash_evidence"])
            self.assertEqual(basis["hash_evidence"]["review_subject_hash"], review_input["candidate"]["hash"])
            self.assertIn("dependency_status", basis)
            self.assertIn("downstream_evidence", basis)
            self.assertIn("subject_imports", basis)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_rejects_draft_superseded_by_official_output(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_stale_draft_official"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_stale_draft_official"
            stale_draft = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_draft,
            )
            os.utime(pack_dir / "draft.lean", (1000, 1000))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("Stale build-check source target", detail)
            self.assertIn("review-now --review-subject existing", detail)
            self.assertFalse((pack_dir / "candidate_v1.lean").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_requires_math_review_go_for_risky_problem(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_math_gate"
        try:
            self._clean_root(root)
            task_id = "prob_14_1"
            draft = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=draft,
            )
            ledger.update_runtime_metadata(
                task_id,
                phase2_status="fail",
                phase2_status_reason="semantic_fail_public_premise: moved white-count law into setup",
                latest_semantic_fail_triage_category="public_premise",
            )

            success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("Math Review Gate", detail)
            self.assertIn("math_proof_skeleton_vN.md", detail)
            self.assertFalse((pack_dir / "candidate_v1.lean").exists())
            metadata = json.loads((pack_dir / "metadata.json").read_text(encoding="utf-8"))
            self.assertTrue(metadata["math_review_gate_required"])
            self.assertEqual(metadata["math_review_gate_status"], "missing_skeleton")
            self.assertEqual(
                ledger.ledger["tasks"][task_id]["math_review_gate_status"],
                "missing_skeleton",
            )
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_ignores_newer_divergent_legacy_shadow(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_multiple_official_targets"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_multiple_official_targets"
            stale_draft = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired secondary official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_draft,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(stale_draft, encoding="utf-8")
            os.utime(output_path, (1000, 1000))
            os.utime(pack_dir / "draft.lean", (1000, 1000))
            secondary_output = settings.output_lean_files_dir / "08_chap4_measurable_functions" / f"{task_id}.lean"
            secondary_output.parent.mkdir(parents=True, exist_ok=True)
            secondary_output.write_text(repaired_output, encoding="utf-8")
            os.utime(secondary_output, (2000, 2000))

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new_callable=AsyncMock,
                return_value=(True, "repl ok"),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new_callable=AsyncMock,
                return_value=(True, "temp build ok"),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertNotIn(str(secondary_output), detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_complex_pack_does_not_create_or_reference_proof_obligations_file(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_complex_obligations"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            task_id = "thm_10_8"
            complex_content = "Proof. Construct the representation, split the cases, pass to the limit, and show convergence. " * 40
            (plans_dir / "chapter10-problems_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": task_id,
                            "type": "Theorem_with_Proof",
                            "title": "Complex proof",
                            "content": complex_content,
                            "dependencies": ["def_10_4", "prob_3_5"],
                        }
                    ],
                    indent=2,
                ),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
            ledger.add_or_update_task(
                {
                    "block_id": task_id,
                    "type": "Theorem_with_Proof",
                    "title": "Complex proof",
                    "content": complex_content,
                    "source_plan": "chapter10-problems",
                    "dependencies": ["def_10_4", "prob_3_5"],
                }
            )
            settings = self._make_settings(root, plans_dir)

            pack_dir = write_prompt_pack(task_id, ledger, settings)

            obligations_path = pack_dir / "proof_obligations.json"
            self.assertFalse(obligations_path.exists())
            metadata = json.loads((pack_dir / "metadata.json").read_text(encoding="utf-8"))
            self.assertNotIn("proof_obligations_file", metadata)
            self.assertNotIn("proof_obligation_summary", metadata)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_prompt_pack_rejects_hard_dependency_with_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_proof_debt_dep"
        try:
            ledger, settings, task_id, dep_id = self._setup_proof_debt_dependency_task(root)

            with self.assertRaisesRegex(ValueError, f"{dep_id}.*proof debt"):
                write_prompt_pack(task_id, ledger, settings)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_prompt_pack_allows_explicit_allowed_exception_dependency(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_allowed_exception_dep"
        try:
            ledger, settings, task_id, dep_id = self._setup_proof_debt_dependency_task(root, downstream_type="Theorem")
            ledger.update_runtime_metadata(
                dep_id,
                phase2_status="allowed_exception",
                phase2_status_evidence_type="explicit_allowed_exception",
                phase2_task_status="allowed_exception",
                phase2_task_status_evidence_type="explicit_allowed_exception",
            )

            pack_dir = write_prompt_pack(task_id, ledger, settings)

            self.assertTrue(pack_dir.exists())
            self.assertTrue((pack_dir / "metadata.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_prompt_pack_ignores_legacy_proof_debt_summary_on_completed_dependency(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_legacy_proof_debt_dep"
        try:
            ledger, settings, task_id, dep_id = self._setup_proof_debt_dependency_task(
                root,
                legacy_completed_debt=True,
                downstream_type="Theorem",
            )
            pack_dir = write_prompt_pack(task_id, ledger, settings)

            self.assertTrue(pack_dir.exists())
            self.assertEqual(ledger.ledger["tasks"][dep_id]["status"], TaskStatus.COMPLETED.value)
            self.assertTrue(ledger.ledger["tasks"][dep_id]["proof_obligation_summary"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_reflects_pack_soft_imports(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_pack_soft_import"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_pack_soft_import"
            dep_id = "thm_4_pack_generation_soft_dep"
            stale_dep_id = "thm_4_pack_generation_stale_soft_dep"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)

            for local_dep_id in [dep_id, stale_dep_id]:
                dep_code = f"import Mathlib\n\ntheorem {local_dep_id} : True := by\n  trivial\n"
                dep_path = settings.canonical_lean_dir / f"{local_dep_id}.lean"
                dep_path.parent.mkdir(parents=True, exist_ok=True)
                dep_path.write_text(dep_code, encoding="utf-8")
                ledger.add_or_update_task(
                    {
                        "block_id": local_dep_id,
                        "type": "Theorem",
                        "title": "Soft dependency",
                        "content": "A previously completed local output.",
                        "source_plan": "08_chap4_measurable_functions",
                        "dependencies": [],
                    }
                )
                ledger.register_success(local_dep_id, dep_code, ledger._hash_text(dep_code))
            ledger.update_candidate_soft_imports(task_id, [stale_dep_id])

            task_json_path = pack_dir / "task.json"
            task_payload = json.loads(task_json_path.read_text(encoding="utf-8"))
            task_payload["soft_imports"] = [dep_id]
            task_payload["final_import_union"] = [dep_id]
            task_json_path.write_text(json.dumps(task_payload, indent=2, ensure_ascii=False), encoding="utf-8")
            (pack_dir / "draft.lean").write_text(
                f"import Mathlib\nimport ProbabilityTheory.{dep_id}\n\ntheorem {task_id} : True := by\n  exact {dep_id}\n",
                encoding="utf-8",
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            with patch.dict(os.environ, {"FORMALIZATION_ENGINE_PHASE2_REVIEWER_ARGV_JSON": ""}, clear=False):
                review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))

            self.assertTrue(review_success, review_detail)
            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertIn(dep_id, review_input["task"]["soft_imports"])
            self.assertIn(dep_id, review_input["review_basis"]["task"]["soft_imports"])
            self.assertNotIn(stale_dep_id, review_input["task"]["soft_imports"])
            self.assertNotIn(stale_dep_id, review_input["review_basis"]["task"]["soft_imports"])
            self.assertIn(f"import ProbabilityTheory.{dep_id}", review_input["imports"])
            self.assertNotIn(f"import ProbabilityTheory.{stale_dep_id}", review_input["imports"])
            self.assertIn(dep_id, {entry["task_id"] for entry in review_input["dependencies"]})
            self.assertNotIn(stale_dep_id, {entry["task_id"] for entry in review_input["dependencies"]})
            review_context = (pack_dir / "semantic_review_context_v1.md").read_text(encoding="utf-8")
            self.assertIn(dep_id, review_context)
            self.assertNotIn(stale_dep_id, review_context)
            self.assertIn("Soft imports", review_context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_failure_before_15_keeps_task_packed(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_fail_before_15"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_fail_before_15"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "repl failed")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(False, "temp build failed")),
            ):
                success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("repl failed", detail.lower())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "PACKED")
            self.assertEqual(task["pack_candidate_state"], "build_failed")
            self.assertEqual(task["phase2_build_fail_counter"], 1)
            self.assertEqual(task["phase2_review_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_failure_fails_only_after_15_consecutive_build_failures(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_fail_after_15"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_fail_after_15"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._seed_build_failures(pack_dir, task_id, 14)

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "repl failed")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(False, "temp build failed")),
            ):
                success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("repl failed", detail.lower())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "FAILED_LOCAL")
            self.assertEqual(task["phase2_build_fail_counter"], 15)
            self.assertEqual(task["phase2_review_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_successful_build_check_resets_build_failure_counter(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_success_resets_counter"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_success_resets_counter"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._seed_build_failures(pack_dir, task_id, 14)

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)

            self.assertTrue(build_success, build_detail)
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "PACKED")
            self.assertEqual(task["pack_candidate_state"], "build_ready")
            self.assertEqual(task["phase2_build_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_hard_check_allows_auxiliary_output_module_with_task_prefix(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ProbabilityTheory.thm_10_8_quantile_defs

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertTrue(success, detail)
        self.assertEqual(diagnostics, [])

    def test_hard_check_accepts_cordis_mapped_structure_and_abbrev_declarations(self):
        candidate = """
namespace Cordis.Foundations

abbrev EffectContext (State : Type) := State × (State → State)

structure TwistedPair (State : Type) where
  forward : State → State
  inverse : State → State

end Cordis.Foundations
""".strip()
        cases = (
            ("def_1", "TwistedPair"),
            ("def_2", "EffectContext"),
        )

        for task_id, declaration in cases:
            with self.subTest(task_id=task_id):
                success, diagnostics, detail = validate_candidate_hard_checks(
                    {"block_id": task_id, "type": "Definition", "dependencies": []},
                    candidate,
                    target_declaration_names={task_id: [declaration]},
                )

                self.assertTrue(success, detail)
                self.assertEqual(diagnostics, [])

    def test_hard_check_still_rejects_exact_self_import(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ProbabilityTheory.thm_10_8

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertFalse(success)
        self.assertIn("self-imports", detail)
        self.assertEqual(diagnostics[0]["kind"], "self_import")

    def test_hard_check_obligation_task_targets_focused_child_landing(self):
        task = {
            "block_id": "obl_thm_7_8_t7_8_simple_sandwich",
            "type": "Phase2ObligationTask",
            "parent_block_id": "thm_7_8",
            "dependencies": [],
        }
        candidate = """
import Mathlib

theorem obl_thm_7_8_t7_8_simple_sandwich : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertTrue(success, detail)
        self.assertEqual(diagnostics, [])

    def test_hard_check_obligation_task_allows_unprefixed_focused_landing(self):
        task = {
            "block_id": "obl_thm_10_8_quantile_event_measurability",
            "type": "Phase2ObligationTask",
            "parent_block_id": "thm_10_8",
            "dependencies": [],
        }
        candidate = """
import Mathlib

theorem thm_10_8_quantile_event_measurability : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertTrue(success, detail)
        self.assertEqual(diagnostics, [])

    def test_hard_check_still_rejects_undeclared_task_import(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ProbabilityTheory.prob_10_10

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertFalse(success)
        self.assertIn("prob_10_10", detail)
        self.assertEqual(diagnostics[0]["kind"], "undeclared_local_import")

    def test_build_result_classifies_task_prefixed_unknown_identifier_as_missing_local_foundation(self):
        diagnostics = [
            {
                "stage": "repl",
                "kind": "unknown_identifier",
                "message": "Line 129, Col 8: Unknown identifier `prob_11_10_polya_uniformization_from_pointwise`",
                "line": 129,
                "column": 8,
                "blocking_symbols": ["prob_11_10_polya_uniformization_from_pointwise"],
            }
        ]

        payload = _build_build_result_payload(
            task_id="prob_11_10",
            attempt=7,
            candidate_path=Path("candidate_v7.lean"),
            candidate_code="theorem prob_11_10 : True := by\n  exact prob_11_10_polya_uniformization_from_pointwise\n",
            candidate_kind="draft",
            built_at="2026-05-28T00:00:00Z",
            hard_checks_success=True,
            repl_success=False,
            repl_output="unknown identifier",
            temp_build_success=False,
            temp_build_output="unknown identifier",
            final_build_success=False,
            final_build_output="",
            diagnostics=diagnostics,
            disposition="build_check_temp_build_failed",
        )

        self.assertEqual(payload["primary_failure_kind"], "missing_local_foundation_lemma")
        self.assertEqual(payload["diagnostics"][0]["kind"], "missing_local_foundation_lemma")
        self.assertEqual(
            payload["diagnostics"][0]["local_missing_symbols"],
            ["prob_11_10_polya_uniformization_from_pointwise"],
        )

    def test_review_existing_success_generates_official_snapshot_and_review_artifacts(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_review_existing_success"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_review_existing_success"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertTrue((pack_dir / "official_snapshot_v1.lean").exists())
            self.assertTrue((pack_dir / "semantic_review_input_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request_v1.json").exists())
            self.assertTrue((pack_dir / "verify_result_v1.json").exists())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["latest_operation_kind"], "review-existing")
            self.assertTrue(str(task["latest_verify_result_file"]).endswith("verify_result_v1.json"))
            self.assertEqual(task["pack_candidate_state"], "draft")
            self.assertTrue(str(task["current_review_request_file"]).endswith("semantic_review_request_v1.json"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_hard_check_failure_blocks_review_materials(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_review_existing_hard_check"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_review_existing_hard_check"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)

            with patch(
                "formalization_engine.phase2_prompt_pack.validate_candidate_hard_checks",
                return_value=(
                    False,
                    [{"severity": "error", "code": "contains_sorry", "message": "fixture hard-check failure"}],
                    "fixture hard-check failure",
                ),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
            ) as build_mock:
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertEqual(detail, "fixture hard-check failure")
            build_mock.assert_not_called()
            self.assertTrue(output_path.exists())
            self.assertFalse((pack_dir / "official_snapshot_v1.lean").exists())
            self.assertFalse((pack_dir / "semantic_review_input_v1.json").exists())
            compat_result = json.loads((pack_dir / "verify_result_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(compat_result["mode"], "review-existing")
            self.assertEqual(compat_result["disposition"], "review_existing_hard_check_failed")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_problem_preserves_soft_import_confirmation_in_review_artifacts(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_problem_soft_confirmed"
        try:
            self._clean_root(root)
            task_id = "prob_4_pack_generation_problem_soft_confirmed"
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            (plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": task_id,
                            "type": "Problem",
                            "title": "Confirmed soft imports problem",
                            "content": "Problem with an explicitly confirmed empty soft-import selection.",
                            "dependencies": [],
                            "soft_imports": [],
                        }
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
            ledger.add_or_update_task(
                {
                    "block_id": task_id,
                    "type": "Problem",
                    "title": "Confirmed soft imports problem",
                    "content": "Problem with an explicitly confirmed empty soft-import selection.",
                    "source_plan": "12_chap4_problems",
                    "dependencies": [],
                    "soft_imports": [],
                }
            )
            ledger.mark_soft_imports_confirmed(task_id, [])
            settings = self._make_settings(root, plans_dir)
            output_path = settings.canonical_lean_dir / f"{task_id}.lean"
            output_path.parent.mkdir(parents=True, exist_ok=True)
            official_code = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            output_path.write_text(official_code, encoding="utf-8")
            ledger.register_success(task_id, official_code, ledger._hash_text(official_code))

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            confirmed_at = ledger.ledger["tasks"][task_id]["soft_imports_confirmed_at"]
            self.assertTrue(confirmed_at)
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            task_payload = json.loads((pack_dir / "task.json").read_text(encoding="utf-8"))
            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(task_payload["soft_imports_confirmed_at"], confirmed_at)
            self.assertEqual(review_input["task"]["soft_imports_confirmed_at"], confirmed_at)
            self.assertEqual(review_input["review_basis"]["task"]["soft_imports_confirmed_at"], confirmed_at)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_uses_canonical_target_when_shadow_is_newer(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_review_existing_latest_target"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_review_existing_latest_target"
            old_output = f"import Mathlib\n\n-- old official output\ntheorem {task_id} : True := by\n  trivial\n"
            latest_output = f"import Mathlib\n\n-- latest official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            output_path.write_text(old_output, encoding="utf-8")
            os.utime(output_path, (1000, 1000))
            secondary_output = settings.output_lean_files_dir / "08_chap4_measurable_functions" / f"{task_id}.lean"
            secondary_output.parent.mkdir(parents=True, exist_ok=True)
            secondary_output.write_text(latest_output, encoding="utf-8")
            os.utime(secondary_output, (2000, 2000))

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertEqual((pack_dir / "official_snapshot_v1.lean").read_text(encoding="utf-8"), old_output)
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["current_review_subject_kind"], "official_output")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_queue_uses_canonical_target_when_shadow_is_newer(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_queue_latest_target"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_queue_latest_target"
            old_output = f"import Mathlib\n\n-- old official output\ntheorem {task_id} : True := by\n  trivial\n"
            latest_output = f"import Mathlib\n\n-- latest queue official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            output_path.write_text(old_output, encoding="utf-8")
            os.utime(output_path, (1000, 1000))
            secondary_output = settings.output_lean_files_dir / "08_chap4_measurable_functions" / f"{task_id}.lean"
            secondary_output.parent.mkdir(parents=True, exist_ok=True)
            secondary_output.write_text(latest_output, encoding="utf-8")
            os.utime(secondary_output, (2000, 2000))

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([task_id], ledger, settings))

            self.assertTrue(success, detail)
            report_path = next((settings.phase2_prompt_packs_dir / "_reports").glob("review_existing_queue_*.json"))
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["tasks"][0]["official_output_file"], str(output_path))
            self.assertEqual((pack_dir / "official_snapshot_v1.lean").read_text(encoding="utf-8"), old_output)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_queue_reports_hard_check_blocker(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_queue_hard_check"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_queue_hard_check"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ), patch(
                "formalization_engine.phase2_prompt_pack.validate_candidate_hard_checks",
                return_value=(
                    False,
                    [{"severity": "error", "code": "contains_sorry", "message": "fixture queue hard-check failure"}],
                    "fixture queue hard-check failure",
                ),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([task_id], ledger, settings))

            self.assertTrue(success, detail)
            self.assertTrue(output_path.exists())
            self.assertFalse((pack_dir / "official_snapshot_v1.lean").exists())
            report_path = next((settings.phase2_prompt_packs_dir / "_reports").glob("review_existing_queue_*.json"))
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["counts"]["blocked_hard_check"], 1)
            self.assertEqual(report["tasks"][0]["queue_status"], "blocked_hard_check")
            self.assertEqual(report["tasks"][0]["next_action"], "fix_output")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_queue_reuses_matching_attempt_with_existing_result(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_existing_queue_reuse"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_existing_queue_reuse"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            result_payload = json.loads(result_path.read_text(encoding="utf-8"))
            result_payload["review_input_file"] = str(pack_dir / "semantic_review_input_v1.json")
            result_path.write_text(json.dumps(result_payload, indent=2, ensure_ascii=False), encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([], ledger, settings))

            self.assertTrue(success, detail)
            report_path = next((settings.phase2_prompt_packs_dir / "_reports").glob("review_existing_queue_*.json"))
            report = json.loads(report_path.read_text(encoding="utf-8"))
            task_report = report["tasks"][0]
            self.assertEqual(task_report["queue_status"], "review_result_present")
            self.assertEqual(task_report["next_action"], "inspect_existing_result")
            self.assertTrue(str(task_report["latest_matching_review_result_file"]).endswith("semantic_review_result_v1.json"))
            self.assertFalse((pack_dir / "semantic_review_input_v2.json").exists())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertTrue(str(task_record["current_review_input_file"]).endswith("semantic_review_input_v1.json"))
            self.assertEqual(task_record["current_review_origin"], "review-existing-queue")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_queue_reports_stale_results_as_prepared_fresh_review_work(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_existing_queue_stale_summary"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_existing_queue_stale_summary"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([task_id], ledger, settings))
            self.assertTrue(success, detail)

            stale_result = {
                "task_id": task_id,
                "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
                "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
                "review_input_file": str(pack_dir / "semantic_review_input_v1.json"),
                "candidate_hash": "stale-hash",
                "verdict": "pass",
            }
            (pack_dir / "semantic_review_result_v1.json").write_text(
                json.dumps(stale_result, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([task_id], ledger, settings))

            self.assertTrue(success, detail)
            report_path = max(
                (settings.phase2_prompt_packs_dir / "_reports").glob("review_existing_queue_*.json"),
                key=lambda path: path.stat().st_mtime,
            )
            report = json.loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["counts"]["stale_review_result"], 1)
            self.assertEqual(report["counts"]["ready_for_codex_review"], 0)
            self.assertEqual(report["review_material_summary"]["prepared_review_materials"], 1)
            self.assertEqual(report["review_material_summary"]["fresh_review_required"], 1)
            self.assertEqual(report["review_material_summary"]["stale_or_invalid_prior_results"], 1)
            self.assertEqual(report["review_material_summary"]["current_matching_review_results"], 0)
            self.assertIn("fresh_review_required=1", detail)
            markdown_path = report_path.with_suffix(".md")
            markdown = markdown_path.read_text(encoding="utf-8")
            self.assertIn("Prepared review materials", markdown)
            self.assertIn("Fresh review required", markdown)
            self.assertIn("stale_review_result` means review materials are prepared", markdown)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
