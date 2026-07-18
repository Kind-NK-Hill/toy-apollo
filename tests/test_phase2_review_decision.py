import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


from src.toy_apollo.phase2_review_decision import evaluate_semantic_review_result  # noqa: E402
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    build_semantic_review_input,
    normalize_reviewer_result,
    run_semantic_review,
)


class Phase2ReviewDecisionTests(unittest.TestCase):
    def _review_input(self, task_id: str = "thm_11_7", task_type: str = "Theorem") -> dict:
        task = {
            "block_id": task_id,
            "type": task_type,
            "title": "Fixture theorem",
            "content": "A fixture source theorem.",
            "source_plan": "fixture_plan",
            "dependencies": [],
            "soft_imports": [],
            "soft_imports_confirmed_at": "",
        }
        candidate_lean = f"import Mathlib\n\ntheorem {task_id} : True := by trivial\n"
        candidate_hash = hashlib.sha256(candidate_lean.encode("utf-8")).hexdigest()
        review_basis = {"task": dict(task), "required_evidence_classes": []}
        context_markdown = "# Fixture review context\n"
        return {
            "schema_version": "phase2.semantic_review.input.v3",
            "task": task,
            "mode": "review-pack",
            "attempt": 1,
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "cache_key": "fixture",
            "reviewer_backend_id": "test",
            "review_subject_kind": "candidate",
            "review_subject_file": "candidate.lean",
            "review_subject_hash": candidate_hash,
            "candidate": {"file": "candidate.lean", "hash": candidate_hash, "lean": candidate_lean},
            "review_context_hash": hashlib.sha256(context_markdown.encode("utf-8")).hexdigest(),
            "review_context_markdown": context_markdown,
            "review_basis": review_basis,
            "review_basis_hash": hashlib.sha256(
                json.dumps(review_basis, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
        }

    def _raw_result(
        self,
        review_input: dict,
        *,
        proof_class: str = "source_route_proof_completed",
        completion_class: str = "source_route_proof_completed",
    ) -> dict:
        return {
            "task_id": review_input["task"]["block_id"],
            "review_input_hash": hashlib.sha256(
                json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest(),
            "candidate_hash": review_input["candidate"]["hash"],
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "verdict": "pass",
            "confidence": "high",
            "summary": "fixture review",
            "proof_class": proof_class,
            "completion_class": completion_class,
            "reviewer_independence": {
                "role": "independent_read_only_reviewer",
                "read_only": True,
                "did_edit_candidate": False,
                "used_current_review_request": True,
                "attestation": "independent fixture reviewer",
            },
            "source_claims": [{"claim": "source proof"}],
            "claim_mapping": [{"source_claim": "source proof", "lean_declaration": review_input["task"]["block_id"]}],
            "route_inspection": {
                "status": "covered",
                "source_route": "source proof",
                "expected_answer_or_statement": review_input["task"]["block_id"],
                "local_mathlib_search": "checked",
                "public_interface_check": "no public-premise relocation",
                "support_or_reassembly_decision": "direct proof",
                "stop_go_verdict": "go",
            },
            "spine_alignment": {
                "status": "covered",
                "summary": "covered",
                "obligations_checked": [{"source_obligation": "source proof", "lean_landing": review_input["task"]["block_id"], "status": "covered"}],
                "missing_obligations": [],
                "shortcut_assessment": "covered",
            },
            "obligation_review": {
                "status": "covered",
                "summary": "covered",
                "items": [],
                "open_blockers": [],
                "scaffold_assessment": [],
            },
            "evidence_review": {"status": "covered", "summary": "covered", "items": [], "blocking_issues": []},
            "interface_contract": {"status": "covered", "summary": "covered", "mismatches": []},
            "downstream_adequacy": {"status": "covered", "summary": "covered", "consumers_checked": [], "blocking_issues": []},
            "forbidden_weakenings": [{"status": "not_present", "summary": "none"}],
            "findings": [],
            "recommended_disposition": "promote",
        }

    def test_authoritative_projection_overwrites_reviewer_self_reported_pass(self):
        review_input = self._review_input()
        raw = self._raw_result(
            review_input,
            proof_class="mathlib_backed_adapter_completed",
            completion_class="mathlib_backed_adapter_completed",
        )
        raw.update({"phase2_status": "pass", "task_status": "pass", "task_role": "reviewer_claim"})

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertTrue(decision.is_semantic_verdict)
        self.assertFalse(decision.is_clean_pass)
        self.assertEqual(decision.task_status_projection.task_status, "fail")
        self.assertEqual(decision.result["phase2_status"], "fail")
        self.assertEqual(decision.result["task_status"], "fail")
        self.assertEqual(decision.result["task_role"], "proof_bearing")

    def test_missing_class_has_no_authoritative_projection(self):
        review_input = self._review_input()
        raw = self._raw_result(review_input)
        raw.pop("proof_class")
        raw.pop("completion_class")
        raw["phase2_status"] = "pass"

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertFalse(decision.is_semantic_verdict)
        self.assertFalse(decision.is_clean_pass)
        self.assertIsNone(decision.task_status_projection)
        self.assertNotIn("phase2_status", decision.result)

    def test_allowed_exception_is_not_counted_as_clean_pass(self):
        review_input = self._review_input("thm_14_8", "Theorem")
        raw = self._raw_result(
            review_input,
            proof_class="beyond_book_exception",
            completion_class="beyond_book_exception",
        )

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertTrue(decision.is_semantic_verdict)
        self.assertEqual(decision.task_status_projection.task_status, "allowed_exception")
        self.assertFalse(decision.is_clean_pass)

    def test_reviewer_cannot_override_authoritative_binding_metadata(self):
        review_input = self._review_input()
        raw = self._raw_result(review_input)
        raw.update(
            {
                "mode": "forged-mode",
                "attempt": 999,
                "cache_key": "forged-cache",
                "reviewer_backend_id": "forged-backend",
                "runner": {"status": "forged-runner"},
                "schema_version": "forged-schema",
            }
        )

        decision = evaluate_semantic_review_result(
            raw,
            review_input=review_input,
            runner_metadata={"status": "trusted-runner"},
        )

        self.assertTrue(decision.is_semantic_verdict)
        self.assertEqual(decision.result["mode"], review_input["mode"])
        self.assertEqual(decision.result["attempt"], review_input["attempt"])
        self.assertEqual(decision.result["cache_key"], review_input["cache_key"])
        self.assertEqual(decision.result["reviewer_backend_id"], review_input["reviewer_backend_id"])
        self.assertEqual(decision.result["runner"], {"status": "trusted-runner"})
        self.assertEqual(decision.result["schema_version"], "phase2.semantic_review.result.v7")

    def test_non_string_classes_and_malformed_versions_are_operational_failures(self):
        review_input = self._review_input()
        cases = []
        non_string_class = self._raw_result(review_input)
        non_string_class["proof_class"] = True
        non_string_class["completion_class"] = True
        cases.append(("non_string_class", non_string_class))
        malformed_version = self._raw_result(review_input)
        malformed_version["prompt_version"] = "nine"
        cases.append(("malformed_version", malformed_version))

        for label, raw in cases:
            with self.subTest(label=label):
                decision = evaluate_semantic_review_result(
                    raw,
                    review_input=review_input,
                    runner_metadata={"status": "test"},
                )
                self.assertFalse(decision.is_semantic_verdict)
                self.assertEqual(decision.result["cache_class"], "operational_failure")

    def test_malformed_nested_review_input_is_an_operational_failure(self):
        for field in ("task", "candidate"):
            with self.subTest(field=field):
                review_input = self._review_input()
                review_input[field] = []

                decision = evaluate_semantic_review_result(
                    {},
                    review_input=review_input,
                    runner_metadata={"status": "test"},
                )

                self.assertFalse(decision.is_semantic_verdict)
                self.assertEqual(decision.result["cache_class"], "operational_failure")
                self.assertIn(field, decision.result["normalization_reason"])

    def test_non_positive_or_malformed_review_attempt_is_an_operational_failure(self):
        for attempt in (True, 0, "bad"):
            with self.subTest(attempt=attempt):
                review_input = self._review_input()
                review_input["attempt"] = attempt
                raw = self._raw_result(review_input)

                decision = evaluate_semantic_review_result(
                    raw,
                    review_input=review_input,
                    runner_metadata={"status": "test"},
                )

                self.assertFalse(decision.is_semantic_verdict)
                self.assertEqual(decision.result["cache_class"], "operational_failure")
                self.assertIn("attempt", decision.result["normalization_reason"])

    def test_source_backed_pass_cannot_treat_missing_tex_as_not_applicable(self):
        review_input = self._review_input()
        review_input["review_basis"]["source_evidence"] = {
            "source_kind": "source_tex",
            "tex_status": "missing_required",
            "tex_exists": False,
            "tex_hash": "",
        }
        review_input["review_basis_hash"] = hashlib.sha256(
            json.dumps(
                review_input["review_basis"],
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        raw = self._raw_result(review_input)
        raw["review_input_hash"] = hashlib.sha256(
            json.dumps(review_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()

        decision = evaluate_semantic_review_result(raw, review_input=review_input, runner_metadata={"status": "test"})

        self.assertFalse(decision.is_semantic_verdict)
        self.assertIn("source", decision.result["normalization_reason"].lower())

    def test_inline_candidate_tamper_is_rejected_by_the_tracked_decision_boundary(self):
        review_input = self._review_input()
        review_input["candidate"]["lean"] += "\n-- reviewer saw different Lean\n"
        raw = self._raw_result(review_input)

        decision = evaluate_semantic_review_result(
            raw,
            review_input=review_input,
            runner_metadata={"status": "test"},
        )

        self.assertFalse(decision.is_semantic_verdict)
        self.assertIn("inline candidate", decision.result["normalization_reason"].lower())

    def test_cached_semantic_result_is_revalidated_and_rebound_to_current_input(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_decision_cache"
        try:
            shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)
            first_input = self._review_input()
            candidate_path = root / "candidate.lean"
            context_path = root / "semantic_review_context_v1.md"
            candidate_path.write_text(first_input["candidate"]["lean"], encoding="utf-8")
            context_path.write_text(first_input["review_context_markdown"], encoding="utf-8")
            first_input["review_subject_file"] = str(candidate_path)
            first_input["candidate"]["file"] = str(candidate_path)
            first_input["review_context_file"] = str(context_path)
            first_input_path = root / "semantic_review_input_v1.json"
            first_input_path.write_text(json.dumps(first_input, indent=2, ensure_ascii=False), encoding="utf-8")
            first_raw = self._raw_result(first_input)
            first_raw["review_input_file"] = str(first_input_path)
            cached = normalize_reviewer_result(
                first_raw,
                review_input=first_input,
                runner_metadata={"status": "first-run"},
            )
            (root / "semantic_review_result_v1.json").write_text(
                json.dumps(cached, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            current_input = dict(first_input)
            current_input["attempt"] = 2

            result = run_semantic_review(
                pack_dir=root,
                attempt=2,
                review_input=current_input,
                config=None,
                allow_missing_config=True,
            )

            expected_hash = hashlib.sha256(
                json.dumps(current_input, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
            ).hexdigest()
            self.assertTrue(result["cache_hit"])
            self.assertEqual(result["attempt"], 2)
            self.assertEqual(result["review_input_hash"], expected_hash)
            self.assertEqual(result["runner"]["status"], "cache_hit_revalidated")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_cache_key_covers_all_reviewer_visible_context(self):
        task = self._review_input()["task"]
        common = {
            "task": task,
            "mode": "review-pack",
            "attempt": 1,
            "candidate_path": Path("candidate.lean"),
            "candidate_code": "import Mathlib\n\ntheorem fixture : True := by trivial\n",
            "import_lines": ["import Mathlib"],
            "dependency_summary": [],
            "search_summary": {"query": "fixture"},
            "build_summary": {"success": True},
            "backend_id": "test",
            "reviewer_argv_hash": "runner",
            "review_basis": {"task": task},
        }
        first_context = "# Context\nThe source decision is A.\n"
        second_context = "# Context\nThe source decision is reversed.\n"

        first = build_semantic_review_input(
            **common,
            review_context_hash=hashlib.sha256(first_context.encode("utf-8")).hexdigest(),
            review_context_markdown=first_context,
        )
        second = build_semantic_review_input(
            **common,
            review_context_hash=hashlib.sha256(second_context.encode("utf-8")).hexdigest(),
            review_context_markdown=second_context,
        )

        self.assertNotEqual(first["cache_key"], second["cache_key"])

    def test_review_bundle_and_cache_bind_task_owned_support_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp)
            support = runtime / "ToyApollo" / "Output" / "thm_1_1_support" / "core.lean"
            support.parent.mkdir(parents=True)
            support.write_text("theorem helper : True := by trivial\n", encoding="utf-8")
            task = self._review_input("thm_1_1")["task"]
            common = {
                "task": task,
                "mode": "review-pack",
                "attempt": 1,
                "candidate_path": Path("candidate.lean"),
                "candidate_code": "theorem fixture : True := by trivial\n",
                "import_lines": ["import Mathlib"],
                "dependency_summary": [],
                "search_summary": {},
                "build_summary": {"success": True},
                "backend_id": "test",
                "reviewer_argv_hash": "runner",
                "review_basis": {"task": task},
                "runtime_root": runtime,
            }

            first = build_semantic_review_input(**common)
            support.write_text("theorem helper : True := by exact True.intro\n", encoding="utf-8")
            second = build_semantic_review_input(**common)

            self.assertEqual(len(first["subject_bundle"]["files"]), 2)
            self.assertNotEqual(
                first["subject_bundle"]["bundle_hash"], second["subject_bundle"]["bundle_hash"]
            )
            self.assertNotEqual(first["cache_key"], second["cache_key"])

    def test_tracked_collector_cli_reports_authoritative_projection_without_mutating_inputs(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_decision_cli"
        try:
            shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)
            review_input = self._review_input()
            raw = self._raw_result(
                review_input,
                proof_class="mathlib_backed_adapter_completed",
                completion_class="mathlib_backed_adapter_completed",
            )
            raw["phase2_status"] = "pass"
            input_path = root / "review_input.json"
            result_path = root / "raw_result.json"
            input_path.write_text(json.dumps(review_input, indent=2, ensure_ascii=False), encoding="utf-8")
            result_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False), encoding="utf-8")
            input_before = input_path.read_text(encoding="utf-8")
            result_before = result_path.read_text(encoding="utf-8")

            completed = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "tools" / "phase2_review_decision.py"),
                    "--review-input",
                    str(input_path),
                    "--review-result",
                    str(result_path),
                ],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
            )

            self.assertEqual(completed.returncode, 0, completed.stderr)
            payload = json.loads(completed.stdout)
            self.assertTrue(payload["is_semantic_verdict"])
            self.assertFalse(payload["is_clean_pass"])
            self.assertEqual(payload["phase2_status"], "fail")
            self.assertEqual(payload["result"]["phase2_status"], "fail")
            self.assertEqual(input_path.read_text(encoding="utf-8"), input_before)
            self.assertEqual(result_path.read_text(encoding="utf-8"), result_before)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_tracked_collector_cli_rejects_identity_mismatch(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_decision_cli_identity"
        try:
            shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)
            review_input = self._review_input()
            raw = self._raw_result(review_input)
            raw["task_id"] = "thm_wrong_identity"
            input_path = root / "review_input.json"
            result_path = root / "raw_result.json"
            input_path.write_text(json.dumps(review_input, indent=2, ensure_ascii=False), encoding="utf-8")
            result_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False), encoding="utf-8")

            completed = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "tools" / "phase2_review_decision.py"),
                    "--review-input",
                    str(input_path),
                    "--review-result",
                    str(result_path),
                ],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
            )

            self.assertEqual(completed.returncode, 2)
            payload = json.loads(completed.stdout)
            self.assertFalse(payload["is_semantic_verdict"])
            self.assertIsNone(payload["phase2_status"])
            self.assertIn("task id mismatch", payload["result"]["normalization_reason"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_tracked_collector_cli_refuses_to_overwrite_input_or_result(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_decision_cli_alias"
        try:
            shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)
            review_input = self._review_input()
            raw = self._raw_result(review_input)
            input_path = root / "review_input.json"
            result_path = root / "raw_result.json"
            input_path.write_text(json.dumps(review_input, indent=2, ensure_ascii=False), encoding="utf-8")
            result_path.write_text(json.dumps(raw, indent=2, ensure_ascii=False), encoding="utf-8")
            result_before = result_path.read_text(encoding="utf-8")

            completed = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "tools" / "phase2_review_decision.py"),
                    "--review-input",
                    str(input_path),
                    "--review-result",
                    str(result_path),
                    "--output",
                    str(result_path),
                ],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
            )

            self.assertEqual(completed.returncode, 2)
            self.assertIn("separate", completed.stderr.lower())
            self.assertEqual(result_path.read_text(encoding="utf-8"), result_before)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
