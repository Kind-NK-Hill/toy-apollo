import ast
import subprocess
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class Phase2SurfaceReductionTests(unittest.TestCase):
    OWNER_MODULES = {
        "phase2_review_request.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_review_request.py",
        "phase2_review_apply.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_review_apply.py",
        "phase2_review_loop.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_review_loop.py",
        "phase2_pack_views.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_pack_views.py",
    }

    NO_PROMPT_PACK_IMPORT_MODULES = {
        "phase2_review_apply.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_review_apply.py",
        "phase2_review_loop.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_review_loop.py",
        "review_basis_parts.py": REPO_ROOT / "src" / "toy_apollo" / "phase2_pack_shared" / "review_basis_parts.py",
    }

    FOCUSED_TEST_MODULES = {
        "test_phase2_review_request.py": REPO_ROOT / "tests" / "test_phase2_review_request.py",
        "test_phase2_review_apply.py": REPO_ROOT / "tests" / "test_phase2_review_apply.py",
        "test_phase2_pack_views.py": REPO_ROOT / "tests" / "test_phase2_pack_views.py",
        "test_phase2_cli_review.py": REPO_ROOT / "tests" / "test_phase2_cli_review.py",
    }

    PROMPT_PACK_WRAPPERS = {
        "build_operator_prompt",
        "build_context_markdown",
        "build_failure_summary_markdown",
        "_refresh_pack_runtime_view",
        "build_semantic_review_basis",
        "_render_review_repair_summary",
        "_resolve_current_review_request_path",
        "_validate_review_input_freshness",
        "_load_current_codex_review_request",
        "_resolve_current_review_repair_request_path",
        "_load_current_review_repair_request",
        "run_codex_review_now",
        "run_codex_review_fix",
        "run_codex_auto_loop",
        "apply_codex_review_result",
    }

    def test_owner_modules_do_not_call_back_into_phase2_prompt_pack(self):
        for label, path in self.OWNER_MODULES.items():
            source = path.read_text(encoding="utf-8")
            self.assertNotIn("_pack(", source, f"{label} still back-jumps into phase2_prompt_pack")

    def test_owner_and_shared_modules_do_not_import_phase2_prompt_pack(self):
        for label, path in self.NO_PROMPT_PACK_IMPORT_MODULES.items():
            tree = ast.parse(path.read_text(encoding="utf-8"))
            for node in ast.walk(tree):
                if isinstance(node, ast.ImportFrom):
                    self.assertNotEqual(node.module, "src.toy_apollo.phase2_prompt_pack")
                    self.assertNotEqual(node.module, ".phase2_prompt_pack")
                    self.assertNotEqual(node.module, "phase2_prompt_pack")
                elif isinstance(node, ast.Import):
                    imported = {alias.name for alias in node.names}
                    self.assertNotIn("src.toy_apollo.phase2_prompt_pack", imported)
                    self.assertNotIn("phase2_prompt_pack", imported)

    def test_apply_owner_no_longer_registers_review_fix_callback(self):
        path = self.OWNER_MODULES["phase2_review_apply.py"]
        source = path.read_text(encoding="utf-8")
        self.assertNotIn("register_review_fix_continuation", source)
        self.assertNotIn("phase2_review_loop", source)

    def test_focused_test_modules_are_not_prompt_pack_wrappers(self):
        for label, path in self.FOCUSED_TEST_MODULES.items():
            source = path.read_text(encoding="utf-8")
            self.assertNotIn("tests.test_phase2_prompt_pack", source, f"{label} still forwards to the monolithic test file")
            self.assertNotIn("_run_prompt_pack_test", source, f"{label} still wraps prompt-pack tests instead of owning them")

    def test_prompt_pack_wrapper_functions_are_thin(self):
        path = REPO_ROOT / "src" / "toy_apollo" / "phase2_prompt_pack.py"
        tree = ast.parse(path.read_text(encoding="utf-8"))
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        for name in self.PROMPT_PACK_WRAPPERS:
            node = functions.get(name)
            self.assertIsNotNone(node, f"Missing wrapper function {name}")
            self.assertLessEqual(
                len(node.body),
                3,
                f"{name} in phase2_prompt_pack.py still contains legacy implementation instead of a thin wrapper",
            )

    def test_prompt_pack_has_single_owner_symbol_definition(self):
        path = REPO_ROOT / "src" / "toy_apollo" / "phase2_prompt_pack.py"
        tree = ast.parse(path.read_text(encoding="utf-8"))
        counts: dict[str, int] = {}
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in self.PROMPT_PACK_WRAPPERS:
                counts[node.name] = counts.get(node.name, 0) + 1
        for name in self.PROMPT_PACK_WRAPPERS:
            self.assertEqual(counts.get(name, 0), 1, f"{name} is still defined multiple times in phase2_prompt_pack.py")

    def test_prompt_pack_test_file_no_longer_hosts_owned_test_groups(self):
        path = REPO_ROOT / "tests" / "test_phase2_prompt_pack.py"
        if not path.exists():
            return
        source = path.read_text(encoding="utf-8")
        banned_markers = [
            "def test_codex_review_apply_",
            "def test_existing_review_apply_",
            "def test_review_apply_",
            "def test_review_now_",
            "def test_review_fix_",
            "def test_auto_loop_",
            "def test_build_operator_prompt_",
            "def test_cli_",
            "def test_process_target_",
        ]
        for marker in banned_markers:
            self.assertNotIn(marker, source, f"test_phase2_prompt_pack.py still hosts owned test group {marker}")

    def test_active_phase2_docs_surface_is_small(self):
        result = subprocess.run(
            ["rg", "--files", "docs/phase2"],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=True,
        )
        docs = {line.replace("\\", "/") for line in result.stdout.splitlines() if line.strip()}
        self.assertEqual(
            docs,
            {
                "docs/phase2/README.md",
                "docs/phase2/workflow.md",
                "docs/phase2/status_contract.md",
                "docs/phase2/review_criteria.md",
                "docs/phase2/artifacts.md",
                "docs/phase2/tools.md",
                "docs/phase2/rs_stieltjes_boundary.md",
                "docs/phase2/output_auxiliary_modules.md",
                "docs/phase2/author_errata_confirmations_2026-07.md",
                "docs/phase2/p5_p9_health_reconciliation.md",
                "docs/phase2/chapter9_intro_context_reconciliation.md",
                "docs/phase2/chapter10_14_remark_context_reconciliation.md",
            },
        )

    def test_phase2_docs_link_interface_policy_for_mathlib_bridge_boundary(self):
        readme = (REPO_ROOT / "docs" / "phase2" / "README.md").read_text(encoding="utf-8")
        review_criteria = (REPO_ROOT / "docs" / "phase2" / "review_criteria.md").read_text(encoding="utf-8")
        rs_boundary = (REPO_ROOT / "docs" / "phase2" / "rs_stieltjes_boundary.md").read_text(encoding="utf-8")

        self.assertIn("../interface_dependency_policy.md", readme)
        self.assertIn("../interface_dependency_policy.md", review_criteria)
        self.assertIn("textbook-first, bridge-then-Mathlib", rs_boundary)

    def test_ordinary_rg_hides_phase2_archives_packs_and_generated_reports(self):
        result = subprocess.run(
            ["rg", "--files"],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=True,
        )
        files = {line.replace("\\", "/") for line in result.stdout.splitlines() if line.strip()}
        hidden_prefixes = (
            "docs/archive/",
            "docs/phase2/archive/",
            "phase2_prompt_packs/",
        )
        hidden_files = {
            "docs/phase2/textbook_complete_targets.json",
            "docs/phase2_completion_classification.md",
            "docs/phase2_completion_classification.json",
            "docs/phase2_ch10_14_clean_debt_surface_audit.md",
            "docs/phase2_ch10_14_clean_debt_surface_audit.json",
            "docs/phase2_current_status_snapshot.md",
            "docs/phase2_current_status_snapshot.json",
            "docs/phase2_unfinished_tasks_audit.md",
            "docs/phase2_unfinished_tasks_audit.json",
            "docs/phase2_source_output_alignment_audit.md",
        }
        self.assertFalse(any(path.startswith(hidden_prefixes) for path in files))
        self.assertTrue(hidden_files.isdisjoint(files))


if __name__ == "__main__":
    unittest.main()
