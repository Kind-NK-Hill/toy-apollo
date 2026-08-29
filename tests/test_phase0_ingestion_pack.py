import json
import os
import shutil
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.phase0_ingestion_pack import (  # noqa: E402
    apply_phase0_pack,
    validate_phase0_pack,
    write_phase0_pack,
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
        toyapollo_output_dir=root / "ToyApollo" / "Output",
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
        phase0_ingestion_packs_dir=root / "phase0_ingestion_packs",
        phase1_prompt_packs_dir=root / "phase1_prompt_packs",
    )


CLEAN_CHAPTER9_TEX = r"""\section*{Moment Generating Functions and Characteristic Functions}

The moment generating function and characteristic function are transform functions used to analyze probability distributions.

\subsection*{9.1 Moments and Moment Generating Functions}

\begin{defbox}{9.1}
For integer $r \ge 1$, the $r$-th moment of $X$ is defined as the expectation $E[X^r]$.
\end{defbox}

\begin{thmbox}{9.1}
Suppose $X$ is a random variable such that $E[|X|^r] < \infty$. Then the $r$-th moment can be computed from the density when it exists.
\end{thmbox}

\begin{defbox}{9.2}
The moment generating function of $X$ is defined as $M_X(t)\triangleq E[e^{tX}]$.
\end{defbox}

\begin{thmbox}{9.2}
If $X$ has moment generating function $M_X(t)$, then $X$ has finite moments of all orders.
\end{thmbox}

\textit{Proof} The proof uses Taylor expansion and dominated convergence.
\hfill $\square$

\textbf{Example 9.1.1 (Moment Generating Function of Poisson Distribution)} \\
Suppose $X$ is a Poisson random variable with mean $\lambda$.
"""


class Phase0IngestionPackTests(unittest.TestCase):
    def test_write_phase0_pack_creates_operator_materials(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_pack"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pdf_path = root / "textbooks" / "book.pdf"
            pdf_path.parent.mkdir(parents=True, exist_ok=True)
            pdf_path.write_bytes(b"%PDF fixture placeholder")

            with patch(
                "src.toy_apollo.phase0_ingestion_pack._extract_pdf_pages",
                return_value="9 Moment Generating Functions\n9.1 Moments and Moment Generating Functions",
            ):
                pack_dir = write_phase0_pack(pdf_path, "157-160", "chapter9-moments-mgf", settings)

            self.assertTrue((pack_dir / "source_info.json").exists())
            self.assertTrue((pack_dir / "raw_pdf_extract.txt").exists())
            self.assertTrue((pack_dir / "cleanup_rules.md").exists())
            self.assertTrue((pack_dir / "operator_prompt.md").exists())
            self.assertTrue((pack_dir / "draft_input.tex").exists())
            self.assertTrue((pack_dir / "validation_report.json").exists())
            self.assertTrue((pack_dir / "apply_report.md").exists())
            source_info = json.loads((pack_dir / "source_info.json").read_text(encoding="utf-8"))
            self.assertEqual(source_info["page_range"], {"start": 157, "end": 160})
            self.assertEqual(source_info["output_stem"], "chapter9-moments-mgf")
            self.assertTrue(source_info["target_input_file"].endswith("inputs/chapter9-moments-mgf.tex"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_validate_phase0_pack_rejects_pdf_noise(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_validate_noise"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pack_dir = settings.phase0_ingestion_packs_dir / "chapter9-moments-mgf"
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft_input.tex").write_text(
                "9 Moment Generating Functions | Deﬁnition 9.1 | w eh a v e .E[X] | https://doi.org/10.1007/978",
                encoding="utf-8",
            )

            success, detail, report = validate_phase0_pack("chapter9-moments-mgf", settings)

            self.assertFalse(success)
            self.assertIn("failed", detail.lower())
            self.assertIn("pdf_noise", {finding["code"] for finding in report["findings"]})
            self.assertTrue((pack_dir / "validation_report.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_validate_phase0_pack_accepts_clean_tex(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_validate_clean"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pack_dir = settings.phase0_ingestion_packs_dir / "chapter9-moments-mgf"
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft_input.tex").write_text(CLEAN_CHAPTER9_TEX, encoding="utf-8")

            success, detail, report = validate_phase0_pack("chapter9-moments-mgf", settings)

            self.assertTrue(success)
            self.assertIn("passed", detail.lower())
            self.assertEqual(report["status"], "pass")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_validate_phase0_pack_rejects_multiple_source_units(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_validate_multi_source"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pack_dir = settings.phase0_ingestion_packs_dir / "chapter9-full"
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft_input.tex").write_text(
                (
                    "\\section*{Moment Generating Functions and Characteristic Functions}\n"
                    "\\subsection*{9.1 Moments and Moment Generating Functions}\n"
                    "Text.\n"
                    "\\subsection*{9.2 Characteristic Functions}\n"
                    "Text.\n"
                ),
                encoding="utf-8",
            )

            success, detail, report = validate_phase0_pack("chapter9-full", settings)

            self.assertFalse(success)
            self.assertIn("failed", detail.lower())
            self.assertIn("multiple_source_units", {finding["code"] for finding in report["findings"]})
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_validate_phase0_pack_accepts_problem_references_to_theorems(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_validate_problem_refs"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pack_dir = settings.phase0_ingestion_packs_dir / "chapter9-problems"
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft_input.tex").write_text(
                (
                    "\\subsection*{Problems}\n\n"
                    "\\textbf{Problem 9.5} By applying Theorem 9.7, derive an identity.\n"
                ),
                encoding="utf-8",
            )

            success, detail, report = validate_phase0_pack("chapter9-problems", settings)

            self.assertTrue(success, msg=detail)
            self.assertEqual(report["status"], "pass")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase0_pack_writes_only_target_input_after_validation(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_apply"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            pack_dir = settings.phase0_ingestion_packs_dir / "chapter9-moments-mgf"
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft_input.tex").write_text(CLEAN_CHAPTER9_TEX, encoding="utf-8")

            success, detail, target_path = apply_phase0_pack("chapter9-moments-mgf", settings)

            self.assertTrue(success)
            self.assertIn("inputs", detail)
            self.assertEqual(target_path, root / "inputs" / "chapter9-moments-mgf.tex")
            self.assertEqual(target_path.read_text(encoding="utf-8"), CLEAN_CHAPTER9_TEX)
            self.assertFalse((settings.plans_dir / "chapter9-moments-mgf_plan.json").exists())
            self.assertFalse(settings.project_ledger_file.exists())
            self.assertTrue((pack_dir / "apply_report.md").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_phase0_rejects_invalid_output_stem(self):
        root = REPO_ROOT / "tests" / "_tmp_phase0_bad_stem"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            with self.assertRaises(ValueError):
                validate_phase0_pack("Chapter 9 Moments", settings)
            with self.assertRaises(ValueError):
                validate_phase0_pack("chapter9/moments", settings)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_cli_help_includes_phase0_without_requiring_secrets(self):
        env = os.environ.copy()
        env.pop("DEEPSEEK_API_KEY", None)
        result = subprocess.run(
            [sys.executable, str(REPO_ROOT / "run_chapter.py"), "-h"],
            capture_output=True,
            text=True,
            cwd=str(REPO_ROOT),
            env=env,
            check=False,
        )

        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertNotIn("DEEPSEEK", result.stdout + result.stderr)
        self.assertIn("--phase0-mode", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
