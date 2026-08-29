from __future__ import annotations

import subprocess
import sys
from pathlib import Path


FORBIDDEN_PREFIXES = [
    ".claude/worktrees/",
    "data/workspace_inventory/",
    "dependency_decisions/",
    "docs/archive/",
    "docs/plans/",
    "docs/phase2/archive/",
    "docs/superpowers/",
    "inputs/",
    "output_lean_files/",
    "formalized_chapters/",
    "phase0_ingestion_packs/",
    "phase1_prompt_packs/",
    "phase2_prompt_packs/",
    "phase2_softdep_packs/",
    "phase3_execution_batches/",
    "phase3_post_harvest_packs/",
    "phase3_softdep_packs/",
    "plans/",
    "reports/",
    "upstream/",
    "error_logs/",
    "error_logs_1/",
    "aristotle_outbox/",
    "aristotle_archives/",
    "aristole-example-outputs/",
]

FORBIDDEN_FILES = {
    "artifacts_manifest.json",
    "docs/phase2/author_errata_confirmations_2026-07.md",
    "docs/phase2/ch1_hardened_review_audit_20260711.md",
    "docs/phase2/ch1_kenneth_integration_2b86c183.md",
    "docs/phase2/chapter10_14_remark_context_reconciliation.md",
    "docs/phase2/chapter9_intro_context_reconciliation.md",
    "docs/phase2/p5_p9_health_reconciliation.md",
    "docs/phase2/textbook_complete_targets.json",
    "docs/phase2_ch10_14_clean_debt_surface_audit.json",
    "docs/phase2_ch10_14_clean_debt_surface_audit.md",
    "docs/phase2_completion_classification.json",
    "docs/phase2_completion_classification.md",
    "docs/phase2_source_output_alignment_audit.md",
    "docs/phase2_unfinished_tasks_audit.json",
    "docs/phase2_unfinished_tasks_audit.md",
    "docs/workspace_inventory.md",
    "mathlib_index.faiss",
    "mathlib_corpus.json",
    "project_ledger.json",
    "tests/test_kenneth_upstream_provenance.py",
    "lab_notebook.json",
}


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        capture_output=True,
        text=True,
        check=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def find_forbidden_tracked_files(paths: list[str]) -> list[str]:
    bad: list[str] = []
    for path in paths:
        normalized = path.replace("\\", "/")
        if normalized in FORBIDDEN_FILES:
            bad.append(normalized)
            continue
        if any(normalized.startswith(prefix) for prefix in FORBIDDEN_PREFIXES):
            bad.append(normalized)
    return bad


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    bad = find_forbidden_tracked_files(tracked_files())

    if bad:
        print("Repository hygiene check failed. Remove tracked artifacts from main repo:")
        for p in bad:
            print(f" - {p}")
        print(f"Working directory: {root}")
        return 1

    print("Repository hygiene check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

