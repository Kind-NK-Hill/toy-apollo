"""Publication boundary; independent of the local evidence-preservation policy."""

FORBIDDEN_PREFIXES = (
    ".claude/worktrees/", "data/workspace_inventory/", "dependency_decisions/",
    "docs/archive/", "docs/plans/", "docs/phase2/archive/", "docs/superpowers/",
    "inputs/", "plans/", "upstream/", "output_lean_files/", "formalized_chapters/",
    "phase0_ingestion_packs/", "phase1_prompt_packs/", "phase2_prompt_packs/",
    "phase2_softdep_packs/", "phase3_execution_batches/", "phase3_post_harvest_packs/",
    "phase3_softdep_packs/", "reports/", "error_logs/", "error_logs_1/",
    "aristotle_outbox/", "aristotle_archives/", "aristole-example-outputs/",
)
FORBIDDEN_FILES = {
    "artifacts_manifest.json", "mathlib_index.faiss", "mathlib_corpus.json",
    "project_ledger.json", "lab_notebook.json", "tests/test_kenneth_upstream_provenance.py",
    "tests/fixtures/semantic_fail_diagnosis_result_v1.json",
    "data/migration/legacy_evidence_relocation_v1.json",
    "data/migration/legacy_name_allowlist_v1.json",
    "data/task_catalog/catalog_policy_v1.json", "data/task_catalog/catalog_policy_v2.json",
    "docs/catalog_v2.md", "docs/cutover_v2.md", "docs/authority_relocation_v2.md",
    "docs/workspace_inventory.md", "tools/check_active_surface.py",
    "docs/phase2/author_errata_confirmations_2026-07.md",
    "docs/phase2/ch1_hardened_review_audit_20260711.md",
    "docs/phase2/ch1_kenneth_integration_2b86c183.md",
    "docs/phase2/chapter10_14_remark_context_reconciliation.md",
    "docs/phase2/chapter9_intro_context_reconciliation.md",
    "docs/phase2/p5_p9_health_reconciliation.md",
    "docs/phase2/textbook_complete_targets.json",
    "docs/phase2_ch10_14_clean_debt_surface_audit.json",
    "docs/phase2_ch10_14_clean_debt_surface_audit.md",
    "docs/phase2_completion_classification.json", "docs/phase2_completion_classification.md",
    "docs/phase2_source_output_alignment_audit.md",
    "docs/phase2_unfinished_tasks_audit.json", "docs/phase2_unfinished_tasks_audit.md",
}
ALLOWED_PREFIXES = ("src/", "tests/", "tools/", "docs/", "examples/", "ProbabilityTheory/",
                    ".agents/", ".claude/rules/", ".github/")
ALLOWED_ROOT_FILES = {
    ".editorconfig", ".gitattributes", ".gitignore", ".ignore", ".rgignore",
    "AGENTS.md", "CLAUDE.md", "CONTEXT.md", "README.md", "README.zh-CN.md",
    "CONTRIBUTING.md", "SECURITY.md", "LICENSE", "COORDINATION_PROVENANCE.md",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain", "pyproject.toml",
    "requirements.txt", "manifest_by_chapter.csv",
}


def forbidden(path: str) -> bool:
    path = path.replace("\\", "/")
    parts = path.split("/")
    return (path.startswith("/") or ":" in path or ".." in parts or ".git" in parts
            or any(p.startswith(".env") for p in parts)
            or path.lower().endswith((".sqlite3", ".sqlite", ".sqlite3-wal", ".sqlite3-shm", ".sqlite-wal", ".sqlite-shm", ".db", ".db-wal", ".db-shm", ".pyc", ".pyo", ".pdf"))
            or "__pycache__" in parts or any(p.startswith("_tmp") for p in parts)
            or path in FORBIDDEN_FILES or path.startswith(FORBIDDEN_PREFIXES))


def selected(path: str) -> bool:
    return not forbidden(path) and (path in ALLOWED_ROOT_FILES or path.startswith(ALLOWED_PREFIXES))


def find_forbidden_tracked_files(paths: list[str]) -> list[str]:
    return [p.replace("\\", "/") for p in paths if forbidden(p)]
