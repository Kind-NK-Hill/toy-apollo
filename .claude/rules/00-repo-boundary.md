# Repo Boundary

## Purpose

Keep `ProbabilityTheoryFormalization` source-first and treat runtime outputs as external artifacts.

## Source Of Truth

- Active runtime code:
  - installed `formalize` entry point
  - `src/formalization_engine/*`
- Design guidance only:
  - the workspace's sibling `research materials/` directory
  - the workspace's indexed historical archives

## Write Boundaries

Classify important files before proposing Git tracking or cleanup:

- `must-track-now`: active runtime/code/test/docs needed for a clean checkout to run.
- `must-track-after-review`: possible source truth that needs human review for completeness or scope.
- `must-ignore-but-preserve`: generated runtime state or prompt packs that stay local and must not be deleted.
- `must-archive-not-delete`: historical or provenance material that should stay available outside the active Git surface.
- `do-not-touch`: high-risk state requiring explicit user scope before edits.

- Safe to edit:
  - `src/`
  - `tools/`
  - `tests/`
  - `docs/`
  - root agent docs and config docs
- Runtime state, usually do not hand-edit unless the task explicitly requires it:
  - `plans/`
  - `project_ledger.json`
  - sibling `ProbabilityTheoryFormalization-artifacts/state.sqlite3`
  - `lab_notebook.json`
  - `output_lean_files/`
  - `formalized_chapters/`
  - `reports/`
  - `error_logs/`
  - `phase0_ingestion_packs/`
  - `phase1_prompt_packs/`
  - `phase2_prompt_packs/`
  - `phase2_softdep_packs/`
  - `phase3_softdep_packs/` (legacy/protected local artifact; not active workflow)
  - `phase3_execution_batches/` (legacy/protected local artifact; not active workflow)
  - `phase3_post_harvest_packs/` (legacy/protected local artifact; not active workflow)
  - `dependency_decisions/`
  - `aristotle_outbox/` (legacy/protected local artifact; not active workflow)
  - `aristotle_archives/` (legacy/protected local artifact; not active workflow)
  - `.claude/worktrees/`

High-risk protected boundaries:

- The SQLite state database, legacy ledger, and notebook files are `must-ignore-but-preserve` unless a task explicitly targets state migration.
- Prompt packs are generated handoff state: ignore/search-hide them by default, preserve them locally, and summarize or archive rather than delete.
- `dependency_decisions/` is protected provenance; decide chapter-by-chapter whether any curated summary belongs in Git.
- Chapter outputs, especially Chapter 1-8/9 source, plan, output, ledger, and provenance material, are not cleanup targets.
- `.claude/worktrees/` is local agent/worktree state; inspect only when asked and never treat it as source truth.

## Current Unified Runtime

- All active Python code lives under `src/formalization_engine/*`; there is no
  active `src/*.py` compatibility package.
- `formalize` is the canonical entry point and delegates into `formalization_engine.cli.app`.
- `ProbabilityTheory/` is the only canonical Lean corpus. Ordinary authoring,
  build, and review preparation use artifact staging; only exact-subject
  `review-apply` may land a manifest-resolved path, with rollback on failure.
- Kenneth and historical MAT repositories remain external evidence/review
  sources. They are not alternative active output trees.
- Mutable outputs, prompt packs, logs, and reports resolve under the artifacts
  root. Historical repository-root copies remain protected evidence.
- See `docs/cutover_v2.md` and `docs/workspace_state.md` for the active boundary.

## Practical Rule

When docs disagree, trust current CLI behavior and current settings resolution.
