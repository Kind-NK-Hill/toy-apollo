# Repo Boundary

## Purpose

Keep `toy-apollo` source-first and treat runtime outputs as external artifacts.

## Source Of Truth

- Active runtime code:
  - `run_chapter.py`
  - `src/toy_apollo/*`
  - legacy compatibility modules under `src/*.py`
- Design guidance only:
  - `D:\Grad_Study\Practimum\Formalization\research materials`
  - `D:\Grad_Study\Practimum\Formalization\toy_apollo_archive`

## Write Boundaries

Classify important files before proposing Git tracking or cleanup:

- `must-track-now`: active runtime/code/test/docs needed for a clean checkout to run.
- `must-track-after-review`: possible source truth that needs human review for completeness or scope.
- `must-ignore-but-preserve`: generated runtime state or prompt packs that stay local and must not be deleted.
- `must-archive-not-delete`: historical or provenance material that should stay available outside the active Git surface.
- `do-not-touch`: high-risk state requiring explicit user scope before edits.

- Safe to edit:
  - `src/`
  - `ToyApollo/` source modules
  - `tools/`
  - `tests/`
  - `docs/`
  - root agent docs and config docs
- Runtime state, usually do not hand-edit unless the task explicitly requires it:
  - `plans/`
  - `project_ledger.json`
  - sibling `toy-apollo-artifacts/state.sqlite3`
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

## Current Migration Reality

- New code should land under `src/toy_apollo/*`.
- `src/*.py` still contains real runtime logic during the migration period.
- `run_chapter.py` remains the stable root entry and delegates into `toy_apollo.cli.app`.

## Practical Rule

When docs disagree, trust current CLI behavior and current settings resolution.
