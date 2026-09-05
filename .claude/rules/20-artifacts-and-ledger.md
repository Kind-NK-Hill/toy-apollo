# Artifacts And Ledger

## What The Artifacts Repo Is For

`ProbabilityTheoryFormalization-artifacts` exists to hold runtime outputs and large generated state so the main repository can stay source-focused.

Typical artifact sets:

- `output_lean_files/`
- `formalized_chapters/`
- `reports/`
- `error_logs/`
- `aristotle_outbox/` (legacy/protected local provider artifact)
- `aristotle_archives/` (legacy/protected local provider artifact)
- `mathlib_index.faiss`
- `mathlib_corpus.json`
- `state.sqlite3` (workspace operational state)
- `project_ledger.json` (legacy protected evidence)
- `lab_notebook.json`

## Artifact Glossary

- `must-ignore-but-preserve`: generated runtime state that should stay out of Git and must not be deleted as cleanup.
- `must-archive-not-delete`: historical/provenance material that is not active runtime truth but remains evidence.
- `do-not-touch`: high-risk state that requires explicit user scope before any edit.
- `artifact-root shared`: state that may be synchronized through the artifact root instead of the source repo.
- `tracked source truth`: small, reviewed source/config/docs needed for a clean checkout to run.

## Current Runtime Resolution

Settings come from `src/formalization_engine/core/settings.py`:

- `FORMALIZATION_ENGINE_RUNTIME_ROOT`
- `FORMALIZATION_ENGINE_ARTIFACT_ROOT`

The canonical state database always resolves to the sibling artifacts root;
campaign/artifact overrides do not move it into a campaign.

## Ledger Rules

- `ProbabilityTheoryFormalization-artifacts/state.sqlite3` is the single operational state database and is `ignored-but-protected`.
- `project_ledger.json` is frozen legacy evidence after SQLite activation; compatibility code reads its imported copy but must not rewrite the file.
- `lab_notebook.json` follows the same preserve-by-default rule.
- Do not delete it as cleanup.
- Do not rename status strings without deliberate migration work.
- Treat legacy ledger snapshots and prompt-pack metadata as generated evidence, never as a second current authority.

## Protected Provenance And Prompt Packs

- `dependency_decisions/` is protected provenance, not disposable output. Keep it local/artifact-rooted by default; promote only curated chapter-scoped summaries to Git after review.
- `phase0_ingestion_packs/` and `phase1_prompt_packs/` are prompt-pack handoff state: ignore them, preserve them locally, and archive summaries when needed instead of deleting packs.
- Chapter 9 prompt packs and related provenance deserve special preserve-before-review handling; do not collapse them into a generic cleanup bucket.
- Phase 2 prompt packs and Phase 2 Problem soft-dependency packs are generated runtime state. They are normally `must-ignore-but-preserve`, not tracked source.
- Retired provider artifacts are still protected local artifacts. Do not delete them as cleanup, and do not treat them as active workflow inputs.

## Sync Commands

```powershell
.\tools\sync_artifacts.ps1 -Mode push -ArtifactsRepoPath ..\ProbabilityTheoryFormalization-artifacts -MainRepoPath .
.\tools\sync_artifacts.ps1 -Mode pull -ArtifactsRepoPath ..\ProbabilityTheoryFormalization-artifacts -MainRepoPath .
```

## Important Current Gap

The artifacts repo README describes snapshot-style storage, but the current sync script mirrors artifact paths directly at repo root. Treat the script as implementation truth until snapshot storage is actually implemented.
