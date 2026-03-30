# Reorganization Guide (Windows First)

This document tracks the staged reorganization while preserving:

- `python run_chapter.py --phase {1,2,3,4}`
- `python run_chapter.py --status`

## Stage A: Baseline and Inventories

- Inventory files are generated under `docs/reorg/`:
  - `inventory_source.json`
  - `inventory_artifacts.json`
  - `inventory_history.json`
  - `baseline_sample.md`
- Baseline run command set (after credentials are configured):
  - `python .\run_chapter.py --phase 1 --input .\inputs\01_chap3_premeasure.tex`
  - `python .\run_chapter.py --phase 2 --input .\plans\01_chap3_premeasure_plan.json`

## Stage B: Main Repo vs Artifacts Repo

- Main repo keeps source/config/input/docs only.
- Runtime outputs and large files move to `toy-apollo-artifacts`.
- `artifacts_manifest.json` tracks snapshot metadata.
- `tools/sync_artifacts.ps1` provides `push` and `pull` sync flows.
- Sync examples:
  - Push runtime outputs to artifacts repo clone:
    - `.\tools\sync_artifacts.ps1 -Mode push -ArtifactsRepoPath ..\toy-apollo-artifacts -MainRepoPath .`
  - Pull runtime outputs from artifacts repo clone:
    - `.\tools\sync_artifacts.ps1 -Mode pull -ArtifactsRepoPath ..\toy-apollo-artifacts -MainRepoPath .`

## Stage C: Source Layout Migration (Compatibility Period)

New layered namespace is introduced under `src/toy_apollo/`:

- `cli/`
- `pipeline/`
- `integrations/`
- `core/`
- `search/`

Current `src/*.py` modules remain active as compatibility shims for one migration cycle.
- Stable entry remains root `run_chapter.py`; it now delegates to `toy_apollo.cli.app`.

## Stage D: Stabilization

- Keep phase boundaries unchanged.
- Document setup/runbook in `README.md` and this file.
- Keep `AGENTS.md` as the engineering contract.
- Current key policy for this stage: keep hardcoded defaults in `src/config.py`; env vars are optional overrides.
- New environment variable overrides:
  - `TOY_APOLLO_RUNTIME_ROOT`
  - `TOY_APOLLO_ARTIFACT_ROOT`

## Stage E: Cleanup Rules

- Main repo must not track runtime outputs/logs.
- Historical archives should be moved to the artifacts repository.
- Naming normalization target:
  - `archieve_2` -> `archive_legacy_v2` (in artifacts repo)
  - `archive_old` -> `archive_legacy_v1` (in artifacts repo)
- CI guard:
  - `.github/workflows/lean_action_ci.yml` runs `python tools/check_repo_hygiene.py`.
