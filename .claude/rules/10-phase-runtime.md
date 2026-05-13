# Phase Runtime

## Stable Commands

```powershell
python .\run_chapter.py -h
python .\run_chapter.py --status
python .\run_chapter.py --phase 0 --phase0-mode pack --input <source.pdf> --page-range <start-end> --phase0-output <output_stem>
python .\run_chapter.py --phase 0 --phase0-mode validate --phase0-output <output_stem>
python .\run_chapter.py --phase 0 --phase0-mode apply --phase0-output <output_stem>
python .\run_chapter.py --phase 1 --phase1-mode pack --input .\inputs\<source>.tex
python .\run_chapter.py --phase 1 --phase1-mode apply --input .\inputs\<source>.tex
python .\run_chapter.py --phase 1 --phase1-mode apply --input .\inputs
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id> --candidate <path>
python .\run_chapter.py --phase 2 --phase2-mode review-pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-existing --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing
python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
python .\run_chapter.py --phase 2 --phase2-mode verify --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode audit --tasks <task_id>
python .\run_chapter.py --phase 3 --phase3-mode offload
python .\run_chapter.py --phase 3 --phase3-mode soft-pack --tasks <problem_ids>
python .\run_chapter.py --phase 3 --phase3-mode soft-apply --tasks <problem_ids> --selection <path>
python .\run_chapter.py --phase 3 --phase3-mode plan-batches --tasks <problem_ids>
python .\run_chapter.py --phase 3 --phase3-mode offload-batch --batch <batch_id>
python .\run_chapter.py --phase 3 --phase3-mode repair-pack --tasks <task_id>
python .\run_chapter.py --phase 3 --phase3-mode repair-verify --tasks <task_id>
python .\run_chapter.py --phase 3 --phase3-mode repair-verify --tasks <task_id> --candidate <path>
```

## Phase Contract

- Phase 0:
  - create `phase0_ingestion_packs/<output_stem>/` from textbook PDF pages
  - `pack` writes operator materials only and does not write `inputs/`
  - `validate` checks `draft_input.tex` against clean-input formatting rules
  - `apply` writes only `inputs/<output_stem>.tex` after validation passes
  - Phase 0 does not touch the ledger, generate plans, or trigger Phase 1
  - cleaned inputs are source-unit scoped: one numbered subsection, or one
    Problems section; do not clean a whole chapter into one input
  - chapter intro may be included only with the first numbered subsection of
    that chapter
- Phase 1:
  - `pack` prepares a prompt pack from cleaned `.tex`; it does not decompose the text by itself
  - agent/human decompose is the explicit middle step that reads `phase1_prompt_packs/<source>/input.tex` and writes `draft_plan.json`
  - the middle `draft_plan.json` authoring step is not a CLI mode; CLI supports only `--phase1-mode pack` and `--phase1-mode apply`
  - `apply --input` must point to the original source `.tex` or the `inputs/` directory; do not pass `phase1_prompt_packs/<source>/draft_plan.json`
  - `apply` validates the agent-authored `draft_plan.json`, writes `plans/*_plan.json`, and registers discovery state in the ledger
  - `apply` records dependency decisions for declared hard deps and explicit textbook references
  - one source unit becomes one Phase 1 plan; if a `.tex` contains multiple
    numbered subsections, split it before running `pack`
  - problems belong in their own source unit and plan
- Phase 2:
  - old direct-generation/`legacy` mode is not a stable recommended command; treat it as historical compatibility only when current CLI help still exposes it
  - default workflow is two-stage:
    1. `pack`
    2. edit `draft.lean`
    3. `build-check` until `lake build ToyApollo.Output.<task_id>` passes
    4. `review-now --review-subject candidate` for a new candidate, `review-now --review-subject existing` for one runnable official output, or `review-existing-queue` followed by `review-now --review-subject current` for a batch existing-output queue
    5. reviewer writes `semantic_review_result_vM.json`
    6. `review-apply`
  - `review-pack` is not a build gate
  - `review-pack`, `review-existing`, and `review-existing-queue` only prepare review materials and are prepare-only/compatibility paths, not the default semantic review entrypoint
  - `review-now` is the current semantic review orchestration entrypoint
  - `review-apply` only validates and consumes an already existing review result
  - `verify` and `audit` remain runner-backed advanced modes
  - `pack` consumes hard deps plus confirmed soft imports and writes `dependency_decision_context.*`
  - `build-check` records undeclared local imports as dependency violations; it does not add them to the ledger
- Phase 3:
  - `offload` resolves `FAILED_LOCAL` tasks from the ledger
  - exclude tasks with `pack_candidate_state = review_rejected` from automatic offload
  - `soft-pack`, `soft-apply`, `plan-batches`, `offload-batch` support the operator-driven problem workflow
  - `soft-apply` only applies selected soft imports to the ledger and pack artifacts
  - `soft-apply` records the reason for each selected soft import when rationale is available
  - `soft-apply` does not run Aristotle and does not perform a Lean acceptance gate
  - `offload` and `offload-batch` materialize the final hard/soft union for Aristotle and record that materialization
  - `repair-pack` and `repair-verify` form the phase3 post-harvest repair track
  - the phase3 post-harvest repair track is for local repair after Aristotle harvest, not for every harvest failure class
- Phase 4:
  - CLI branch is currently disabled/no-op
  - do not document it as automated until the code path is restored

## Interface Dependency Policy

- Current policy is documented in `docs/interface_dependency_policy.md`.
- Dependency decision trail details are documented in `docs/dependency_decision_trail.md`.
- Do not rewrite existing runnable Lean output only to make every file use one
  style.
- For a new important concept, first define it in the textbook style, prove a
  small set of direct properties, then add a theorem connecting it to Mathlib
  when Mathlib has the same idea or a more general version.
- After that connection exists, later Lean work should usually use the standard
  Mathlib way of writing definitions and theorem statements.
- Project textbook definitions such as `expectation`, `textbookIntegral`,
  `StieltjesMeasureFunction`, `rsIntegral`, or `totalVariationDistance` should
  still be used directly when the task introduces them, studies them, or must
  reuse a theorem stated with that exact project definition.
- Common textbook notation such as `E[X]`, integrals, distributions, and
  Stieltjes integrals is mathematical context, not an automatic Lean import.
- When a later theorem must connect the textbook way and the Mathlib way, add or
  import a translation lemma, often in a bridge file.
- Common notation is not an automatic dependency.  If it becomes one, record the
  exact reason in the dependency decision trail.

## Dependency Decision Source Of Truth

- Ledger source of truth: current task state and current hard/soft import union.
- Decision trail source of truth: why a dependency was selected.
- Trail records live under `dependency_decisions/<task_id>.jsonl`.
- Phase 1 chooses hard dependencies.
- Phase 3 `soft-apply` chooses problem soft imports.
- Phase 2 consumes the declared union and records violations only.
- Offload materializes the declared union for Aristotle.
- Historical archives and old prompt packs are read-only evidence, not current
  dependency authority.

## Phase 2 Source Of Truth

- Build authority: `phase2_prompt_packs/<task_id>/build_result_vN.json`
- Review authority: `phase2_prompt_packs/<task_id>/semantic_review_result_vM.json`
- Compatibility summary: `phase2_prompt_packs/<task_id>/verify_result_vK.json`
- Runtime summary:
  - latest operation: `latest_operation_kind` + `latest_operation_file`
  - latest build section: `latest_build_result_file`
  - current pending review section: `current_review_input_file` + `current_review_prompt_file` + `current_review_template_file`
  - last completed review section: `latest_semantic_review_result_file`
  - compatibility pointer: `latest_verify_result_file`

## Phase 3 Source Of Truth

- Default candidate source: ledger tasks in `FAILED_LOCAL`
- Exclusion rule:
  - do not offload tasks whose `pack_candidate_state` is `review_rejected`
- Backfill order:
  - `plans/*_plan.json`
  - `plans/offload_candidates_legacy.json`
  - `ledger.candidate_snapshot`
- `plans/unsolved_tasks.json` is legacy audit material, not the default queue driver

## Verification Pattern

- Use `python run_chapter.py --status` for state summary
- Use `python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>` for the default technical gate
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate` for the default semantic review of a build-ready candidate
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing` for existing runnable official output
- Use `review-pack` and `review-existing` only as prepare-only/compatibility material-generation modes
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue` to build the batch Codex reviewer queue from `ToyApollo/Output`
- Use `python .\run_chapter.py --phase 3 --phase3-mode soft-apply --tasks <problem_ids> --selection <path>` only to persist selected soft imports
- Use `python .\run_chapter.py --phase 3 --phase3-mode repair-pack --tasks <task_id>` before editing a post-harvest repair candidate
- Use `python .\run_chapter.py --phase 3 --phase3-mode repair-verify --tasks <task_id>` as the local acceptance gate for the phase3 post-harvest repair track
- Use `lake build ToyApollo.Output.<block_id>` as the Lean-facing health signal
- Avoid treating `lake build ToyApollo` as the only health signal
