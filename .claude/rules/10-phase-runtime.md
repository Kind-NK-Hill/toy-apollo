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
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>
python .\run_chapter.py --phase 2 --phase2-mode batch-run --tasks <task_id>,<task_id> --batch-max-actions 1
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks <problem_ids>
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks <problem_ids> --selection <path>
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
  - Phase 2 authority is three-gate:
    - Build gate decides only whether the Lean subject builds. Its canonical
      artifacts are `candidate_vN.lean` and `build_result_vN.json`.
    - Review gate is the only proof-status verdict. A valid review must inspect
      source TeX, the Lean subject, `proof_obligations.json`, audit signals,
      classification history, dependency status, downstream/import evidence,
      ledger runtime status, and freshness/hash evidence.
    - Apply gate lands clean completion only when the latest valid semantic
      review projects to task-level `phase2_status=pass`. Failed
      existing-output review records repair-required/open-debt evidence and
      preserves official output by default.
  - default workflow is two-stage:
    1. `pack`
    2. edit `draft.lean`
    3. `build-check` until `lake build ToyApollo.Output.<task_id>` passes
    4. `review-now --review-subject candidate` for a new candidate, `review-now --review-subject existing` for one runnable official output, or `review-existing-queue` followed by existing-output review/apply in deterministic queue order for a batch existing-output queue
    5. reviewer writes `semantic_review_result_vM.json`
    6. `review-apply`
  - after failed or inconclusive semantic review, use `auto-loop` for repair.
    Its default runtime budget and CLI floor are 15 review rounds and 15
    build-check attempts before each review round. A manual `review-fix` /
    `build-check` /
    `review-now` chain is diagnostic only unless it immediately returns to
    `auto-loop`.
  - for a chapter or task-set scope, use `batch-plan` before hand-picking work.
    `batch-plan` is a read-only scheduler over ledger and Phase2 metadata.
    `batch-run --batch-max-actions 1` may advance a bounded number of selected
    actions, but it only dispatches existing review/auto-loop commands and does
    not decide completion.
  - if `ToyApollo/Output/<task_id>.lean` is newer than and differs from the
    latest `draft.lean` or build-ready `candidate_vN.lean`, candidate review is
    stale; do not build-check or review that stale candidate. Review the
    official output with `review-now --review-subject existing`, or
    intentionally sync the output into `draft.lean` and rerun `build-check`
  - `review-pack` is not a build gate
  - `review-pack`, `review-existing`, and `review-existing-queue` only prepare review materials and are prepare-only/compatibility paths, not the default semantic review entrypoint
  - `review-now` is the current semantic review orchestration entrypoint
  - semantic review results must include `evidence_review` covering source TeX,
    Lean subject, proof obligations, audit, classification, dependency status,
    downstream/import evidence, ledger status, and hashes; if the reviewer does
    not address that evidence, the review is not valid proof-status evidence
  - `review-apply` only validates and consumes an already existing review result
  - candidate `fail`, `inconclusive`, invalid, or stale review results must not
    promote the candidate
  - existing-output `fail` must not quarantine or demote official output by
    default; it records repair-required evidence and continues through repair
    unless an operator explicitly opts into quarantine after downstream import
    checks
  - `debt-fix` and `promote-obligations` are non-default maintenance paths.
    They do not create a separate completion authority.
  - `COMPLETED_WITH_PROOF_DEBT` is not a clean dependency; hard dependents and
    selected soft imports must wait until `debt-fix` removes the accepted debt
  - before adding a new proof-debt support object or helper obligation, inspect
    existing `ToyApollo/Output` files, including older textbook outputs,
    definition files, bridge/foundation files, renamed helper variants, and
    downstream-imported files; reuse or register buildable local outputs before
    treating an obligation as unavailable
  - `verify` and `audit` are runner-backed diagnostics/report modes only. They
    do not land completion.
  - `pack` consumes hard deps plus confirmed soft imports and writes `dependency_decision_context.*`
  - `build-check` records undeclared local imports as dependency violations; it does not add them to the ledger
  - `soft-pack` and `soft-apply` are the Problem soft-dependency special case
  - `soft-apply` only applies selected soft imports to the ledger and pack artifacts
  - `soft-apply` records the reason for each selected soft import when rationale is available
  - `soft-apply` does not call an external provider and does not perform a Lean acceptance gate
- Phase 3:
  - merged into Phase 2
  - old soft-dependency commands should fail with a migration message
  - ordinary failed local tasks remain in Phase 2 review/repair workflows
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
- Phase 2 `soft-apply` chooses problem soft imports.
- Phase 2 prompt-pack/build modes consume the declared union and record violations only.
- Historical archives and old prompt packs are read-only evidence, not current
  dependency authority.

## Phase 2 Source Of Truth

- Build authority: `phase2_prompt_packs/<task_id>/build_result_vN.json` for
  technical build status only
- Review authority: the latest valid
  `phase2_prompt_packs/<task_id>/semantic_review_result_vM.json` matching the
  current review basis; this is the only proof-status verdict
- Apply authority: `review-apply` consumes a valid review result and either
  promotes a candidate with `phase2_status=pass`, reconciles existing output
  with `phase2_status=pass`, or records fail/blocked/repair evidence
- Compatibility summary: `phase2_prompt_packs/<task_id>/verify_result_vK.json`
- Runtime summary:
  - latest operation: `latest_operation_kind` + `latest_operation_file`
  - latest build section: `latest_build_result_file`
  - current pending review section: `current_review_input_file` + `current_review_prompt_file` + `current_review_template_file`
  - last completed review section: `latest_semantic_review_result_file`
  - compatibility pointer: `latest_verify_result_file`
- `proof_obligations.json`, classification artifacts, audit reports, batch
  state JSON, ledger runtime status, and dependency/downstream status are
  review evidence, caches, or reports. They must be read by review when
  applicable, but none of them independently marks a task complete or overrides
  the latest valid semantic review verdict.

## Phase 2 Problem Soft-Dependency Source Of Truth

- Source for active Problem soft-dependency selection: explicit problem task ids passed with `--tasks`.
- Selection authority: operator-confirmed selection JSON consumed by `soft-apply`.
- Ledger authority: `soft_imports` plus `soft_imports_confirmed_at` after `soft-apply`.
- `plans/unsolved_tasks.json` is legacy audit material, not the default queue driver.

## Verification Pattern

- Use `python run_chapter.py --status` for state summary
- Use `python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>` for the default technical gate
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate` for the default semantic review of a build-ready candidate
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing` for existing runnable official output
- Use `python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id> --review-subject current` for failed/inconclusive semantic-review repair
- Use `python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>` before chapter-wide or task-set routing decisions
- Use `python .\run_chapter.py --phase 2 --phase2-mode batch-run --tasks <task_id>,<task_id> --batch-max-actions 1` only to dispatch a bounded number of existing review/auto-loop actions
- Use `python .\run_chapter.py --phase 2 --phase2-mode debt-fix --tasks <task_id>` only for tasks with `accepted_as_proof_debt` in `proof_obligations.json` or the ledger proof-obligation summary, then return to `auto-loop`
- If a hard dependency is `COMPLETED_WITH_PROOF_DEBT`, or a legacy
  `COMPLETED` dependency still records `accepted_as_proof_debt`, skip the
  downstream task as proof-debt-blocked and repair the blocker first.
- Use `review-pack` and `review-existing` only as prepare-only/compatibility material-generation modes
- Use `python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue` to build the batch Codex reviewer queue from `ToyApollo/Output`
- Use `python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks <problem_ids> --selection <path>` only to persist selected soft imports
- Use `lake build ToyApollo.Output.<block_id>` as the Lean-facing health signal
- Avoid treating `lake build ToyApollo` as the only health signal
