# Phase2 Codex Workflow

## Purpose

This is the authoritative runbook for the Phase2 prompt-pack workflow.

Phase2 is now explicitly split into two loops:

1. Authoring / Build Loop
2. Semantic Review / Repair Loop

The default path is no longer "edit draft, then let `review-pack` decide whether it builds." The build gate is explicit and happens first.

## Default Workflow

For a new candidate:

1. `pack`
2. edit `draft.lean`
3. run `build-check`
4. repeat step 2 and 3 until the candidate is build-ready
5. run `review-now --review-subject candidate`
6. inspect the reviewer verdict and generated `semantic_review_result_vM.json`
7. run `review-apply` only when you want to land the review result
8. if review fails or is inconclusive, run `review-fix`, repair `draft.lean`, then return to `build-check`

For an existing runnable official output:

1. run `review-now --review-subject existing`
2. inspect the reviewer verdict and generated `semantic_review_result_vM.json`
3. run `review-apply` only when you want to land the review result
4. if the official output fails review, the runtime will quarantine it and generate `review_repair_request_vM.json`; continue with `review-fix`

For all existing runnable official outputs:

1. run `review-existing-queue`
2. inspect the generated queue report
3. use `review-now --review-subject current` task by task to let Codex consume the latest request and write `semantic_review_result_vM.json`
4. run `review-apply` only for the tasks you explicitly want to land

`verify` and `audit` still exist, but they are advanced runner-backed modes rather than the default operator path.

## Runtime Modes

Relevant CLI modes:

1. `pack`
2. `build-check`
3. `review-pack`
4. `review-existing`
5. `review-now`
6. `review-fix`
7. `auto-loop`
8. `review-existing-queue`
9. `review-apply`
10. `verify`
11. `audit`
12. `soft-pack`
13. `soft-apply`

Commands:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id> --candidate <path>
python .\run_chapter.py --phase 2 --phase2-mode review-pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-existing --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject current --auto-apply-pass
python .\run_chapter.py --phase 2 --phase2-mode review-fix --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-fix --tasks <task_id> --abandon-current-repair
python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id> --review-subject candidate --max-auto-rounds 6 --nonprogress-limit 2 --max-build-attempts-per-round 3
python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue
python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue --tasks <task_id>,<task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
python .\run_chapter.py --phase 2 --phase2-mode verify --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode audit --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks <problem_id>,<problem_id>
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks <problem_id>,<problem_id> --selection <path>
```

Rules:

- `pack` requires exactly one task id.
- `build-check` requires exactly one task id.
- `review-pack` requires exactly one task id and only prepares Codex handoff materials from the current build-ready candidate.
- `review-existing` requires exactly one task id and only prepares Codex handoff materials from the current official output.
- `review-now` requires exactly one task id.
- `review-now --review-subject candidate` prepares a fresh candidate review request and is the recommended Codex path for reviewing the current build-ready candidate.
- `review-now --review-subject existing` prepares a fresh existing-output review request and is the recommended Codex path for reviewing the current official output.
- `review-now --review-subject current` reuses the latest review request only if the runtime freshness preflight succeeds; otherwise it instructs the operator to prepare a fresh request.
- `review-fix` requires exactly one task id and only works when there is an active `review_repair_request_vM.json`.
- `review-fix` does not run `build-check` automatically; it seeds `draft.lean` for the next authoring pass and refreshes the repair-mode operator context.
- `auto-loop` requires exactly one task id and is a same-session Codex composite action, not a standalone unattended runtime.
- `auto-loop` persists live loop state in ledger runtime metadata; pack files only mirror that state.
- `auto-loop` can automatically advance runtime-side transitions (`review-now`, `review-apply`, `review-fix`, `build-check`), but the current Codex agent still performs the authoring edit and reviewer JSON write.
- when `auto-loop` is active, the current Codex agent must keep going in the same session: build failure means immediately continue repairing `draft.lean`, and a prepared review request means immediately write `semantic_review_result_vM.json`
- `auto-loop` should not be described or operated as "run one step, then wait for the user to say continue again" unless the user explicitly interrupts the loop.
- `nonprogress` is the semantic stop condition for repeated no-op rounds: it means the same semantic failure fingerprint or unchanged candidate content has repeated across rounds, so the current repair strategy is not meaningfully advancing.
- `review-existing-queue` scans `ToyApollo\Output\*.lean`, prepares reviewer materials for every matching official output, and optionally filters the scan with `--tasks`.
- `review-apply` requires exactly one task id and `--review-result`.
- `soft-pack` and `soft-apply` accept one or more `Problem` task ids.
- `soft-apply` requires `--selection`.
- `build-check` defaults to `phase2_prompt_packs/<task_id>/draft.lean`.
- `build-check --candidate <path>` supports an external Lean file and freezes it into `candidate_vN.lean`.
- `review-pack` without `--candidate` only works from the current build-ready candidate and remains a low-level prepare-only mode.
- `review-pack --candidate ToyApollo\Output\<task_id>.lean` remains a compatibility entrypoint, but it is internally treated as `review-existing`.
- `review-pack --candidate <external-file>` is not part of the default path and is rejected; use `build-check --candidate <external-file>` first.
- The old direct-generation/orchestrator `legacy` mode is no longer an active CLI mode.
- `verify` and `audit` require reviewer runner configuration for semantic review.

## Two-Stage Contract

### Authoring / Build Loop

The authoring loop exists to get a technically runnable candidate.

Technical runnability is not the whole authoring target. The candidate should still track the source TeX at high priority, especially for theorem/example tasks whose textbook proof contains essential constructions, partitions, reductions, or contradiction arguments.

Inputs and operator-facing files:

- `task.json`
- `context.md`
- `operator_prompt.md`
- `search_manifest.json`
- `search_notes.md`
- `imports.lean`
- `target_stub.lean`
- `draft.lean`
- `attempt_history.json`
- `failure_summary.md`
- `build_feedback.txt`

Outputs of this loop:

- `candidate_vN.lean`
- `build_result_vN.json`
- updated `attempt_history.json`
- updated `failure_summary.md`
- updated `build_feedback.txt`

Exit condition:

- the current frozen candidate passes hard checks, REPL, temporary module build, and staged `lake build ToyApollo.Output.<task_id>`

### Semantic Review / Repair Loop

The semantic review loop exists to check whether the runnable Lean candidate actually matches the source task and TeX intent.

Reviewer priority rule:

- faithful alignment with the textbook TeX is higher priority than proof shortness or local convenience
- if the source proof carries essential mathematical content, the review should reject candidates that replace that proof by theorem-specific wrappers, placeholder axioms, or assumptions that already contain the desired contradiction/conclusion
- local helper lemmas are acceptable, but they must preserve the source proof spine rather than erase it

## Semantic Review Pass Gates

`pass` requires all four gates to be covered:

1. statement fidelity
2. source proof / construction spine fidelity
3. interface contract
4. downstream adequacy

`statement preserved + downstream usable` is still insufficient if the reviewer cannot show where the source-side spine lands in Lean.

Inputs and reviewer-facing files:

- `candidate_vN.lean` for new candidate review
- `official_snapshot_vM.lean` for existing official output review
- `semantic_review_input_vM.json`
- `semantic_review_prompt_vM.md`
- `semantic_review_result_template_vM.json`

Outputs of this loop:

- `semantic_review_result_vM.json`
- `semantic_review_report_vM.md`
- `verify_result_vK.json`
- `semantic_review_request_vM.json`
- `review_repair_request_vM.json`
- `review_repair_summary_vM.md`

Responsibility split:

- `review-pack`, `review-existing`, and `review-existing-queue` only prepare reviewer materials and the corresponding `semantic_review_request_vM.json`
- `review-now` is the Codex-facing orchestration entrypoint:
  - runtime prepares or refreshes `semantic_review_request_vM.json`
  - the current Codex agent reads the request and writes `semantic_review_result_vM.json`
- `auto-loop` is the same-session Codex orchestration entrypoint:
  - runtime tracks the live round / phase / stop state in ledger runtime metadata
  - runtime advances request/apply/repair/build transitions until blocked on author or reviewer work
  - the current Codex agent writes `draft.lean` in author mode and `semantic_review_result_vM.json` in reviewer mode
  - those author/reviewer steps are not normal stopping points; in the default `auto-loop` contract the same Codex session immediately continues with the next required author/reviewer action until the loop reaches `completed` or a hard stop reason
  - when the hard stop reason is `nonprogress`, read it as "semantic non-progress": the loop has repeated the same semantic failure or candidate content and needs a different repair strategy rather than another identical round
- `review-apply` only validates and consumes an already existing review result
- `review-fix` is the semantic-repair orchestration entrypoint:
  - runtime validates the active `review_repair_request_vM.json`
  - runtime safely seeds `draft.lean` from the failed review subject
  - the current Codex agent edits `draft.lean`, runs `build-check`, and re-enters `review-now --review-subject candidate`

Exit condition:

- `review-apply` consumes a valid review result and either promotes, reconciles, rejects, or quarantines according to fixed rules
- a `pass` verdict is only appropriate when the reviewer can trace the main source claims and proof structure into the Lean artifact at an appropriate level of abstraction

## Directory Layout

Each task lives in:

- `phase2_prompt_packs/<task_id>/`

Main files:

- `task.json`
- `metadata.json`
- `operator_prompt.md`
- `context.md`
- `search_manifest.json`
- `search_notes.md`
- `imports.lean`
- `target_stub.lean`
- `draft.lean`
- `attempt_history.json`
- `failure_summary.md`
- `build_feedback.txt`
- `verification_report.md`
- `candidate_v1.lean`, `candidate_v2.lean`, ...
- `build_result_v1.json`, `build_result_v2.json`, ...
- `verify_result_v1.json`, `verify_result_v2.json`, ...
- `official_snapshot_v1.lean`, `official_snapshot_v2.lean`, ...
- `semantic_review_request_v1.json`, `semantic_review_request_v2.json`, ...
- `review_repair_request_v1.json`, `review_repair_request_v2.json`, ...
- `review_repair_summary_v1.md`, `review_repair_summary_v2.md`, ...
- `draft_pre_repair_v1.lean`, `draft_pre_repair_v2.lean`, ... when a prior draft must be archived before repair seeding
- `semantic_review_input_v1.json`, `semantic_review_prompt_v1.md`, `semantic_review_result_v1.json`, `semantic_review_report_v1.md`, ...
- `semantic_review_result_template_v1.json`, `semantic_review_result_template_v2.json`, ...
- latest-alias review files
- `rejected_official_v1/`, `rejected_official_v2/`, ... when official output is quarantined

## Migration Note

If a semantic review result predates the current strict schema or predates the current review basis, `review-apply` should reject it as stale or under-evidenced. Refresh the review request, redo the reviewer step with the fresh template, and apply again.

## File Meanings

### `task.json`

Canonical task payload:

- task id
- task type
- source plan
- hard dependencies
- soft imports
- final import union

### `metadata.json`

Pack runtime metadata includes:

- pack timing
- latest build candidate pointers
- latest build-ready candidate pointers
- latest build result
- current pending review material pointers:
  - `current_review_request_file`
  - `current_review_input_file`
  - `current_review_prompt_file`
  - `current_review_template_file`
  - `current_review_backend_id`
  - `current_review_expected_result_file`
  - `current_review_subject_kind`
  - `current_review_subject_file`
  - `current_review_subject_hash`
  - `current_review_origin`
- last completed semantic review pointers:
  - `latest_semantic_review_input_file`
  - `latest_semantic_review_result_file`
  - `latest_semantic_review_report_file`
- latest compatibility summary
- latest operation pointer
- `pack_candidate_state`
- mirrored `current_auto_loop_*` fields from ledger runtime metadata; these are display-only, not the live source of truth

### `operator_prompt.md`

This is the Codex behavior contract.

It tells Codex to:

- edit only `draft.lean`
- use local grounding artifacts first
- read `failure_summary.md` before the next build attempt
- repeat `build-check` until the candidate is build-ready
- start semantic review only after build success

### `context.md`

Human-readable runtime view.

It summarizes:

- task statement and dependency state
- latest operation summary
- build state
- current pending review material state
- current review request binding state
- last completed semantic review state
- compatibility state
- stale build-ready warnings

### `draft.lean`

This is the live editable work file.

Rules:

- Codex edits this file
- `pack` initializes it once
- later `pack` runs do not overwrite it
- `build-check` snapshots it into immutable `candidate_vN.lean`

### `candidate_vN.lean`

Immutable snapshots created by `build-check`.

These are build subjects for the new-candidate workflow. They are historical records, not work-in-place files.

### `build_result_vN.json`

Immutable structured build results.

Each file records:

- candidate file
- candidate hash
- hard-check result
- REPL result
- temporary build result
- staged official build result
- diagnostics
- primary failure kind
- blocking symbols

This is the authority for whether a candidate was technically build-ready.

### `verify_result_vK.json`

Compatibility summary for review and advanced modes.

This file is not the build authority and not the semantic review authority. It is the cross-mode operation summary and compatibility pointer used by runtime views and older integrations.

### Semantic review files

The reviewer gate writes:

- `semantic_review_input_vM.json`
- `semantic_review_prompt_vM.md`
- `semantic_review_result_template_vM.json`
- `semantic_review_result_vM.json`
- `semantic_review_report_vM.md`

The reviewer verdict is `pass`, `fail`, or `inconclusive`.

A valid `pass` must include non-empty source claims and claim mappings from the source task to the Lean declaration.

Invalid results such as task-id mismatch, hash mismatch, prompt/rubric version mismatch, missing input linkage, or invalid JSON/schema are normalized into a recorded invalid review result and handled as rejection for candidate review.

## Standard Procedure

### Step 1: Generate or refresh the pack

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
```

Expected result:

- the task directory exists under `phase2_prompt_packs/`
- `draft.lean` exists
- build/review runtime metadata is refreshed
- if there is no active official output, ledger state becomes `PACKED`
- if there is an active official output, ledger state remains `COMPLETED`

### Step 2: Read grounding before editing

Read in this order:

1. `failure_summary.md`
2. `search_manifest.json`
3. `context.md`
4. `imports.lean`
5. `target_stub.lean`

### Step 3: Edit `draft.lean`

Codex edits:

- `phase2_prompt_packs/<task_id>/draft.lean`

### Step 4: Run `build-check`

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
```

Or for an external file:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id> --candidate <path>
```

What `build-check` does:

1. freezes the current build subject into `candidate_vN.lean`
2. runs deterministic hard checks
3. runs local REPL validation
4. runs temporary module build
5. runs a staged `lake build ToyApollo.Output.<task_id>` with restore-on-exit semantics
6. writes `build_result_vN.json`
7. updates `attempt_history.json`, `failure_summary.md`, `build_feedback.txt`, `context.md`, and metadata
8. marks the candidate `build_ready` on success or `build_failed` on failure

`build-check` is the default technical gate. `review-pack` does not replace it.

### Step 5: New candidate semantic review with `review-now --review-subject candidate`

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
```

What `review-now --review-subject candidate` does:

1. resolves the current build-ready candidate
2. rejects stale draft-based candidates that no longer match `draft.lean`
3. writes `semantic_review_input_vM.json`, `semantic_review_prompt_vM.md`, and `semantic_review_result_template_vM.json`
4. points `current_review_*` metadata at the prepared candidate review materials
5. writes `verify_result_vK.json` compatibility summary
6. updates runtime metadata and marks `pack_candidate_state = review_pending`
7. enters the current agent-facing semantic review step for the fresh candidate request

Compatibility note:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-pack --tasks <task_id>
```

`review-pack` remains a prepare-only compatibility path for candidate review materials. It is not the default semantic review entrypoint.

What `review-pack` still does not do:

- no hard checks
- no REPL
- no temporary build
- no final build
- no promotion

### Step 6: Existing runnable official output review with `review-existing`

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-existing --tasks <task_id>
```

What `review-existing` does:

1. locates the current official output
2. runs `lake build ToyApollo.Output.<task_id>` sanity build
3. if sanity build fails, writes only `verify_result_vK.json` and stops
4. if sanity build succeeds, freezes the official output into `official_snapshot_vM.lean`
5. writes `semantic_review_input_vM.json`, `semantic_review_prompt_vM.md`, and `semantic_review_result_template_vM.json`
6. points `current_review_*` metadata at the prepared official-output review materials
7. writes `verify_result_vK.json`

This path does not change `pack_candidate_state`.

### Step 6b: Batch existing-output queue with `review-existing-queue`

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue
```

Optional filter:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-existing-queue --tasks <task_id>,<task_id>
```

What `review-existing-queue` does:

1. scans `ToyApollo\Output\*.lean`
2. skips `PackBuildCheck_*`, `PackVerify_*`, and `Temp_Validation*`
3. ignores non-official stems and records them in the queue report
4. resolves source tasks from `plans/*_plan.json`
5. runs `lake build ToyApollo.Output.<task_id>` sanity build for each official output
6. reuses matching existing review materials when the official output hash and prompt/rubric versions still match
7. otherwise writes a fresh `official_snapshot_vM.lean`, `semantic_review_input_vM.json`, `semantic_review_prompt_vM.md`, and `semantic_review_result_template_vM.json`
8. writes queue reports under `phase2_prompt_packs\_reports\review_existing_queue_<timestamp>.json|.md`

What it does not do:

- no reviewer backend call
- no `review-apply`
- no ledger status change
- no quarantine
- no promotion

### Step 7: Apply the semantic review

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result phase2_prompt_packs\<task_id>\semantic_review_result_vM.json
```

`review-apply` validates:

- task id
- review subject hash
- prompt version
- rubric version
- review schema
- review input binding
- candidate subject against the current build-ready pointer
- official-output subject against the current official output hash

The reviewer should start from `semantic_review_result_template_vM.json` and keep the binding fields unchanged.

Behavior:

- candidate `pass`: promote to official output, run final staged build, then mark `COMPLETED`
- candidate `fail`, `inconclusive`, or invalid: do not promote; mark `review_rejected`; preserve existing official output if one exists
- official-output `pass`: reconcile and keep `COMPLETED`
- official-output `fail`: quarantine and demote to `FAILED_LOCAL`
- official-output `inconclusive` or invalid: record the review without quarantining or changing output

## Advanced Modes

### `verify`

Use only when a stable reviewer runner is configured.

`verify` keeps its strict order:

1. confirm reviewer config exists
2. fail fast if config is missing
3. only then run the shared build gate
4. invoke the reviewer
5. promote on valid `pass`

### `audit`

Use only when you want runner-backed re-review of the current official output.

`audit` keeps its order:

1. run official output build sanity
2. if build passes, check reviewer config
3. if config is missing, record `inconclusive-no-state-change`
4. only demote on reviewer `fail`

## State Notes

- Main task status stays conservative:
  - `PACKED`
  - `FAILED_LOCAL`
  - `COMPLETED`
  - `VERIFYING`
- fine-grained Phase2 state lives in `pack_candidate_state`
- `pack_candidate_state = review_rejected` stays in the Phase 2 repair path; it does not trigger Problem soft-dependency selection

## Failure Triage

### Build failures

Read:

1. `build_result_vN.json`
2. `build_feedback.txt`
3. `failure_summary.md`

Common build failure kinds:

- `missing_import`
- `unknown_identifier`
- `noncomputable_required`
- `type_mismatch`
- `contains_sorry`
- `repl_failed`
- `temp_build_failed`
- `final_build_failed`

### Review failures

Read:

1. `semantic_review_result_vM.json`
2. `semantic_review_report_vM.md`
3. `context.md`

Do not try to solve review failures by regenerating the same review request unchanged. Either revise the candidate and re-enter the build loop, or audit the existing official output explicitly.
