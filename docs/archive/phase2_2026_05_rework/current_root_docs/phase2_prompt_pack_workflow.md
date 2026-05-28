# Phase2 Codex Workflow

## Purpose

This is the authoritative runbook for the Phase2 prompt-pack workflow.
For proof-fidelity verdicts, completion classes, public proof-package surface
rules, and obligation landing discipline, read
`docs/phase2_proof_fidelity_contract.md` first. This workflow document explains
how to run Phase2; the contract explains what the result means.

Phase2 is now explicitly split into two loops:

1. Authoring / Build Loop
2. Semantic Review / Repair Loop

The default path is no longer "edit draft, then let `review-pack` decide whether it builds." The build gate is explicit and happens first.

Phase2 uses the three-level tracking policy defined in
`docs/phase2_proof_fidelity_contract.md`: ordinary Phase2, interface
translation, and complex obligation tracking. The default remains ordinary
Phase2; proof-obligation ledgers are reserved for complex source-step tracking.

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
9. if the task lands as `COMPLETED_WITH_PROOF_DEBT`, or an older completed task has `accepted_as_proof_debt` in `proof_obligations.json` or the ledger proof-obligation summary, run `debt-fix`, then `review-fix`, repair `draft.lean`, and return to `build-check`

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
7. `debt-fix`
8. `auto-loop`
9. `review-existing-queue`
10. `review-apply`
11. `verify`
12. `audit`
13. `soft-pack`
14. `soft-apply`

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
python .\run_chapter.py --phase 2 --phase2-mode debt-fix --tasks <task_id>
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
- `debt-fix` requires exactly one task id and works only when `proof_obligations.json` or the ledger proof-obligation summary contains `accepted_as_proof_debt`.
  It creates a normal `review_repair_request_vM.json` with `repair_trigger = proof_debt`,
  seeds from the official output or latest official snapshot, and then the normal
  `review-fix -> build-check -> review-now --review-subject candidate -> review-apply`
  loop discharges the debt.
  It also recognizes older tasks whose ledger status is still `COMPLETED` but whose proof-obligation summary already records accepted debt.
- `promote-obligations` turns blocking `proof_obligations.json` entries into
  first-class `Phase2ObligationTask` ledger children. With no `--tasks` filter it
  scans all existing Phase 2 packs; with `--tasks` it only promotes the selected
  parent tasks. These children keep their own pack directory and ordinary
  Phase2 counters, but their output owner is the parent task, for example
  `ToyApollo.Output.thm_10_8`.
- An obligation child uses the normal loop:
  `pack -> build-check -> review-pack/review-apply`. Its build/review failures
  count against the child task's `phase2_build_fail_counter` and
  `phase2_review_fail_counter`, with the same hard limit of 15. When review
  passes, the parent `proof_obligations.json` entry is marked `proved`; the child
  task remains in the ledger as a closed historical subtask rather than being
  deleted.
- `COMPLETED_WITH_PROOF_DEBT` is not a clean dependency. Ordinary `pack`,
  `build-check`, `review-now`, `auto-loop`, and `soft-apply` refuse downstream
  work that would consume a hard dependency or selected soft import carrying
  accepted proof debt.
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

## Multi-Task Dependency Blocking

This rule applies to both chapter-wide/task-set goals and single-task entrypoint
preflights. It does not change the internal `pack -> build-check -> review-now
-> review-apply` contract for a task whose hard dependencies are clean.
For the durable batch checklist, status schema, and dry-run summary helper, see
`docs/phase2_batch_controller.md`.

If a task reaches a hard stop during a task-set run, for example
`hard_failure`, `nonprogress`, `max_rounds`, or `build_budget_exhausted`, treat
that task as failed for the current task set. Every uncompleted task that hard
depends on that failed task must be marked/skipped as dependency-failed rather
than attempted as an ordinary task.

Dependency failure is not a task-set stop condition. After marking the direct or
transitive blocked dependents, continue with remaining tasks whose hard
dependencies are not failed. A chapter/task-set goal stops only when every task
in scope is terminal.

Accepted proof debt is a separate blocker. A task with
`COMPLETED_WITH_PROOF_DEBT`, or a legacy `COMPLETED` task whose proof-obligation
summary contains `accepted_as_proof_debt`, is terminal for itself but must not be
used as a clean upstream dependency. Direct and transitive hard dependents are
`DEPENDENCY_PROOF_DEBT` until the blocker is repaired with `debt-fix` and lands
cleanly. Soft-dependency packs exclude debt-bearing materials, and `soft-apply`
rejects a stale selection if a chosen material became debt-bearing after pack
generation.

Chapter/task-set summaries must distinguish terminal state from success. Do not
describe a task set as "passed" or "completed" merely because every task is
terminal. Report at least:

- semantic-pass/completed tasks
- completed-with-proof-debt tasks
- root `FAILED_LOCAL` tasks, grouped by stop reason
- dependency-failed tasks, grouped by failed hard dependency
- dependency-proof-debt tasks, grouped by proof-debt hard dependency
- any remaining nonterminal tasks

If one root failure blocks downstream tasks, include a root-failure audit summary
rather than letting the dependency-failed count hide the original blocker.

## Source TeX Proof Inspection

Follow `docs/phase2_proof_fidelity_contract.md` for the source-inspection
requirement. Workflow-specific rule: record the inspected TeX span and proof
spine in the task-local artifact that explains the decision, such as
`semantic_review_result_vM.json`, `semantic_review_report_vM.md`,
`failure_summary.md`, or `hard_failure_note.md`.

## Existing Output Dependency Scan

Follow the source and dependency discipline in
`docs/phase2_proof_fidelity_contract.md`. Workflow-specific rule: if an existing
output discharges an obligation but metadata is missing, treat that as metadata
repair and surface the declaration in review context before inventing new
scaffold.

### Translation and Proof-Debt Support Classification

Use `docs/phase2_proof_fidelity_contract.md` as the classification source of
truth. Operationally:

- `interface_translation` is only for representation mismatch between textbook
  notation, Mathlib, and existing ToyApollo declarations.
- substantive source mathematics must be proved, classified as open math debt,
  or explicitly placed in the single accepted beyond-book exception.
- `proof_debt_support` is exceptional and auditable; it is not the default path
  for normal tasks and is never equivalent to `proved`.
- when a step has both interface and mathematical content, split the bridge from
  the mathematical obligation.

## Complex Task Decomposition Gate

Use `docs/phase2_proof_fidelity_contract.md` for the normal/complex boundary
and the decompose-then-reconstruct rule. This section records only the runtime
consequences for prompt-pack artifacts.

Existing prompt packs may contain
`phase2_prompt_packs/<task_id>/proof_obligations.json`. For normal tasks this
file is lightweight review metadata and should not force the task into a debt
workflow. Normal tasks stay on the older Phase2 path: build, semantic review of
source claims, proof spine, interface contract, and downstream adequacy. For
complex tasks it is the machine-readable decomposition artifact and must
contain:

- source TeX file/span inspected
- complexity class and reasons
- source proof obligation nodes in textbook order
- dependencies between obligation nodes
- Lean landing plan and status for each obligation
- scaffold hypotheses, classified as `interface_translation`,
  `assembly_scaffold`, `support_constructor`, `support_package`,
  `proof_debt_support`, `proof_obligation`, `external_theorem_gap`, or
  `forbidden_shortcut`
- reconstruction target showing how proved obligations assemble into the
  exported task theorem or definition
- current blocker/review history

The generated `source_proof_spine` entry is only an unresolved placeholder, and
`decomposition_plan.md` is only a human-readable companion. A complex task
passes semantic review only when the candidate can be mapped back to concrete
obligation nodes and the exported theorem reconstructs the source claim.

### Complex Retry Budget

After a complex task has been previously hard-stopped without sufficient
decomposition evidence, a renewed attempt must continue until the task is
completed, explicitly interrupted by the user, blocked by a documented mechanism
failure, or one of the two Phase 2 failure streak counters reaches 15.

The counters are independent and hard-coded:

- `phase2_build_fail_counter`: consecutive failed `build-check` attempts before
  semantic review. Each failed build attempt increments this counter. A
  successful `build-check` resets it to `0`.
- `phase2_review_fail_counter`: failed or inconclusive semantic reviews of
  build-ready candidates. A successful `build-check` does not increment this
  counter; it only makes the next review eligible to count. A failed or
  inconclusive candidate review increments it by `1`. A semantic pass completes
  the task and resets the live failure path.

A task may enter `FAILED_LOCAL` only when:

- `phase2_build_fail_counter >= 15`, or
- `phase2_review_fail_counter >= 15`.

Build failures and review failures must not be mixed into one shared total. For
example, 14 build failures followed by a successful build and one review failure
is not 15 failures; it is `build=0`, `review=1`, so the task remains
nonterminal.

Pure setup failures, missing reviewer configuration, stale request refreshes, or
dependency-failed skips do not increment either counter. A long-running build or
review that is manually aborted or times out without a canonical
`build_result_vM.json`, `semantic_review_result_vM.json`, or `review-apply`
result is a mechanism blocker, not a counted failure. Record it in the
task-local blocker log and continue with a smaller diagnostic check or an
adjusted timeout strategy.

If the runtime or documentation allows a complex task to stop before this
budget without completion, explicit user interruption, or a documented external
mechanism blocker, treat that as a workflow defect: patch the Markdown/runbook
rule first, then resume the task.

## Hard Failure Admission

Use `docs/phase2_proof_fidelity_contract.md` for hard-failure admission
criteria. Workflow-specific rule: every `hard_failure` must leave a task-local
`hard_failure_note.md` or equivalent review artifact, and timed-out or aborted
runs without canonical result files are mechanism blockers, not proof failures.

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

Statement fidelity includes public-assumption expansion. The reviewer must
expand any local `def`, `structure`, or package used in the public theorem
assumptions, classify extra fields, and reject hidden strengthening. A field
such as `MemLp` or `Integrable` may be acceptable when it is the Lean spelling of
a source finiteness condition; it is not acceptable when it is an unproved proof
ingredient that should have been derived internally.

For Chapter 10 and later, clean completion also requires the public proof-debt
surface gate. This gate applies to every official task output file, not only
files whose source task type is `Theorem_with_Proof`:

- Run `python .\tools\audit_phase2_clean_debt_surface.py --write-report
  --fail-on-errors` before claiming the Chapter 10-14 proof-debt surface is
  clean.
- Apply the public-surface and obligation-landing rules from
  `docs/phase2_proof_fidelity_contract.md`.
- Do not report `textbook_proof_completed` unless the proof route, not only the
  public statement or ledger metadata, satisfies that contract.

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
- `debt-fix` is the accepted-proof-debt repair entrypoint:
  - runtime reads `proof_obligations.json` for `accepted_as_proof_debt`
  - runtime writes a normal repair request with `repair_trigger = proof_debt`
  - runtime marks legacy clean-completed debt tasks as `COMPLETED_WITH_PROOF_DEBT`
  - the current Codex agent then continues through `review-fix`, `build-check`,
    `review-now --review-subject candidate`, and `review-apply`
  - for large foundation debt, this loop prepares the repair contract; the
    current Codex agent must still build the missing Lean foundation instead of
    expecting the runtime to synthesize it automatically
- Proof-debt repair should follow the textbook proof spine first. Mathlib is
  the formal substrate for low-level facts, measure/topology APIs, and
  source-aligned already-proved results; it should not replace the textbook
  proof with an unrelated high-level shortcut. If a Mathlib theorem discharges
  a source step, record the source-step mapping explicitly in the local wrapper
  or obligation evidence.

Foundation-debt authoring rule:

- Before adding a new theorem-local support object, scan existing foundation
  files, older `ToyApollo/Output` textbook task files, existing bridge files,
  ledger decisions, Mathlib APIs, and nearby downstream tasks for reusable
  structure. The scan is for reusable primitives and source-aligned bridges,
  not permission to bypass the textbook proof spine. The goal is to avoid
  rebuilding the same wheel under different theorem names.
- If the source proof is large, follow the `thm_9_5` pattern: split reusable
  ingredients into focused foundation files, keep any source-spine package
  internal, and remove it from the public theorem once its fields can be
  constructed from proved lemmas.
- If several debt tasks share the same missing bridge, make a shared foundation
  first and then return to the individual task files. Do not patch each task
  with separate opaque support structures.

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

If a dependency is absent from `project_ledger.json` but an official output file
exists under `ToyApollo/Output/<task_id>.lean`, the review context must not leave
that dependency as a bare `UNKNOWN`. It must surface the fallback output file and
top-level declarations, and the reviewer should treat this as a ledger metadata
repair signal rather than as evidence that the mathematical dependency is
missing.

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
- `semantic_review_context_vM.md`
- `semantic_review_result_template_vM.json`
- `semantic_review_result_vM.json`
- `semantic_review_report_vM.md`

The review basis includes `proof_obligations.json` and its summary. Reviewer
results must fill `obligation_review`; a `pass` requires every blocking
obligation to be covered, explicitly not applicable, or explicitly
`accepted_as_proof_debt`, and must have no open scaffold blocker.

The reviewer verdict is `pass`, `fail`, or `inconclusive`.

A valid `pass` must include non-empty source claims, claim mappings from the
source task to the Lean declaration, covered spine alignment, covered proof
obligations, covered interface/downstream adequacy, and explicit forbidden
weakening judgments.

Invalid results such as task-id mismatch, hash mismatch, prompt/rubric version mismatch, missing input linkage, or invalid JSON/schema are normalized into a recorded invalid review result and handled as rejection for candidate review.

## Standard Procedure

### Step 1: Generate or refresh the pack

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
```

Expected result:

- the task directory exists under `phase2_prompt_packs/`
- `draft.lean` exists
- `proof_obligations.json` exists
- build/review runtime metadata is refreshed
- if there is no active official output, ledger state becomes `PACKED`
- if there is an active official output, ledger state remains `COMPLETED`

### Step 2: Read grounding before editing

Read in this order:

1. `failure_summary.md`
2. `proof_obligations.json`
3. `search_manifest.json`
4. `context.md`
5. `imports.lean`
6. `target_stub.lean`

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
- proof obligation coverage and scaffold assessment
- candidate subject against the current build-ready pointer
- official-output subject against the current official output hash

The reviewer should start from `semantic_review_result_template_vM.json` and keep the binding fields unchanged.
Do not run `review-apply` without an explicit `--review-result` path; use the
`expected_result_file` recorded in the current `semantic_review_request_vM.json`.

The template includes `reviewer_schema_hints`; use them when filling a pass
result. The strict pass shape is:

- `spine_alignment.status`, `obligation_review.status`, `interface_contract.status`, and `downstream_adequacy.status` use `covered`, `partial`, `missing`, `violated`, or `unclear`
- `obligation_review.items[*].status` additionally allows `not_applicable` and `accepted_as_proof_debt`
- if direct downstream consumers are listed, `downstream_adequacy.consumers_checked` must contain one object per consumer:
  `{"block_id": "<direct downstream block_id>", "status": "covered|not_applicable|blocked", "evidence": "..."}`
- `forbidden_weakenings[*].status` uses `not_present`, `present`, or `not_applicable`, and a pass cannot mark a forbidden weakening as `present`

Behavior:

- candidate `pass`: promote to official output, run final staged build, then mark `COMPLETED`, or `COMPLETED_WITH_PROOF_DEBT` when accepted proof-debt support remains
- candidate `fail`, `inconclusive`, or invalid: do not promote; mark `review_rejected`; preserve existing official output if one exists; for semantic fail/inconclusive, generate a repair request that carries proof-obligation blockers
- official-output `pass`: reconcile and keep `COMPLETED`, or `COMPLETED_WITH_PROOF_DEBT` when accepted proof-debt support remains
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
  - `COMPLETED_WITH_PROOF_DEBT`
  - `VERIFYING`
- A historical `COMPLETED` task whose `proof_obligation_summary.status_counts.accepted_as_proof_debt > 0`
  should be treated as debt-bearing by `debt-fix`; running `debt-fix` reconciles
  it to `COMPLETED_WITH_PROOF_DEBT` before repair continues.
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
