# Phase 2 Review Loop Protocol

This document carries the expanded runtime/operator protocol for the Phase 2 Codex semantic-review loop.
For proof-fidelity verdicts, adapter/debt classification, and public
proof-package surface rules, use `docs/phase2_proof_fidelity_contract.md`.

## Composite Actions

- `review-now` prepares or refreshes the current Codex review request for `current`, `existing`, or `candidate`.
- `review-fix` validates the active review-repair contract and seeds `draft.lean` from the bound failed-review subject.
- `debt-fix` creates a review-repair contract for accepted proof debt and then hands off to the normal `review-fix` authoring path.
- `auto-loop` advances same-session review/apply/repair/build runtime state, but the current Codex agent still performs authoring and reviewer work.

## Hard Invariants

- `review_basis_hash` is the semantic freshness gate for Codex review materials.
- `review-apply` is the only landing/promotion step for Codex semantic-review results.
- `auto-loop` is never an unattended daemon or background reviewer.
- Build-fail and review-prepared states are not ordinary waiting points; the current Codex agent must continue in the same session.
- `nonprogress` is a semantic stop reason: it means the same semantic failure fingerprint or unchanged candidate content repeated across rounds.

## Same-Session Expectations

- In reviewer mode, the current Codex agent reads `semantic_review_request.json` and writes the canonical `semantic_review_result_vM.json`.
- In repair mode, the current Codex agent edits `draft.lean` against the active repair contract, not against a generic build error summary.
- In active same-session loop mode, the current Codex agent must not convert a reviewer/repair checkpoint into a completion-style handoff or status-only ending.
- Before ending the turn, check the live ledger metadata first. If `current_auto_loop_status = active` and no documented stop reason is present, continue the required reviewer or repair step in the same session.
- "This repair is large", "I should explain the blocker first", and "the current Codex agent still needs to write the review result or edit `draft.lean`" are not valid stop conditions.
- If the user did not ask for landing/apply behavior, stop after generating the reviewer result and report the verdict plus result path.
- Only continue automatically to `review-apply` when the user explicitly asked for landing/apply behavior and the verdict is `pass`.

## Strict Reviewer Contract Upgrades

- Prompt, rubric, template, and review-basis upgrades may invalidate older semantic review artifacts through freshness gates.
- This does not change `review-now`, `review-apply`, `review-fix`, `debt-fix`, or `auto-loop` semantics.
- When strict reviewer evidence is missing or stale, the correct recovery is to regenerate a fresh request and redo the reviewer step, not to weaken apply-time validation.
- Invalid reviewer output is not a normal completion point; current review subject metadata and same-session auto-loop state should remain available so the same session can continue with a corrected reviewer result.

## Accepted Proof-Debt Repair

Use `docs/phase2_proof_fidelity_contract.md` for the semantic meaning and
lifecycle of accepted proof debt. The runtime protocol is:

`COMPLETED_WITH_PROOF_DEBT` is a completed-but-not-clean state. It should not
be consumed as an ordinary completed dependency. Downstream hard dependents are
blocked as `DEPENDENCY_PROOF_DEBT` until the debt-bearing task is repaired, and
normal `pack`, `build-check`, `review-now`, `auto-loop`, and soft-dependency
selection entrypoints must refuse work that would carry that debt forward.

Use `debt-fix` when either condition holds:

- the task status is `COMPLETED_WITH_PROOF_DEBT`
- the task is an older `COMPLETED` task but `proof_obligations.json` or the
  ledger proof-obligation summary records `accepted_as_proof_debt`

`debt-fix` does not prove anything by itself. It creates a normal
`review_repair_request_vM.json` with `repair_trigger = proof_debt`, clears any
active review request, and seeds the next `review-fix` cycle from the official
output or latest official snapshot. After that, use the standard
`review-fix -> build-check -> review-now --review-subject candidate ->
review-apply` loop.

For large proof debt, the repair loop is only the contract and state machine.
The authoring step must build the missing foundation explicitly. Before creating
a new foundation/API:

- keep the textbook proof spine as the controlling decomposition;
- scan existing `ToyApollo/Output` foundation files, older textbook task files,
  bridge files, ledger decisions, Mathlib APIs, and downstream debt tasks for
  similar source-aligned bridges;
- use Mathlib as the formal substrate for atomic facts and APIs, not as a
  black-box replacement for the source proof;
- prefer a shared foundation file over repeated theorem-local support objects;
- use the `thm_9_5` style when applicable: focused foundation layers first,
  final theorem assembly last, and no public source-spine/support parameter in
  the clean theorem.

## Existing-Output Batch Requests

- When the user asks to review an existing chapter, section, or ordered task set, interpret that request as a same-session self-driving existing-output batch by default.
- In that batch mode:
  - always start from `review_subject=existing`
  - never silently fall back to `current`
  - process tasks in deterministic `block_id` order
  - do not treat build-fail, review-prepared, or repair-ready states as ordinary pause points; the current Codex agent continues the required author/reviewer step in the same session
  - apply pass results automatically
  - route fail/inconclusive results through `review-apply -> review-fix -> build-check -> review-now --review-subject candidate -> review-apply`
- Only downgrade an existing-output batch request to prepare-only behavior when the user explicitly says to only inspect or prepare review materials.

## Examples

- User: `帮我 review existing chapter2 的 tasks`
  - interpret this as an existing-output batch request
  - use `review_subject=existing`
  - walk Chapter 2 formal tasks in `block_id` order
  - continue same-session author/reviewer work without asking for confirmation after each task
  - stop early only on `freshness_error`, `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption

## Stop Reasons

Only stop the same-session loop on:

- `completed`
- `freshness_error`
- `hard_failure`
- `nonprogress`
- `max_rounds`
- `build_budget_exhausted`
- explicit user interruption

Everything else is continuation work, not a pause point. In particular, review-prepared, repair-ready, authoring-required, and reviewer-required states must stay inside the same-session loop until one of the stop reasons above is reached.

`hard_failure` is only valid after the task satisfies the admission criteria in
`docs/phase2_prompt_pack_workflow.md`: original TeX proof inspection when
available, source proof-spine decomposition, search/attempt evidence for the
blocking obligation, and a task-local hard-failure note or equivalent artifact.
Do not treat "large proof", "needs decomposition", or "no one-shot theorem was
found" as `hard_failure`.

For complex tasks, the reviewer must also check the task-local
`decomposition_plan.md` or `decomposition_plan.json` when present. A semantic
pass requires the candidate to reconstruct the listed obligations; compiling a
weaker wrapper or assuming the difficult obligations is a fail.
The reviewer should also verify that the candidate/decomposition has searched
and reused existing `ToyApollo/Output` declarations before accepting a new
black-box obligation for a source proof step.
Interface-translation lemmas are acceptable only when they resolve an interface
mismatch between the source proof and an existing theorem. They are not
acceptable when they merely rename an unproved analytic obligation or the
task's main theorem. Explicit proof-debt support must be classified separately
as `proof_debt_support`, not as an interface translation. If review accepts
that support for a task, record the obligation status as
`accepted_as_proof_debt`; this is an auditable debt marker, not a claim that the
underlying theorem has been proved.

If a complex task is being retried after an under-evidenced hard stop, the loop
must not accept another `hard_failure` until the renewed attempt has either
completed or one of the two hard-coded counters reaches 15:

- `phase2_build_fail_counter >= 15`: consecutive failed `build-check` attempts
  before semantic review. A successful `build-check` resets this counter to `0`.
- `phase2_review_fail_counter >= 15`: failed or inconclusive semantic reviews
  of build-ready candidates. A successful build makes review eligible; it does
  not itself increment the review counter.

Build failures and review failures are not additive. The task fails only when
one counter independently reaches 15. Pure setup/configuration failures,
dependency-failed skips, stale review refreshes, and timed-out or manually
aborted build/review attempts with no canonical result file do not increment
either counter; record those as mechanism blockers or continuation work and
resume the renewed attempt.
