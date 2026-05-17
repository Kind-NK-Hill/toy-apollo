# Phase 2 Review Loop Protocol

This document carries the expanded runtime/operator protocol for the Phase 2 Codex semantic-review loop.

## Composite Actions

- `review-now` prepares or refreshes the current Codex review request for `current`, `existing`, or `candidate`.
- `review-fix` validates the active review-repair contract and seeds `draft.lean` from the bound failed-review subject.
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
- This does not change `review-now`, `review-apply`, `review-fix`, or `auto-loop` semantics.
- When strict reviewer evidence is missing or stale, the correct recovery is to regenerate a fresh request and redo the reviewer step, not to weaken apply-time validation.
- Invalid reviewer output is not a normal completion point; current review subject metadata and same-session auto-loop state should remain available so the same session can continue with a corrected reviewer result.

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
Bridge lemmas are acceptable only when they resolve an interface mismatch
between the source proof and an existing theorem. They are not acceptable when
they merely rename an unproved analytic obligation or the task's main theorem.

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
