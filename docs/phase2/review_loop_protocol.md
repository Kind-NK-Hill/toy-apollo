# Phase2 Review Loop Protocol

This file summarizes the current semantic review and repair loop. For
proof-fidelity verdicts, use `proof_fidelity_contract.md`.

Responsibility: define review/apply/repair loop behavior, reviewer
independence, freshness, and valid stop reasons. Non-responsibility: Lean
authoring style or proof-completion definitions.

## Composite Actions

- `review-now`: prepares or refreshes a Codex review request for `existing`,
  `candidate`, or current review subject.
- `review-fix`: validates the active repair contract and seeds `draft.lean`
  from the failed-review subject.
- `debt-fix`: creates a proof-debt repair contract, then hands off to the normal
  `review-fix` path.
- `review-apply`: the only supported landing/promotion step for semantic review
  results.
- `auto-loop`: advances same-session review/apply/repair/build state; it is not
  an unattended daemon.

`auto-loop` live state is ledger runtime metadata. Prompt-pack metadata mirrors
that state for display; it is not the source of truth.

## Reviewer Independence

Semantic review is a read-only independent role. For a candidate produced in
the current repair loop, the authoring agent must not review its own candidate.
The orchestrator must use a separate reviewer subagent or a configured external
reviewer runner for the reviewer step.

The reviewer may only read the current review request, input, prompt, context,
template, source, dependencies, candidate, proof obligations, audit signals,
classification history, dependency status, downstream/import evidence, ledger
runtime status, and hash/freshness evidence. It must not edit Lean files,
prompt-pack state, obligations, classification, or ledger state.

Every semantic review result must include `reviewer_independence` with role
`independent_read_only_reviewer`, `read_only = true`,
`did_edit_candidate = false`, and `used_current_review_request = true`.
Missing or false independence evidence is an invalid/inconclusive reviewer
result, not a completion point.

## Same-Session Rule

For chapter, section, or ordered task-set review requests, continue through
review/apply/repair/build in the same session unless the user explicitly asks
for prepare-only behavior.

Do not stop merely because a request was prepared, a repair is needed, or a
candidate failed review. Continue until a documented stop reason exists.

When auto-loop reaches the reviewer step, do not report to the user and stop.
Delegate the review, write the canonical result, run `auto-loop` again, and
continue the same repair loop.

For an ad hoc single-task review, stop after generating the reviewer result
unless the user explicitly asked to land or apply it.

## Freshness And Pass Evidence

Semantic review results are valid only against the current review basis. If a
result predates the current prompt, rubric, template, source basis, or
`review_basis_hash` when present, regenerate a fresh request and redo the
reviewer step. Do not weaken `review-apply` validation to consume stale results.

Candidate build/review is also invalid when the task's official output has moved
ahead of the candidate. If `ToyApollo/Output/<task_id>.lean` is newer than and
different from the latest build-ready `candidate_vN.lean` or active
`draft.lean`, the candidate/current review target is stale. Route the task to
`review-now --review-subject existing`, or explicitly sync the official output
back into `draft.lean` and rerun `build-check` before candidate review.

Invalid reviewer output is not a completion point. Keep the current subject and
same-session state available so the same session can write a corrected review
result.

When a strict review template exists, the reviewer must start from the current
`semantic_review_result_template_vM.json` and keep binding fields unchanged.
Task-id mismatch, subject-hash mismatch, stale prompt/rubric basis, missing
input linkage, invalid JSON, or schema mismatch makes the result invalid. Treat
that as review-result repair or regeneration, not as task completion and not as
a reason to weaken validation.

A pass verdict must give evidence for source claims, proof spine,
interface contract, downstream adequacy, and the full required evidence bundle.
For current strict templates:

- `spine_alignment`, `obligation_review`, `interface_contract`, and
  `downstream_adequacy` must be covered or explicitly not applicable;
- `evidence_review` must cover source TeX, Lean subject, proof obligations,
  audit, classification, dependency status, downstream/import evidence, ledger
  status, and hashes, or explain why a class is not applicable;
- audit, classification, dependency, ledger, or batch evidence cannot decide
  completion by itself; the reviewer must reconcile conflicts in the verdict;
- blocking obligations cannot remain open unless the task is honestly
  classified as accepted debt, adapter, open debt, or beyond-book exception;
- every listed direct downstream consumer needs a downstream-adequacy entry;
- forbidden weakenings must be absent or not applicable, not present.

For complex tasks, when `decomposition_plan.md` or
`decomposition_plan.json` exists, the reviewer should read it as the human
route narrative and check that it agrees with `proof_obligations.json`. The
obligation JSON remains the machine-facing review basis. A pass still requires
the candidate to reconstruct concrete obligations; compiling a weaker wrapper
or accepting a new black-box obligation for a source proof step is a fail.

Schema-constrained statuses matter. Top-level review gates use `covered`,
`partial`, `missing`, `violated`, or `unclear`; obligation items may also use
`not_applicable` or `accepted_as_proof_debt`; forbidden weakenings use
`not_present`, `present`, or `not_applicable`.

## Stop Reasons

Only these are valid same-session stops:

- `completed`
- `freshness_error`
- `hard_failure`
- `nonprogress`
- `max_rounds`
- `build_budget_exhausted`
- explicit user interruption

`hard_failure` requires source proof-spine decomposition, dependency search, a
specific blocker, and retry-budget evidence when applicable. Large proof size is
not a hard failure.

An unknown identifier is not automatically a hard blocker. If the missing symbol
is task-local, for example prefixed by the current task id, the current
candidate has introduced an unproved foundation lemma. Continue the normal
repair loop by proving or splitting that lemma, or by importing a real existing
helper. Only missing external public APIs, shared bridges, upstream outputs, or
Mathlib symbols may be treated as dependency blockers after search.

Every `hard_failure` must leave a task-local `hard_failure_note.md` or
equivalent review artifact explaining the blocker and why tempting shortcuts
would weaken the source claim.

For a proof task that is still in the normal repair loop, `hard_failure` is not
valid merely because several attempts failed. The hard-stop threshold is one of:

- `phase2_build_fail_counter >= 15` for consecutive failed build checks before
  a successful build;
- `phase2_review_fail_counter >= 15` for failed or inconclusive semantic
  reviews of build-ready candidates.

Do not add build failures and review failures together. Stale review refreshes,
dependency-failed skips, setup failures, timed-out runs, or manually aborted
runs without canonical result files are mechanism or dependency states, not
substantive proof failures.

`nonprogress` is semantic non-progress: the same semantic failure fingerprint or
unchanged candidate content has repeated, so the repair strategy must change.

## Apply Outcomes

For candidate review, a pass may promote the candidate to official output. A
fail, inconclusive, invalid, or stale result must not promote it; preserve any
existing official output and keep the task in the repair path.

Do not answer a review failure by regenerating the same review request
unchanged. Either revise the candidate through `review-fix` and the build loop,
or explicitly audit the existing official output under a fresh review basis.

For official-output review, a fail records review failure, repair-required
metadata, and the failed-review repair path by default. It must not quarantine
official output or demote the task by default, because removing official output
can break downstream imports before the repair is ready.

Quarantine of official output is an explicit opt-in destructive maintenance
action, not the default apply outcome. Before opt-in quarantine, check direct
downstream consumers and imports, then record the decision and expected repair
route. Prepare-only queue modes never quarantine by themselves.

## Accepted Proof Debt

`COMPLETED_WITH_PROOF_DEBT` is completed-but-not-clean. Downstream hard
dependents remain blocked until the debt-bearing task is repaired cleanly.

Use:

```text
debt-fix -> review-fix -> build-check -> review-now --review-subject candidate -> review-apply
```

The authoring step must replace debt with theorem-level evidence, honest
adapter classification, open debt, or the unique beyond-book exception.
