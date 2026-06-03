# Phase2 Classification Policy

Use this file when updating `docs/phase2_completion_classification.json` and
`docs/phase2_completion_classification.md`.

## Source Of Truth

Classification is ledger-independent review evidence and a reporting cache. It
does not independently decide completion. The latest valid semantic review
result is the proof-status verdict; classification history must be read by the
reviewer and reconciled with that verdict.

`project_ledger.json` is runtime bookkeeping and must not be used as the sole
evidence that a theorem is proof-complete. Classification files likewise must
not be hand-written as a substitute for build + review + apply.

## Promotion Requirements

Promote a proof-bearing task to `textbook_proof_completed` only when:

- the Lean file builds;
- the public statement is source-faithful;
- public assumptions have been expanded and checked;
- the source proof route lands on theorem/lemma evidence;
- task-local obligations, when present, have verified contract fields;
- no private axiom, public proof package, or equivalent hidden premise remains.

Adapter and bridge completions are valid, but do not promote them to textbook
proof completion.

When reporting task-level pass/fail/blocked, do not use `review_verdict=pass`
directly. Project the review result through the source task role:

- theorem, problem, and exercise tasks require `textbook_proof_completed` or a
  stricter source-route completion class to count as task-level pass;
- definition tasks require a source-faithful definition completion;
- a definition or notation task whose source explicitly defines one object by
  an existing interface may pass as a source-faithful definition bridge;
- `interface_bridge_completed` is acceptable task-level pass only for such
  explicit definition/interface/notation tasks, not for ordinary
  proof-bearing targets;
- `mathlib_backed_adapter_completed` is not task-level pass for proof-bearing
  textbook targets.

Example: Definition 13.5 is a source-faithful definition bridge because the
textbook itself defines `P(A | X)` as `E[1_A | sigma(X)]`. A theorem or problem
using a bridge to avoid its source proof route must remain non-clean.

Runtime projection is implemented by `src/toy_apollo/phase2_task_status.py`.
`review-apply` records `phase2_review_verdict`, `phase2_proof_class`,
`phase2_completion_class`, `phase2_task_status`, and
`phase2_task_status_reason`. Batch reports must display `review_verdict` and
`task_status` separately. If a pass review lacks `proof_class` or
`completion_class`, keep the review as historical evidence but set
`needs_class_normalization`; it cannot count as task-level pass until a fresh
classified review result exists.
`review-apply` must not write ordinary clean `COMPLETED` for a pass review whose
projected task status is not `pass`; such an apply result is non-clean and must
remain visible to batch/reporting gates.

For a task explicitly selected as a textbook-complete target, keep
`textbook_proof_completed` as the success criterion. Intermediate landings such
as `foundation_lemma_landed`, `bridge_landed`, or `contract_clean` may appear in
reports, but they must not be written as the final classification for that
selected target. If the target still cannot close, record
`hard_blocked_with_failed_lean_attempt` evidence or an actual statement patch;
do not silently relax the target into adapter/open-debt status.

## Downgrade Requirements

Downgrade or keep a task open when:

- a hard proof step is carried by a public premise;
- a local package contains a hidden source proof obligation;
- a proved obligation lands on a field projection, support declaration, private
  axiom, or empty name;
- the proof route is mainly a stronger Mathlib/local adapter;
- public assumptions are stronger than the source without an accepted statement
  decision.

## Current Artifacts

- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`

Run:

```powershell
python tools/validate_phase2_completion_classification.py --require-proof-contract
```

The validator checks consistency. It does not replace Lean build, semantic
review, or source-route review, and it must not be used as an independent
completion gate.
