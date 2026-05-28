# Phase2 Classification Policy

Use this file when updating `docs/phase2_completion_classification.json` and
`docs/phase2_completion_classification.md`.

## Source Of Truth

Classification records proof-fidelity state. It is ledger-independent.
`project_ledger.json` is runtime bookkeeping and must not be used as the sole
evidence that a theorem is proof-complete.

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

The validator checks consistency. It does not replace Lean build or
source-route review.
