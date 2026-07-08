# Phase2

Phase2 turns one task candidate into an official ToyApollo output only through
three completion gates:

1. Build gate: the candidate must build.
2. Semantic review gate: an independent read-only reviewer judges textbook
   fidelity.
3. Apply gate: `review-apply` may land completion only when the task-level
   `phase2_status` is `pass`.

Lean build success is not theorem completion. A reviewer verdict of `pass` is
not task completion by itself. The review result must also carry a `proof_class`
that projects through the source task role to `phase2_status=pass`.

Some route-risk tasks have a separate pre-author Math Review Gate. That gate
requires a natural language proof skeleton plus an independent three-round math
review with verdict `go` before Lean author/build may start. Its `stop` verdict
is a correct stop signal for rewrite planning, not a completion result.

## Default Workflow

Use the normal path in [workflow.md](workflow.md):

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
# edit phase2_prompt_packs/<task_id>/draft.lean
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
```

For Math Review Gate tasks, insert:

```text
natural language proof skeleton -> xhigh independent math review, 3 rounds -> theorem-shape go/stop
```

between `pack` and editing `draft.lean`. `build-check` enforces this for the
triggered tasks.

For an already buildable official output, use `review-now --review-subject
existing`, then `review-apply`. A failed existing-output review does not
quarantine official output by default.

For repair after a failed or inconclusive semantic review, use `auto-loop`
instead of a hand-written loop. The runtime default and CLI floor are 15 review
rounds and 15 build-check attempts before each review round. A precise blocker
is repair evidence, not a completion state, unless it is recorded through
`review-apply` and no independent task remains in the current goal.

## Stable Entry Points

- [workflow.md](workflow.md): the default operator path.
- [status_contract.md](status_contract.md): `phase2_status`, `proof_class`,
  task roles, and pass/fail/blocked rules.
- [review_criteria.md](review_criteria.md): strict semantic review criteria.
- [artifacts.md](artifacts.md): authority files versus cache/report/history.
- [tools.md](tools.md): short notes for diagnostics-only tools.
- [output_auxiliary_modules.md](output_auxiliary_modules.md): classification
  for non-task `ToyApollo/Output` support, bridge, family-member, and retired
  build-probe modules.
- [../interface_dependency_policy.md](../interface_dependency_policy.md): the
  textbook-first, bridge-then-Mathlib policy for shared mathematical
  interfaces.
- [rs_stieltjes_boundary.md](rs_stieltjes_boundary.md): containment rules for
  Chapter 1 Riemann-Stieltjes core, problem support, and later LS-RS bridges.

## Non-Default Material

The `archive/` directory contains historical runbooks, status snapshots,
classification policy notes, debt cleanup notes, and old review-loop docs. They
are useful evidence, not default Phase2 entry points.
May 2026 step/rescue records under the root archive are historical material, not
an operator path.

## Core Rule

Only the apply gate can land clean completion, and only with
`phase2_status=pass`. Ledger rows, audit reports, classification files, batch
state, validation tools, proof obligations, verify reports, and old prompt-pack
artifacts are evidence or diagnostics. They do not independently complete a
task.
