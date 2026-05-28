# Phase2 Debt Cleanup Playbook

Use this for repairing accepted proof debt or hidden proof-package interfaces.
For the meaning of completion classes, use `proof_fidelity_contract.md`.

## Cleanup Standard

A task is clean only when:

- the Lean file builds;
- the public task-facing theorem has no forbidden proof-package premise;
- public assumption packages do not hide source proof steps;
- proved obligations land on theorem/lemma declarations;
- metadata and classification match the Lean state.

## Allowed Internal Scaffolds

Internal `Support`, `Spine`, setup structures, or source packages may be useful
while organizing proof. They are acceptable when they are constructed by local
theorems and consumed internally.

They are not acceptable when the public theorem asks the user to provide them.

## Common Hidden Forms

Watch for:

- `axiom`, `constant`, `private axiom`, `sorry`, `admit`;
- a structure field that restates the missing proof step;
- a theorem whose hard premise is the missing statement;
- a public local package containing `Support`, `Spine`, `Bridge`,
  `ProofBeyondBook`, or theorem-specific proof evidence;
- public assumptions that should have been derived internally.

Public assumptions must be expanded. A theorem can have no visible
`Support`/`Spine` parameter and still hide debt inside a `Setup`,
`SourcePackage`, or local definition.

## Repair Pattern

1. Identify the exact public leak or hidden assumption.
2. Locate the source proof step it represents.
3. Search existing ToyApollo outputs and Mathlib.
4. Prove the missing theorem-level lemma or classify the file honestly as
   adapter/open debt.
5. Make the public theorem assemble internal evidence.
6. Update task-local obligations and classification only after Lean proof
   exists.

If several debt tasks share the same missing bridge, estimate, or interface
translation, create a shared foundation theorem first. Do not solve the same
gap repeatedly with task-local support packages.

For large accepted debt, `promote-obligations` may convert blocking
`proof_obligations.json` entries into `Phase2ObligationTask` ledger children.
The parent remains the official output owner. Completed children stay in the
ledger as history; do not delete them just because the parent proof strategy
later changes. If an obligation split is superseded, close or mark the old
child through the ledger path rather than removing the audit trail.

For sibling child obligations under the same parent, do not generate all review
results first and apply later. Applying one child can change the parent's review
basis and make sibling review results stale. Use a fresh review/apply cycle per
child.

## Verification

For a focused task:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Do not edit `project_ledger.json` by hand during cleanup.
