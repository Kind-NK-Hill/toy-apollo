# Phase2 Proof Fidelity Contract

This is the stable proof-fidelity contract for Phase2 work. It is shorter than
the workflow runbook on purpose: use this file to decide what a Lean task has
actually completed, then use the workflow docs for how to run the tools.

## Authority

This file is current policy. Step documents under `docs/modification_0525_steps/`
are execution records and design notes, not runtime policy unless a rule is
copied here or implemented by a current tool.

## Completion Classes

Use these labels when judging a proof-bearing task:

- `textbook_proof_completed`: the public statement is source-faithful, the proof
  body follows the source proof or construction route at theorem level, and any
  Mathlib usage is local substrate rather than a shortcut around the source
  argument.
- `mathlib_backed_adapter_completed`: the public statement is useful and
  buildable, but the main proof is a specialization or adapter around stronger
  Mathlib or local infrastructure. This is valid Lean work, but it is not
  textbook proof completion.
- `interface_bridge_completed`: the file or declaration honestly connects a
  textbook-style object to a Mathlib or existing ToyApollo interface. A bridge
  may support later proofs, but it is not itself proof of unrelated source
  mathematics.
- `open_math_debt`: a source proof step remains unproved, reassumed, represented
  by a private axiom, hidden behind a support package, or blocked by a missing
  theorem-level dependency.
- `beyond_book_exception`: the source explicitly places the proof beyond the
  book. The only standing project exception is `thm_14_8_ProofBeyondBook`.
- `metadata_only_cleanliness`: ledger, audit, or obligation files look clean but
  the Lean theorem route has not actually closed the source mathematics.

Do not collapse these classes into `builds` or `COMPLETED`. Build success is a
technical gate, not a proof-fidelity verdict.

When a classification artifact is in scope, keep its vocabulary consistent with
`docs/phase2_completion_classification.md` and
`docs/phase2_completion_classification.json`. Those files record current corpus
status; this contract defines the meaning of the stable classes.

## Public Surface Rules

The public task-facing interface must not expose proof packages as user
obligations.

- A public declaration may not require non-exception `Support`, `Spine`,
  `Bridge`, or `ProofBeyondBook` parameters to state the task conclusion.
- A lemma that proves and returns a `Support` or `Spine` package is allowed as an
  internal or helper proof-constructor.
- A helper theorem that consumes a proof package only for final assembly should
  stay private unless its premises are genuine textbook-facing assumptions.
- `ProofBeyondBook` is allowed only for `thm_14_8_ProofBeyondBook`. Direct
  downstream users must record inherited beyond-book dependence instead of
  pretending the obligation is ordinary proved debt.

## Obligation Contract

For complex tasks, `proof_obligations.json` is a proof contract, not a scratch
note. Each source obligation that can be marked proved should identify:

- the source proof step it represents;
- the expected theorem-level Lean statement, recorded as
  `expected_theorem_signature` when the schema supports it;
- the actual theorem or lemma landing;
- whether the landing is source-route proof, adapter proof, bridge proof, open
  debt, or beyond-book exception.

`proved` means a theorem or lemma proves the source obligation. It must not land
on:

- a structure field projection such as `SomeSourceSpine.some_field`;
- a support predicate or structure declaration itself;
- a private axiom;
- an empty landing;
- an adapter whose statement does not match the source obligation.

When the current schema does not yet have `expected_theorem_signature` or
`proof_contract_status`, record the same information in the nearest review or
classification artifact and do not promote the task to
`textbook_proof_completed`.

## Tracking Levels

Phase2 has three tracking levels:

- Level 0, ordinary Phase2: default path. Build, semantic review, source proof
  spine, interface contract, and downstream adequacy are checked without adding
  a new task-local obligation ledger.
- Level 1, interface translation: theorem-level adapters connect textbook
  notation, Mathlib, and existing ToyApollo declarations. These adapters are not
  proof debt.
- Level 2, complex obligation tracking: use `proof_obligations.json` only when
  the task has independently reviewable source proof steps, repeated partial
  progress, downstream-sensitive interfaces, or scaffold that could otherwise
  hide open mathematics.

## Source And Dependency Discipline

For proof-bearing work, inspect the original `inputs/<source>.tex` statement and
proof or solution span before authoring, reviewing, or declaring a blocker.
Prompt-pack mirrors are useful, but they are not a substitute for the source.

Before adding a new helper obligation, scaffold, bridge, or debt item, scan:

- existing `ToyApollo/Output/*.lean` files, including older chapters;
- local bridge and foundation files;
- dependency decisions and relevant plans;
- `project_ledger.json` and task-local prompt-pack metadata;
- Mathlib APIs and already imported local helpers.

If an existing output covers the source step, reuse it or repair metadata. Do
not create a new black-box bridge for mathematics that is already available.

## Accepted Proof Debt Lifecycle

`accepted_as_proof_debt` and `COMPLETED_WITH_PROOF_DEBT` mean the task is
buildable with explicit debt, not clean. Such a task is not a clean upstream
dependency. Downstream hard dependents remain blocked until `debt-fix` repairs
the task and the repaired candidate passes semantic review without accepted
debt.

`debt-fix` is a workflow entrypoint, not a proof. It creates the repair contract;
the authoring step must replace the accepted debt with theorem-level evidence,
an honest adapter classification, a documented open-debt state, or the single
beyond-book exception.

## Complex Decomposition

For complex tasks, the generated `source_proof_spine` placeholder is not a
completed decomposition. Replace it with concrete source-step nodes before
claiming semantic pass, hard failure, or dependency-failed downstream status.

`decomposition_plan.md` may be a readable companion, but
`proof_obligations.json` is the machine-facing contract when present. The final
public theorem should assemble proved obligations into the source claim rather
than exposing the hard obligations as theorem parameters.

## Hard Failure Admission

`hard_failure` is a last-resort semantic stop, not a label for long proofs or
missing one-shot theorems. It requires:

- source TeX inspection when a proof or solution exists;
- source proof-spine decomposition into concrete obligations;
- search evidence across local outputs, bridge files, dependency metadata, and
  Mathlib;
- a specific blocking obligation;
- a task-local note explaining why faithful completion is beyond the current
  local workflow and why tempting shortcuts would weaken the source claim.

For retried complex tasks, ordinary build or review failures must follow the
active retry-budget rules in the workflow docs.

## Review Gates

Before calling a proof-bearing task clean, verify:

1. the original `inputs/<source>.tex` statement and proof span were inspected;
2. local earlier outputs and bridge files were searched before adding new
   scaffold or debt;
3. the public statement is source-faithful or explicitly classified as an
   adapter;
4. the proof route is classified honestly as textbook route, Mathlib-backed
   adapter, bridge, open debt, or beyond-book exception;
5. public proof-package parameters are absent except for the single
   `thm_14_8_ProofBeyondBook` exception;
6. obligation landings are theorem/lemma landings, not field projections,
   support declarations, private axioms, or empty names.

Use Mathlib freely for atomic formal facts and established APIs. The forbidden
case is not Mathlib usage; it is using a stronger Mathlib theorem or local
adapter to bypass the textbook route while labeling the result as textbook proof
completion.

## Enforcement

Use the contract together with current tools:

- `tools/audit_phase2_clean_debt_surface.py` checks public proof-package surface
  and the unique beyond-book exception.
- `tools/validate_phase2_completion_classification.py` checks completion
  classification artifacts when they are part of the current work.
- Lean build checks remain mandatory for touched Lean-facing files, but build
  success alone never decides proof-fidelity class.
