# Phase2 Proof Fidelity Contract

This is the current policy for deciding what a Lean task has actually
completed. Workflow files explain how to run commands; this file defines the
meaning of completion.

Responsibility: define proof-fidelity verdicts and public-interface standards.
Non-responsibility: command sequencing, repair-loop operation, or case-study
history.

## Completion Classes

- `textbook_proof_completed`: the public statement is source-faithful, public
  assumptions match the source after expansion, the proof follows the source
  proof or construction route at theorem level, and Mathlib is used only as
  local substrate.
- `mathlib_backed_adapter_completed`: the public statement is useful and
  buildable, but the proof is mainly a specialization of stronger Mathlib or
  local infrastructure. This is not textbook proof completion.
- `interface_bridge_completed`: the declaration connects textbook notation to
  Mathlib or existing ToyApollo interfaces. A bridge may support later proofs
  but does not prove unrelated source mathematics.
- `open_math_debt`: a source proof step remains unproved, reassumed, hidden in a
  package, carried by a private axiom, or blocked by a missing theorem-level
  dependency.
- `beyond_book_exception`: the source explicitly places the proof beyond the
  book. The only standing exception is `thm_14_8_ProofBeyondBook`.
- `metadata_only_cleanliness`: metadata, ledger, or audit files look clean, but
  the Lean theorem route has not closed the source mathematics.

Build success is required, but build success alone is never a proof-fidelity
verdict.

## Public Surface

The task-facing theorem must not ask users to provide proof packages.
This rule applies to every official task output file, not only theorem-named
tasks. Examples, problems, and definition-adjacent proof artifacts are included
when they expose task-facing declarations.

- No non-exception public `Support`, `Spine`, `Bridge`, or `ProofBeyondBook`
  parameters may be required to state the task conclusion.
- A lemma may return a `Support` or `Spine` package as an internal constructor.
- A helper theorem that consumes a proof package for final assembly should stay
  private unless its premises are genuine source-facing assumptions.
- `ProofBeyondBook` is allowed only for `thm_14_8_ProofBeyondBook`; downstream
  users must record inherited beyond-book dependence.

## Public Assumption Expansion

Before marking a proof-bearing task `textbook_proof_completed`, expand every
local `def`, `structure`, or package appearing in public theorem assumptions.
Classify each expanded field as:

- source-explicit assumption;
- necessary formal spelling of source finiteness, measurability, or
  integrability;
- internally derived proof ingredient;
- statement strengthening or hidden proof debt.

The first two may appear in a public theorem. The third must be proved inside
the file or imported route. The fourth blocks `textbook_proof_completed`.

Example: `MemLp (X i) 4 P` may spell the source condition
`E[X_i^4] <= c < infinity`. `MemLp (fun w => X i w - mu) 4 P` is hidden
strengthening unless the centered package is derived internally.

Textbook concept words in public assumptions must also be expanded or bound to
a canonical interface before completion is claimed. This is a general rule, not
a special case for any one chapter. Concepts such as distribution/cdf/law, iid,
density, finite moment, tightness, characteristic function, uniform
integrability, stopping time, martingale setup, and conditional expectation may
need formal fields. Those fields are allowed only when they are source-explicit
or necessary formal spelling of the textbook concept. Lower-level operational
premises used to apply a proof tool belong in internal bridge lemmas unless the
task is honestly classified as an operational/interface theorem.

## Obligation Contract

For complex tasks, `proof_obligations.json` is a proof contract. A proved
obligation must identify:

- the source proof step;
- the expected theorem-level Lean statement;
- the actual theorem or lemma landing;
- whether the landing is source-route proof, adapter proof, bridge proof, open
  debt, or beyond-book exception.

`proved` must not land on:

- a structure field projection;
- a support predicate or structure declaration itself;
- a private axiom;
- an empty landing;
- an adapter whose statement does not match the source obligation.

When the schema has contract fields, a blocking obligation cannot be treated as
proved unless these are honestly present:

- `expected_theorem_signature`;
- `proof_contract_status = verified`;
- `signature_match = passed`;
- `body_reassumption_check = passed`;
- `public_premise_check = passed`.

Validators check metadata claims; they do not prove missing mathematics.

The generated `source_proof_spine` placeholder is not a completed
decomposition. Replace it with concrete source-step obligations before claiming
complex-task semantic pass. `decomposition_plan.md` may explain the route, but
`proof_obligations.json` is the machine-facing contract when present.

If contract checks cannot honestly be made, keep the obligation `open`,
`partial`, `blocked`, `obsolete`, or explicitly classified as accepted debt,
adapter, or beyond-book exception as appropriate. Do not fill `verified` or
`passed` merely to satisfy a validator.

## Tracking Levels

- Level 0 ordinary Phase2: build, semantic review, source proof spine,
  interface contract, and downstream adequacy, without a task-local obligation
  ledger.
- Level 1 interface translation: theorem-level adapters for notation or
  representation mismatch; not proof debt.
- Level 2 complex obligation tracking: task-local obligations for independently
  reviewable proof steps, repeated partial progress, downstream-sensitive
  interfaces, or scaffolds that might otherwise hide open mathematics.

## Review Gate

Before calling a proof-bearing task clean, verify:

1. the original source statement and proof span were inspected;
2. earlier outputs, bridge files, dependency metadata, plans, and Mathlib were
   searched before adding new scaffold or debt;
3. the public statement is source-faithful or explicitly classified as adapter;
4. public assumptions were expanded through local packages and extra fields were
   classified;
5. the proof route is honestly classified;
6. public proof-package parameters are absent except for the unique
   `thm_14_8_ProofBeyondBook` exception;
7. obligation landings are theorem/lemma landings, not field projections,
   support declarations, private axioms, or empty names.

For non-theorem task types, apply the same review to their exported
task-facing declarations. Do not exempt a file because its task id is an
example, problem, definition, or bridge.

Use Mathlib freely for atomic formal facts and established APIs. The forbidden
case is using a stronger theorem or adapter to bypass the textbook route while
labeling the result as textbook proof completion.

If a stronger Mathlib or local theorem exactly discharges a source proof step,
the Lean wrapper must make that source-step mapping explicit. Without that
mapping, classify the result as an adapter, not textbook proof completion.

If a candidate fails because it calls an unknown theorem or lemma whose name is
task-local, such as a symbol prefixed by the current task id, this is not an
external hard blocker. It is an unproved local foundation lemma. The worker must
prove it, split it into smaller theorem-level lemmas, import an existing
official helper if one exists, or record the corresponding source obligation.
