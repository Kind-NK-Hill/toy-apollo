# Phase2 Candidate Guidelines

This file tells agents how to write Lean candidates. For completion classes and
proof-fidelity verdicts, use `proof_fidelity_contract.md`.

Responsibility: guide Lean authoring choices inside `draft.lean` or a candidate
file. Non-responsibility: semantic review protocol, ledger transitions, or final
classification policy.

## Hard Rules

1. No `sorry`.
2. No Markdown outside comments/docstrings.
3. Do not redefine standard Mathlib objects.
4. Use provided imports unless there is a clear correction.
5. Do not silently strengthen the theorem statement.
6. Do not edit dependency files while working on the current task unless the
   user explicitly scopes that dependency repair.
7. For proof-bearing tasks, inspect the original source proof span before
   judging or writing the candidate.
8. Stay in the build loop until the candidate builds; semantic review comes
   after technical runnability.
9. For `Problem` tasks, stored soft imports are mandatory imports after
   confirmation, not optional hints.

## Construction Preference

Create the smallest stable Lean artifact that captures the task's mathematical
role, builds, exports meaningful declarations, and avoids unnecessary public
surface area.

Prefer, in order:

1. direct reuse of Mathlib objects;
2. direct reuse of `ToyApollo.Output.*` objects;
3. small abbreviations or wrappers;
4. focused theorem/proof specialized to the task;
5. custom definitions or proof packages only when needed.

If a completed local dependency already exports the needed concept or theorem,
import it and use its symbol. Do not copy its proof body into the current file.

## Task Type Notes

For definition tasks, prefer `abbrev`, short `def`, or reusable wrapper names.
Do not shadow Mathlib names or add long proof scripts unless unavoidable.

For theorem tasks, keep statements reusable and source-faithful. Do not change
the theorem statement just to make the proof easier.

For example tasks, formalize the central mathematical conclusion and preserve
the source construction when the example is a worked argument. Do not reduce a
worked example to prose or to a thin wrapper that drops the construction.

For problem tasks, use stored soft imports first and keep the formal statement
focused on the mathematical core.

## Source Fidelity

Textbook fidelity has higher priority than proof shortness. If the source proof
has essential constructions, reductions, partitions, estimates, or limiting
arguments, preserve that proof spine rather than replacing it with a wrapper
that merely implies the conclusion.

Mathlib is allowed for atomic facts, standard APIs, and established lemmas. Do
not use a stronger Mathlib theorem to bypass the textbook route and then label
the result textbook-complete.

## Public Assumptions

Before treating a public theorem as source-faithful, expand local packages used
in its assumptions. Do not hide hard proof steps inside names such as `Setup`,
`SourcePackage`, `Support`, `Bridge`, or local definitions.

Expand textbook concept words before exposing them as public assumptions. A
public theorem may use a canonical textbook or Mathlib interface, or it may use
the minimal formal fields needed to spell the textbook concept. It must not
silently replace a source concept with proof-tool premises such as pointwise
indicator assumptions, kernel estimates, grid-uniformization assumptions, or
other lower-level operational hypotheses unless the theorem is classified as an
interface/operational theorem rather than the final textbook-facing result.

This check applies to all official task output files, not only theorem tasks.
Examples, problems, and definition-adjacent artifacts must not expose hidden
proof packages either.

Fields like `MemLp`, `Integrable`, measurability, or `Tendsto` are not
automatically wrong. They must be source-explicit, necessary formal spellings of
source finiteness/measurability, or internally derived before the final theorem
is called textbook-complete.

## Normal Vs Complex

Use ordinary Phase2 for direct definitions, wrappers, calculations, or one-step
theorem reuse.

Use complex tracking when:

- the source proof has multiple nontrivial obligations;
- the exported statement needs a chain of local helper lemmas;
- local or Mathlib results almost match but require interface conversion;
- downstream tasks rely on the exact exported interface;
- previous attempts show semantic non-progress.

For complex tasks, `proof_obligations.json` is a contract. Split the source
proof into concrete obligations with source references, dependencies, expected
landings, and status. The exported theorem should assemble proved obligations,
not assume them.

The generated `source_proof_spine` entry is only an unresolved placeholder.
`decomposition_plan.md` is a readable companion, not the machine-checked review
basis. The Lean candidate must reconstruct the concrete obligations, not merely
compile a weaker wrapper.

## Before Declaring Blocked

Before classifying a proof-heavy theorem as blocked:

- write down the source proof spine;
- identify the exact missing theorem-level lemma;
- search existing ToyApollo outputs, bridge/foundation files, dependency
  metadata, plans, and Mathlib;
- if an official output exists but the ledger does not know it, repair metadata
  or add the dependency rather than re-proving or re-assuming it;
- record why tempting shortcuts would weaken the source claim.

Hard failure is a last resort, not a label for long proofs. Do not combine
build and review failures into one count; the old hard-stop rule requires one
independent counter to reach its threshold.

## Search, Warnings, And Noncomputability

Use `search_notes.md` and direct local search to confirm theorem names, import
paths, and signatures. Do not guess names when the pack or local search can
settle them.

If the compiler reports an unknown identifier whose name is prefixed by the
current task id, treat it as a missing task-local foundation lemma, not as an
external dependency. Prove the lemma, split it into smaller lemmas, or import a
real existing helper. Do not stop by calling the invented name a hard blocker.

If Mathlib treats an object as noncomputable, mark the relevant declaration
`noncomputable`; do not force a computable definition for cosmetic reasons.

Style, docstring, whitespace, and linter warnings are tolerable. Build failures,
bad imports, unknown identifiers, unresolved elaboration errors, and `sorry` are
not acceptable candidate warnings.
