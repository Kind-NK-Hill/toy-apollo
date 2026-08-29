# ToyApollo Formalization Context

ToyApollo formalizes a local probability textbook through source-ingestion,
task planning, Lean output, and independent semantic review. This glossary
names the project-specific boundaries used when organizing Phase 2 output.

## Language

**Textbook Source**:
The local PDF and extracted `inputs/*.tex` files that define the mathematical
authority for a task. A prompt pack is a mirror of this source, not the source.
_Avoid_: prompt source, generated source

**Task Parent**:
The source-facing Lean module for one textbook task, such as a theorem,
example, definition, or problem. A task parent has exactly one task role and
should expose the final statement without owning the proof machinery.
_Avoid_: section file, proof dump

**Proof-Layer Support**:
A task-owned Lean module that carries one coherent layer of a task proof, such
as model setup, finite law calculation, asymptotics, or final assembly. It may
be large when its responsibility is singular and its imports are directional.
_Avoid_: shared support, foundational support

**Interface Support**:
A Lean module or theorem family that translates between textbook-facing
definitions, ToyApollo local conventions, and Mathlib APIs. It is not a local
workaround for a single proof.
_Avoid_: bridge debt, temporary adapter

**Shared Support**:
A reusable Lean module whose declarations are stable across more than one task
family, or are clearly part of a recurring textbook interface. A module is not
shared support merely because extracting it makes one file shorter.
_Avoid_: generic support, utility bucket

**Source-Statement Risk**:
A mismatch where the textbook statement, ToyApollo's current definitions, and
the Lean theorem shape cannot all be accepted without additional hypotheses or
a convention decision. This is a source/interface issue, not ordinary proof
debt.
_Avoid_: hard proof, TODO theorem

**Phase 2 Completion**:
A task-level state landed only through the build, independent semantic review,
and review-apply gates. Lean build success alone is not Phase 2 completion.
_Avoid_: build pass, audit pass

## Example Dialogue

Developer: Should this 70KB proof module move to shared support?

Domain expert: Not unless it has a second real consumer or encodes a stable
textbook interface. If it only supports one problem, keep it as proof-layer
support under that task parent.

Developer: The source theorem seems false under our closed-interval
Riemann-Stieltjes convention. Should I keep trying to prove it?

Domain expert: No. Record it as source-statement risk, keep any corrected
theorem separate, and continue with independent tasks.
