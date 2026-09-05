# Riemann-Stieltjes Boundary

This note preserves the historical diagnosis and repair boundaries for the
Chapter 1 Riemann-Stieltjes files. The diagnosis, debt inventory and repair order
below describe the earlier implementation, not a current task queue or completion
verdict. The current import structure is distinguished in the impact section.
The normal Phase2 build, semantic review, and apply gates still decide task status.

This is the Riemann-Stieltjes instance of
[textbook-first, bridge-then-Mathlib](../interface_dependency_policy.md).

## Historical Diagnosis

`ProbabilityTheory/chapter_01/def_1_2.lean` grew because it replaced the old
axiom-backed interface with a source-faithful Darboux upper/lower and tagged
sum core. That direction is acceptable for Definition 1.2 and Theorem 1.3
style properties, but it should not absorb later examples, problem
calculations, or Lebesgue-Stieltjes theory.

The retired pre-cutover `rs_stieltjes_bridge.lean` module historically grew because it became
a holding file for four different kinds of work:

- reusable Mathlib/Stieltjes measure wrappers;
- finite-interval Darboux RS support duplicated or extending `def_1_2`;
- Chapter 1 example and Problem 1.8 floor/jump calculations;
- Chapter 7 and future Lebesgue-Stieltjes/improper/probability bridge axioms,
  now retired to tombstone modules.

That mixed ownership motivated the boundaries below. The retired
`rs_stieltjes_bridge.lean` should not be recreated as a catch-all module. Search
Mathlib and current local support for an explicit bridge before adding another
implementation of the same RS fact.

## Ownership

`def_1_2.lean` should own:

- textbook partition, upper sum, lower sum, tagged sum interfaces;
- the Definition 1.2 integrability predicate and guarded integral value;
- first core algebra/order facts needed immediately after the definition:
  integrand additivity, scalar multiplication, integrator additivity, and
  monotonicity, when proved from the Darboux/tagged formulation.

Reusable RS/Stieltjes bridge files should own:

- `StieltjesFunction` and monotone-integrator measure wrappers;
- finite interval integrability as Lebesgue integrability against the
  associated Stieltjes measure;
- explicit equivalence theorems between the textbook Darboux RS interface and
  Mathlib Lebesgue/Stieltjes APIs.

Chapter 1 problem support should own:

- one-jump step-integrator calculations used by Example 1.3.1;
- finite floor-function decompositions for Problem 1.8;
- concrete algebraic evaluations such as the `[0,10]` square/floor and
  `[0,2]` sqrt/floor computations.

Chapter 7 or future bridge files should own:

- finite LS-to-RS theorem statements for Stieltjes functions;
- whole-line improper RS versus Lebesgue-Stieltjes integrability;
- completion compatibility for Stieltjes measures;
- probability expectation/density reduction theorems.

## Historical Debt Classification

At the time of this diagnosis, these names had been removed from the active
Chapter 1 public axiom surface:

- `rsIntegrable_of_bounded_finite_discontinuities`, replaced by proof-bodied
  Theorem 1.1 support;
- `rsIntegral_sqrt_floor_add_id_0_2`, replaced by proof-bodied Problem 1.8(b)
  support;

The following names then required task-owned repair or blocker evidence. Their
presence in this historical inventory does not assert an unresolved task today:

- `rsIntegral_eq_integral_deriv` and `rsIntegral_integration_by_parts`, because
  downstream files historically called those names;
- `rsIntegrable_interval_concat` and `rsIntegral_interval_concat` for Theorem
  1.2 need blocker evidence before repair. The raw PDF states the interval
  concatenation clause without an extra endpoint-continuity condition, but under
  the current closed-interval Darboux definition the unconditional statement is
  unsafe when `alpha` and `f` jump together at the split point.

Retired from `ProbabilityTheory` as public axiom debt. Do not re-export or wrap
these old bridge names as completion evidence:

- `lsIntegral_eq_rsIntegral_stieltjesFunction`;
- `improperRS_abs_iff_integrable_abs_stieltjes`;
- `expectation_eq_integral_density_of_stieltjes_deriv`;
- `rsIntegrable_iff_ae_continuous_stieltjes`;
- `rsIntegrable_completion_integral_eq`.

The corresponding compatibility modules are tombstones only. Problem 7.3 has
proof-bodied task support for its completion claims. The old Theorem 7.9 and
7.12 bridge signatures were under-specified; future public wrappers for those
routes need source-facing hypothesis packages plus the Math Review Gate.

## Historical Repair Order

These were the proposed intervention steps for the implementation diagnosed
above. Inspect current declarations, support and review evidence before applying
them; do not infer that any listed repair remains outstanding.

1. Keep `def_1_2.lean` focused on the textbook Darboux/tagged interface and
   the first core RS laws already proved there.
2. Split Chapter 1 example/problem support out of `rs_stieltjes_bridge.lean`
   only when editing those proofs anyway; do not delete the proof work.
3. Keep the Chapter 7/future LS-RS compatibility modules as no-declaration
   tombstones. Do not restore the old bridge-debt names as wrappers; future
   public LS-RS support needs source-facing hypothesis packages plus the Math
   Review Gate.
4. Do not attempt an unconditional interval-concatenation repair for Theorem
   1.2. First record a source-route mismatch/blocker note against the raw PDF
   and current Darboux definition. A corrected lemma with endpoint-continuity or
   no-common-jump hypotheses may be useful support, but it cannot by itself land
   the original Theorem 1.2 clause as clean pass.
5. After the Theorem 1.2 blocker is recorded, continue only with independent
   repairs that do not depend on the false unconditional concat surface. The
   Theorem 1.1 finite-discontinuity route and Problem 1.8(b) sqrt/floor route
   already have proof-bodied support and should stay guarded against regression.
6. Prefer Mathlib interval/Lebesgue/Stieltjes APIs through explicit bridge
   theorems whenever the source proof is intentionally textbook-level but not
   meant to rebuild measure theory.

## Theorem 1.2(4) Impact Boundary

The earlier review context reported no direct downstream consumer. That is not
the current repository structure. As inspected on 2026-09-05, the module
`ProbabilityTheory.chapter_01.thm_1_2` is directly imported by
`def_1_3.lean`, `Ex_1_3_2.lean`, `rs_stieltjes_darboux_support.lean`,
`thm_1_1_basic.lean`, `thm_1_2_4.lean`, `thm_1_2_glue_support.lean`, and
`thm_1_4.lean` under `ProbabilityTheory/chapter_01/`.

An import establishes a module dependency, not use of a particular
interval-concatenation clause. Inspect declaration-level uses and the affected
support before deciding the impact of a proposed change; the old zero-consumer
observation cannot establish today's impact boundary.

The clause is still conceptually important. It is the textbook-level interval
localization/additivity property one would use for piecewise RS calculations.
The closest later source use is the Chapter 7 practical-calculation discussion:
piecewise-continuous integrands can be handled by dividing the real line into
pieces when discontinuities of the integrand and the Stieltjes function do not
overlap. That later use matches a corrected/safe interval-concatenation theorem,
not the unconditional local-to-global clause under the mesh-limit definition
discussed in the historical diagnosis.

Do not treat Theorem 1.2(4) as useless, and do not treat it as a global blocker.
Record it as a source/definition convention issue and continue with tasks that
do not depend on the unsafe unconditional local-to-global implication.

## Author confirmation (2026-07)

The retained July correspondence note records that textbook author Kenneth
Shum acknowledged the counterexample and a missing assumption. That note treats
Option A (α continuous at c, or f continuous at c) as an inferred correction
direction; it does not record explicit approval of that exact option. Its
record-only `allowed_exception` status and “not re-run” statement describe the
July update, not the current task status. No new mathematical review or status
change is asserted here. Full historical note:
`docs/phase2/author_errata_confirmations_2026-07.md` in the full local workspace
(retained source evidence, excluded from the public release).
