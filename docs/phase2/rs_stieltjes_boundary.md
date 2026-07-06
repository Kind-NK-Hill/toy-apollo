# Riemann-Stieltjes Boundary

This note records the current Phase2 boundary for the Chapter 1
Riemann-Stieltjes files. It is a containment rule for repair work, not a
completion verdict. The normal Phase2 build, semantic review, and apply gates
still decide task status.

This is the Riemann-Stieltjes instance of
[textbook-first, bridge-then-Mathlib](../interface_dependency_policy.md).

## Current Diagnosis

`ToyApollo/Output/def_1_2.lean` grew because it replaced the old
axiom-backed interface with a source-faithful Darboux upper/lower and tagged
sum core. That direction is acceptable for Definition 1.2 and Theorem 1.3
style properties, but it should not absorb later examples, problem
calculations, or Lebesgue-Stieltjes theory.

`ToyApollo/Output/rs_stieltjes_bridge.lean` historically grew because it became
a holding file for four different kinds of work:

- reusable Mathlib/Stieltjes measure wrappers;
- finite-interval Darboux RS support duplicated or extending `def_1_2`;
- Chapter 1 example and Problem 1.8 floor/jump calculations;
- Chapter 7 and future Lebesgue-Stieltjes/improper/probability bridge axioms,
  now retired to tombstone modules.

The current direction is therefore partially right but badly organized. Do not
expand `rs_stieltjes_bridge.lean` by proving every RS fact from scratch unless
a search of Mathlib and local bridge files shows that no suitable explicit
bridge theorem can cover the need.

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

## Current Debt Classification

Already eliminated from the active Chapter 1 public surface:

- `rsIntegrable_of_bounded_finite_discontinuities`, replaced by proof-bodied
  Theorem 1.1 support;
- `rsIntegral_sqrt_floor_add_id_0_2`, replaced by proof-bodied Problem 1.8(b)
  support;

Still requires task-owned repair or blocker evidence before clean completion:

- `rsIntegral_eq_integral_deriv` and `rsIntegral_integration_by_parts`, because
  downstream files historically called those names;
- `rsIntegrable_interval_concat` and `rsIntegral_interval_concat` for Theorem
  1.2 need blocker evidence before repair. The raw PDF states the interval
  concatenation clause without an extra endpoint-continuity condition, but under
  the current closed-interval Darboux definition the unconditional statement is
  unsafe when `alpha` and `f` jump together at the split point.

Retired from `ToyApollo.Output` as public axiom debt. Do not re-export or wrap
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

## Minimal Repair Order

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

The interval-concatenation clause in Theorem 1.2 has no direct downstream
consumer in the current Phase2 review context for `thm_1_2`, and no official
`ToyApollo/Output` module currently imports `ToyApollo.Output.thm_1_2`. This
means the blocker should be isolated; it should not stop independent Chapter
1--9 repair.

The clause is still conceptually important. It is the textbook-level interval
localization/additivity property one would use for piecewise RS calculations.
The closest later source use is the Chapter 7 practical-calculation discussion:
piecewise-continuous integrands can be handled by dividing the real line into
pieces when discontinuities of the integrand and the Stieltjes function do not
overlap. That later use matches a corrected/safe interval-concatenation theorem,
not the current unconditional Theorem 1.2(4) statement under the mesh-limit
definition.

Do not treat Theorem 1.2(4) as useless, and do not treat it as a global blocker.
Record it as a source/definition convention issue and continue with tasks that
do not depend on the unsafe unconditional local-to-global implication.

## Author confirmation (2026-07)

The textbook author (Kenneth Shum) has acknowledged this issue in
correspondence: the counterexample is valid and Theorem 1.2(4) is missing a
split-point continuity hypothesis (Option A: α continuous at c, or f continuous
at c). This is a record-only update — `thm_1_2` stays `allowed_exception` and is
not re-run. Full note:
[`author_errata_confirmations_2026-07.md`](author_errata_confirmations_2026-07.md).
