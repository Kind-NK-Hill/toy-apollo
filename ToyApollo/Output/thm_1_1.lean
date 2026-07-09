import ToyApollo.Output.thm_1_1_finite_discontinuity_support

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

/-!
# Theorem 1.1

Textbook statement (Shum, Theorem 1.1):

> Suppose `f` is bounded on `[a, b]` and there are finitely many points
> `c₁, …, cₙ` in `[a, b]` at which `f` is discontinuous. If `α` is continuous at
> each of these discontinuity points of `f`, then `f ∈ 𝓡(α)` — that is, `f` is
> Riemann–Stieltjes integrable on `[a, b]` with respect to `α`.

Throughout this chapter `α` is a non-decreasing function (the cdf setting), which
is why the Lean statement carries `Monotone α`. `RSIntegrable` is the exported
Definition 1.2 predicate (see `ToyApollo.Output.def_1_2`).

The finite-discontinuity Darboux proof spine is assembled in
`ToyApollo.Output.thm_1_1_finite_discontinuity_support` and the layer modules it
imports (grouped under `thm_1_1_support/` in the GitHub export). This file is the
readable home of the final theorem itself.
-/

/-- **Theorem 1.1.** If `f` is bounded on `[a, b]` with only finitely many
discontinuities, and the non-decreasing integrator `α` is continuous at each
discontinuity point of `f`, then `f` is Riemann–Stieltjes integrable with respect
to `α` on `[a, b]`. -/
theorem thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b :=
  Thm11SourceRoute.strict_thm_1_1
    hab hα_mono hAbove hBelow hDiscFinite hαCont
