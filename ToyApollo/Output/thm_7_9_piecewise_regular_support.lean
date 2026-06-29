/-
TASK ID: thm_7_9_piecewise_regular_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_1_1
import ToyApollo.Output.thm_7_9_regularity_support

open MeasureTheory Set Topology

noncomputable section

structure Thm79FiniteDiscontinuityInputs
    (F : StieltjesFunction ℝ) (g : ℝ → ℝ) : Prop where
  measurable : Measurable g
  finite_bounds : ∀ ⦃a b : ℝ⦄, a < b →
    BddAbove (g '' Icc a b) ∧ BddBelow (g '' Icc a b)
  finite_abs_bounds : ∀ ⦃a b : ℝ⦄, a < b →
    BddAbove ((fun x => |g x|) '' Icc a b) ∧
      BddBelow ((fun x => |g x|) '' Icc a b)
  finite_discontinuities : ∀ ⦃a b : ℝ⦄, a < b →
    (discontinuitySetOn g a b).Finite
  finite_abs_discontinuities : ∀ ⦃a b : ℝ⦄, a < b →
    (discontinuitySetOn (fun x => |g x|) a b).Finite
  F_cont_at_discontinuities : ∀ ⦃a b x : ℝ⦄, a < b →
    x ∈ discontinuitySetOn g a b → ContinuousAt F x
  F_cont_at_abs_discontinuities : ∀ ⦃a b x : ℝ⦄, a < b →
    x ∈ discontinuitySetOn (fun x => |g x|) a b → ContinuousAt F x

namespace Thm79FiniteDiscontinuityInputs

theorem to_source_regular {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) :
    Thm79SourceRegular F g := by
  refine ⟨h.measurable, ?_, ?_⟩
  · intro a b hab
    have hbounds := h.finite_bounds hab
    exact thm_1_1 hab F.mono hbounds.1 hbounds.2
      (h.finite_discontinuities hab)
      (fun {x} hx => h.F_cont_at_discontinuities (a := a) (b := b) (x := x) hab hx)
  · intro a b hab
    have hbounds := h.finite_abs_bounds hab
    exact thm_1_1 hab F.mono hbounds.1 hbounds.2
      (h.finite_abs_discontinuities hab)
      (fun {x} hx =>
        h.F_cont_at_abs_discontinuities (a := a) (b := b) (x := x) hab hx)

theorem finite_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    RSIntegrable g F a b :=
  h.to_source_regular.finite_rs hab

theorem finite_abs_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    RSIntegrable (fun x => |g x|) F a b :=
  h.to_source_regular.finite_abs_rs hab

end Thm79FiniteDiscontinuityInputs
