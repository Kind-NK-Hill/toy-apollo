import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_13_3

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

noncomputable section

/-- The raw Chapter 12 inner product agrees with Mathlib's `L²` inner product
on the `toLp` representatives. -/
theorem l2Function_toLp_inner_eq_l2Inner {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    ⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ =
      l2Inner P X Y hX hY := by
  rw [L2.inner_def]
  unfold l2Inner L2Function.toLp
  apply integral_congr_ae
  have hXae := MemLp.coeFn_toLp (show MemLp X (2 : ENNReal) P from hX)
  have hYae := MemLp.coeFn_toLp (show MemLp Y (2 : ENNReal) P from hY)
  filter_upwards [hXae, hYae] with ω hXω hYω
  rw [hXω, hYω]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp

/-- `L²` functions are closed under subtraction. -/
theorem l2Function_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function P X) (hY : L2Function P Y) :
    L2Function P (X - Y) :=
  (show MemLp X (2 : ENNReal) P from hX).sub
    (show MemLp Y (2 : ENNReal) P from hY)

/-- `G`-measurable real functions are closed under subtraction. -/
theorem gMeasurable_sub {Ω : Type*} {𝓖 : SigmaField Ω}
    {X Y : Ω → ℝ} (hX : GMeasurable 𝓖 X) (hY : GMeasurable 𝓖 Y) :
    GMeasurable 𝓖 (X - Y) :=
  hX.sub hY

/-- Hilbert-space projection inequality: if the residual `x - y` is
orthogonal to the competitor displacement `z - y`, then `y` is at least as
close to `x` as `z` is. -/
theorem hilbert_norm_le_of_inner_sub_eq_zero {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) (horth : ⟪x - y, z - y⟫_ℝ = 0) :
    ‖x - y‖ ≤ ‖x - z‖ := by
  let e : E := x - y
  let d : E := z - y
  have horth_neg : ⟪e, -d⟫_ℝ = 0 := by
    rw [inner_neg_right, horth, neg_zero]
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e (-d) horth_neg
  have hxd : x - z = e + (-d) := by
    simp [e, d]
  have hsq' : ‖x - z‖ * ‖x - z‖ = ‖e‖ * ‖e‖ + ‖-d‖ * ‖-d‖ := by
    rw [hxd, hsq]
  have hsquare_le : ‖e‖ * ‖e‖ ≤ ‖x - z‖ * ‖x - z‖ := by
    rw [hsq']
    nlinarith [sq_nonneg ‖-d‖]
  have hnorm :=
    (mul_self_le_mul_self_iff (norm_nonneg e) (norm_nonneg (x - z))).2 hsquare_le
  simpa [e] using hnorm
