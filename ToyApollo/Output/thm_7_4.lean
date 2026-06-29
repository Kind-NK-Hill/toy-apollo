/-
TASK ID: thm_7_4
TYPE: Theorem_with_Proof
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_6_6
import ToyApollo.Output.thm_7_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

theorem thm_7_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω :=
    eventually_countable_forall.2 h_bound
  have hX_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    filter_upwards [h_bound_all, h_lim] with ω hω_bound hω_lim
    have hnorm_tendsto : Tendsto (fun n => ‖Xn n ω‖) atTop (nhds ‖X ω‖) :=
      (continuous_norm.tendsto (X ω)).comp hω_lim
    have hmem : ∀ᶠ n in atTop, ‖Xn n ω‖ ∈ Set.Iic (Y ω) :=
      Filter.Eventually.of_forall fun n => hω_bound n
    have hlimit_mem : ‖X ω‖ ∈ Set.Iic (Y ω) :=
      IsClosed.mem_of_tendsto isClosed_Iic hnorm_tendsto hmem
    simpa [Set.mem_Iic] using hlimit_mem
  have hX_int : Integrable X μ :=
    Integrable.mono' hYint hX_meas hX_bound
  have h_tendsto :
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      Y hXm hYint h_bound h_lim
  exact ⟨hX_int, h_tendsto⟩
