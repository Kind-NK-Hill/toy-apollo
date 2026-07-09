/-
TASK ID: thm_7_12
TYPE: Theorem_with_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_11
import ToyApollo.Output.thm_7_9
import ToyApollo.Output.thm_1_1
import ToyApollo.Output.thm_1_4

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

structure TextbookPiecewiseContinuousForDensity
    (F : StieltjesFunction ℝ) (f g : ℝ → ℝ) : Prop where
  measurable_g : Measurable g
  thm79_inputs : Thm79FiniteDiscontinuityInputs F g
  g_continuousOn_Icc : ∀ ⦃a b : ℝ⦄, a ≤ b → ContinuousOn g (Icc a b)
  f_continuousOn_Icc : ∀ ⦃a b : ℝ⦄, a ≤ b → ContinuousOn f (Icc a b)
  F_hasDerivAt : ∀ ⦃a b : ℝ⦄, a ≤ b →
    ∀ x ∈ Icc a b, HasDerivAt (fun t : ℝ => (F t : ℝ)) (f x) x
  density_measurable : Measurable (fun x : ℝ => g x * f x)
  density_integrable : Integrable (fun x : ℝ => g x * f x) volume
  abs_ls_integrable : Integrable (fun x : ℝ => |g x|) F.measure

theorem thm_7_12_intervalIntegral_eq_integral_Ioc
    {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, h x) = ∫ x in Ioc a b, h x ∂volume := by
  rw [intervalIntegral.integral_of_le hab]

theorem thm_7_12_rsTruncIntegral_eq_density_interval
    (F : StieltjesFunction ℝ) {f g : ℝ → ℝ}
    (hreg : TextbookPiecewiseContinuousForDensity F f g)
    {a b : ℝ} (hab : a < b) :
    rsTruncIntegral g F a b = ∫ x in Ioc a b, g x * f x ∂volume := by
  have hle : a ≤ b := le_of_lt hab
  have hRS : RSIntegrable g F a b :=
    hreg.thm79_inputs.finite_rs hab
  have hTrunc :
      rsTruncIntegral g F a b = rsIntegral g F a b hRS := by
    unfold rsTruncIntegral
    simp [hRS]
  have hFinite :
      rsIntegral g F a b hRS = ∫ x in a..b, g x * f x := by
    exact
      (thm_1_4 (f := g) (α := fun t : ℝ => (F t : ℝ)) (α' := f)
        (a := a) (b := b)
        hle
        (hreg.g_continuousOn_Icc hle)
        (F.mono.monotoneOn _)
        (hreg.F_hasDerivAt hle)
        (hreg.f_continuousOn_Icc hle)
        hRS).2
  calc
    rsTruncIntegral g F a b = rsIntegral g F a b hRS := hTrunc
    _ = ∫ x in a..b, g x * f x := hFinite
    _ = ∫ x in Ioc a b, g x * f x ∂volume :=
      thm_7_12_intervalIntegral_eq_integral_Ioc hle

theorem thm_7_12_improperRSIntegral_eq_density_integral
    (F : StieltjesFunction ℝ) {f g : ℝ → ℝ}
    (hreg : TextbookPiecewiseContinuousForDensity F f g)
    (hImp : ImproperRSIntegrable g F) :
    improperRSIntegral g F hImp = ∫ x, g x * f x := by
  have hSpec := improperRSIntegral_spec hImp
  have hAbsDensity : Integrable (fun x : ℝ => |g x * f x|) volume := by
    simpa [Real.norm_eq_abs] using hreg.density_integrable.norm
  have hDensityTendsto :
      Tendsto (fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, g x * f x ∂volume)
        improperRSFilter (nhds (∫ x, g x * f x)) :=
    thm_7_9_integral_Ioc_tendsto volume
      hreg.density_measurable hAbsDensity
  have hEventually :
      (fun p : ℝ × ℝ => rsTruncIntegral g F p.1 p.2)
        =ᶠ[improperRSFilter]
      fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, g x * f x ∂volume := by
    filter_upwards [thm_7_9_eventually_strict_improperRSFilter] with p hp
    exact thm_7_12_rsTruncIntegral_eq_density_interval F hreg hp
  have hRSTendsto :
      Tendsto (fun p : ℝ × ℝ => rsTruncIntegral g F p.1 p.2)
        improperRSFilter (nhds (∫ x, g x * f x)) :=
    Filter.Tendsto.congr' hEventually.symm hDensityTendsto
  haveI : NeBot improperRSFilter := thm_7_9_improperRSFilter_neBot
  exact tendsto_nhds_unique hSpec.2 hRSTendsto

theorem thm_7_12_change_of_variables
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hX : Measurable X) (hg : Measurable g)
    (hMap : Measure.map X P = F.measure) :
    ∫ ω, g (X ω) ∂P = ∫ x, g x ∂F.measure := by
  calc
    ∫ ω, g (X ω) ∂P = ∫ x, g x ∂Measure.map X P :=
      (thm_7_11 P hX hg).2
    _ = ∫ x, g x ∂F.measure := by rw [hMap]

theorem thm_7_12_ls_to_improper_rs
    (F : StieltjesFunction ℝ) {f g : ℝ → ℝ}
    (hreg : TextbookPiecewiseContinuousForDensity F f g) :
    ∃ hImp : ImproperRSIntegrable g F,
      ∫ x, g x ∂F.measure = improperRSIntegral g F hImp := by
  exact (thm_7_9 F hreg.thm79_inputs).2 hreg.abs_ls_integrable

theorem thm_7_12_general
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} {F : StieltjesFunction ℝ} {f g : ℝ → ℝ}
    (hX : Measurable X)
    (hMap : Measure.map X P = F.measure)
    (hreg : TextbookPiecewiseContinuousForDensity F f g)
    (_hIntGX : Integrable (fun ω => g (X ω)) P) :
    ∫ ω, g (X ω) ∂P = ∫ x, g x * f x := by
  rcases thm_7_12_ls_to_improper_rs F hreg with ⟨hImp, hLS⟩
  calc
    ∫ ω, g (X ω) ∂P = ∫ x, g x ∂F.measure :=
      thm_7_12_change_of_variables P hX hreg.measurable_g hMap
    _ = improperRSIntegral g F hImp := hLS
    _ = ∫ x, g x * f x :=
      thm_7_12_improperRSIntegral_eq_density_integral F hreg hImp

theorem thm_7_12_identity_case
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} {F : StieltjesFunction ℝ} {f : ℝ → ℝ}
    (hX : Measurable X)
    (hMap : Measure.map X P = F.measure)
    (hreg_id : TextbookPiecewiseContinuousForDensity F f (fun x : ℝ => x))
    (hIntX : Integrable X P) :
    ∫ ω, X ω ∂P = ∫ x, x * f x := by
  simpa using
    (thm_7_12_general P (X := X) (F := F) (f := f)
      (g := fun x : ℝ => x) hX hMap hreg_id hIntX)

theorem thm_7_12
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} {F : StieltjesFunction ℝ} {f g : ℝ → ℝ}
    (hX : Measurable X)
    (hMap : Measure.map X P = F.measure)
    (hreg_g : TextbookPiecewiseContinuousForDensity F f g)
    (hreg_id : TextbookPiecewiseContinuousForDensity F f (fun x : ℝ => x))
    (hIntGX : Integrable (fun ω => g (X ω)) P)
    (hIntX : Integrable X P) :
    (∫ ω, g (X ω) ∂P = ∫ x, g x * f x) ∧
      (∫ ω, X ω ∂P = ∫ x, x * f x) := by
  constructor
  · exact thm_7_12_general P hX hMap hreg_g hIntGX
  · exact thm_7_12_identity_case P hX hMap hreg_id hIntX
