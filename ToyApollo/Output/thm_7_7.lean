/-
TASK ID: thm_7_7
TYPE: Theorem_Statement
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Filter MeasureTheory
open scoped Topology

theorem thm_7_DCT_filter {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ι → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (l : Filter ι) [l.IsCountablyGenerated]
    (hXm : ∀ᶠ h in l, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ᶠ h in l, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) l (nhds (X ω))) :
    Tendsto (fun h => ∫ ω, Xh h ω ∂μ) l
      (nhds (∫ ω, X ω ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence
    Y hXm h_bound hYint h_lim

theorem thm_7_7_sequential_complex_DCT {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have hX_finite : HasFiniteIntegral X μ :=
    hasFiniteIntegral_of_dominated_convergence hYint.hasFiniteIntegral h_bound h_lim
  have hXint : Integrable X μ := ⟨hX_meas, hX_finite⟩
  have h_tendsto :
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) :=
    thm_7_DCT_filter μ Xn X Y atTop
      (Eventually.of_forall hXm) hYint
      (Eventually.of_forall h_bound) h_lim
  exact ⟨hXint, h_tendsto⟩

theorem thm_7_7_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Set ℝ) (h0 : ℝ)
    (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hh0 : h0 ∈ I)
    (hXm : ∀ h : ℝ, h ∈ I → AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, h ∈ I → ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h : ℝ => Xh h ω) (nhdsWithin h0 I) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
      (nhds (∫ ω, X ω ∂μ)) := by
  have hconst : Tendsto (fun _ : ℕ => h0) atTop (nhdsWithin h0 I) :=
    tendsto_const_nhdsWithin hh0
  have hseq_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun _ : ℕ => Xh h0 ω) atTop (nhds (X ω)) := by
    filter_upwards [h_lim] with ω hω
    exact hω.comp hconst
  have hseq :
      Integrable X μ ∧
        Tendsto (fun _ : ℕ => ∫ ω, Xh h0 ω ∂μ) atTop
          (nhds (∫ ω, X ω ∂μ)) :=
    thm_7_7_sequential_complex_DCT μ (fun _ : ℕ => Xh h0) X Y
      (fun _ => hXm h0 hh0) hYint (fun _ => h_bound h0 hh0) hseq_lim
  have h_tendsto :
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
        (nhds (∫ ω, X ω ∂μ)) := by
    classical
    refine Filter.tendsto_iff_seq_tendsto.2 ?_
    intro u hu
    let v : ℕ → ℝ := fun n => if u n ∈ I then u n else h0
    have hu_mem : ∀ᶠ n in atTop, u n ∈ I :=
      hu.eventually self_mem_nhdsWithin
    have hv_mem : ∀ n : ℕ, v n ∈ I := by
      intro n
      by_cases hn : u n ∈ I
      · simpa [v, hn] using hn
      · simpa [v, hn] using hh0
    have huv : u =ᶠ[atTop] v := by
      filter_upwards [hu_mem] with n hn
      simp [v, hn]
    have hv_lim : Tendsto v atTop (nhdsWithin h0 I) :=
      Filter.Tendsto.congr' huv hu
    have hv_seq_lim :
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xh (v n) ω) atTop (nhds (X ω)) := by
      filter_upwards [h_lim] with ω hω
      exact hω.comp hv_lim
    have hv_dct :=
      thm_7_7_sequential_complex_DCT μ (fun n : ℕ => Xh (v n)) X Y
        (fun n => hXm (v n) (hv_mem n)) hYint
        (fun n => h_bound (v n) (hv_mem n)) hv_seq_lim
    have hint_eq :
        (fun n : ℕ => ∫ ω, Xh (u n) ω ∂μ) =ᶠ[atTop]
          (fun n : ℕ => ∫ ω, Xh (v n) ω ∂μ) := by
      filter_upwards [huv] with n hn
      rw [hn]
    have hu_integral :
        Tendsto (fun n : ℕ => ∫ ω, Xh (u n) ω ∂μ) atTop
          (nhds (∫ ω, X ω ∂μ)) :=
      Filter.Tendsto.congr' hint_eq.symm hv_dct.2
    simpa [Function.comp_def] using hu_integral
  exact ⟨hseq.1, h_tendsto⟩

theorem thm_7_7 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (h0 : ℝ)
    (hXm : ∀ h : ℝ, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) (nhds h0) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h => ∫ ω, Xh h ω ∂μ) (nhds h0) (nhds (∫ ω, X ω ∂μ)) := by
  have hlim_univ :
      ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) (nhdsWithin h0 Set.univ) (nhds (X ω)) := by
    simpa [nhdsWithin_univ] using h_lim
  simpa [nhdsWithin_univ] using
    (thm_7_7_interval μ Set.univ h0 Xh X Y (Set.mem_univ h0)
      (fun h _ => hXm h) hYint (fun h _ => h_bound h) hlim_univ)
