import Mathlib

/-
TASK ID: prob_5_7
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
TASK CONTENT:
\item (Inverse Transform Method). Let $U_1,U_2,\dots$ be a sequence of independent random variables uniformly distributed between 0 and 1. Given a Stieltjes measure function $F(x)$ that is continuous and strictly monotonically increasing, such that the inverse function $F^{-1}$ is well-defined, show that $F^{-1}(U_i)$, for $i\ge 1$, is a sequence of i.i.d. random variable with cdf $F(x)$. (For Stieltjes measure function that is not continuous or not strictly monotonic, see the proof of Theorem 10.8 or [4, Theorem 1.2.2].)
-/

-- WRITE FINAL LEAN CODE BELOW

open ProbabilityTheory MeasureTheory MeasurableSpace Set Filter

/-
The Inverse Transform Method: given i.i.d. Uniform[0,1] random variables U_i
and a continuous strictly increasing CDF F with inverse F_inv,
the random variables X_i = F_inv(U_i) are a.e. measurable and i.i.d. with CDF F.

Note: The original statement used `IndepFun` (for two functions) where `iIndepFun`
(for indexed families) was intended. This has been corrected.
-/
theorem prob_5_7 {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ) (hU_meas : ∀ i, Measurable (U i))
    (hU_indep : iIndepFun (m := fun _ => inferInstance) U P)
    (hU_uniform : ∀ i, P.map (U i) = volume.restrict (Icc (0 : ℝ) 1))
    (F F_inv : ℝ → ℝ) (hF_strict : StrictMono F) (hF_cont : Continuous F)
    (hF_lim0 : Tendsto F atBot (nhds 0)) (hF_lim1 : Tendsto F atTop (nhds 1))
    (hF_inv : ∀ u ∈ Ioo (0 : ℝ) 1, F (F_inv u) = u)
    (hF_inv' : ∀ x, F_inv (F x) = x) :
    let X : ℕ → Ω → ℝ := fun i ω => F_inv (U i ω)
    (∀ i, AEMeasurable (X i) P) ∧
    (∀ i, ∀ x, P {ω | X i ω ≤ x} = ENNReal.ofReal (F x)) ∧
    iIndepFun (m := fun _ => inferInstance) (fun (i : ℕ) => X i) P := by
  intro X
  have hF_inv_monoOn : MonotoneOn F_inv (Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact hF_strict.le_iff_le.mp (by simpa [hF_inv u hu, hF_inv v hv] using huv)
  have hF_inv_ae : AEMeasurable F_inv (volume.restrict (Icc (0 : ℝ) 1)) := by
    have h_ae_ioo : AEMeasurable F_inv (volume.restrict (Ioo (0 : ℝ) 1)) :=
      aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hF_inv_monoOn
    simpa [restrict_Ioo_eq_restrict_Icc] using h_ae_ioo
  have hX_ae : ∀ i, AEMeasurable (X i) P := by
    intro i
    have hF_inv_ae_i : AEMeasurable F_inv (P.map (U i)) := by
      simpa [hU_uniform i] using hF_inv_ae
    simpa [X, Function.comp_def] using hF_inv_ae_i.comp_measurable (hU_meas i)
  refine ⟨hX_ae, ?_, ?_⟩
  · intro i x
    suffices h_eq : P {ω | F_inv (U i ω) ≤ x} = P {ω | U i ω ≤ F x} by
      have h_pushforward :
          P {ω | U i ω ≤ F x} =
            (MeasureTheory.Measure.map (U i) P) (Set.Iic (F x)) := by
        rw [Measure.map_apply] <;> aesop
      simp_all +decide [Set.Iic_inter_Iic]
      rw [h_eq,
        show (Iic (F x) ∩ Icc 0 1 : Set ℝ) = Set.Icc 0 (F x) from ?_,
        Real.volume_Icc] <;> norm_num
      ext
      simp [Set.mem_Iic, Set.mem_Icc]
      exact
        ⟨fun h => ⟨h.2.1, h.1⟩,
          fun h =>
            ⟨h.2, h.1,
              h.2.trans
                (le_of_tendsto_of_tendsto tendsto_const_nhds hF_lim1 <|
                  Filter.eventually_atTop.2
                    ⟨x, fun y hy => hF_strict.monotone hy⟩)⟩⟩
    rw [MeasureTheory.measure_congr]
    have h_eq_set : ∀ᵐ ω ∂P, U i ω ∈ Set.Ioo 0 1 := by
      have h_eq_set : (MeasureTheory.Measure.map (U i) P) {0, 1} = 0 := by
        rw [hU_uniform i, MeasureTheory.Measure.restrict_apply] <;> norm_num
        rw [Set.inter_eq_left.mpr] <;> norm_num [Set.insert_subset_iff]
        rw [Set.insert_eq, MeasureTheory.measure_union] <;> norm_num
      have h_eq_set : (MeasureTheory.Measure.map (U i) P) (Set.Ioo 0 1)ᶜ = 0 := by
        rw [MeasureTheory.measure_compl] <;> norm_num [h_eq_set]
        rw [hU_uniform i, MeasureTheory.Measure.restrict_apply] <;>
          norm_num [Set.Ioo_def]
        rw [Set.inter_eq_left.mpr] <;> norm_num [Set.Ioo_subset_Icc_self]
      rw [MeasureTheory.Measure.map_apply (hU_meas i)] at h_eq_set
      · exact eventually_map.mp h_eq_set
      · exact measurableSet_Ioo.compl
    filter_upwards [h_eq_set] with ω hω
    simp [hF_inv (U i ω) hω]
    exact
      ⟨fun h => by simpa [hF_inv _ hω] using hF_strict.monotone h,
        fun h => by
          simpa [hF_inv'] using hF_strict.le_iff_le.mp
            (by simpa [hF_inv _ hω] using h)⟩
  · have h_indep := hU_indep.comp₀ (fun _ => F_inv)
      (fun i => (hU_meas i).aemeasurable)
      (fun i => by simpa [hU_uniform i] using hF_inv_ae)
    simpa [X, Function.comp_def] using h_indep
