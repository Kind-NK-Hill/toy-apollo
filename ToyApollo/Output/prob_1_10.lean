/-
TASK ID: prob_1_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set Filter

theorem prob_1_10
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio 0) = 0)
    (hboundary :
      Filter.Tendsto (fun x : ℝ => x * (1 - (μ (Iic x)).toReal)) Filter.atTop
        (nhds 0)) :
    ∫ x, x ∂μ = ∫ t in Ioi 0, (μ (Ioi t)).toReal := by
  -- `F + G = 1`, i.e. the tail equals `1 − F`.
  have hFG : ∀ T : ℝ, (μ (Ioi T)).toReal = 1 - (μ (Iic T)).toReal := by
    intro T
    have hsum : μ (Iic T) + μ (Ioi T) = 1 := by
      rw [← compl_Iic (a := T), measure_add_measure_compl measurableSet_Iic, measure_univ]
    have h2 := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), ENNReal.toReal_one] at h2
    linarith
  -- The truncated identity (★), phrased additively in `ℝ≥0∞`.
  have core : ∀ T : ℝ, 0 ≤ T →
      (∫⁻ x in Ioc (0:ℝ) T, ENNReal.ofReal x ∂μ) + ENNReal.ofReal T * μ (Ioi T)
        = ∫⁻ t in Ioc (0:ℝ) T, μ (Ioi t) := by
    intro T hT
    have f_nn : 0 ≤ᵐ[μ] (fun x => min x T) := by
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp] with x hx
      exact le_min (le_of_not_gt hx) hT
    have f_mble : AEMeasurable (fun x => min x T) μ :=
      (measurable_id.min measurable_const).aemeasurable
    -- layer cake applied to the truncated variable `min x T`
    have hlc : ∫⁻ x, ENNReal.ofReal (min x T) ∂μ
        = ∫⁻ t in Ioi 0, μ {x | t < min x T} :=
      lintegral_eq_lintegral_meas_lt μ f_nn f_mble
    -- LHS: split off the boundary term
    have hLHS : ∫⁻ x, ENNReal.ofReal (min x T) ∂μ
        = (∫⁻ x in Ioc (0:ℝ) T, ENNReal.ofReal x ∂μ) + ENNReal.ofReal T * μ (Ioi T) := by
      have hz : ∫⁻ x in Iic (0:ℝ), ENNReal.ofReal (min x T) ∂μ = 0 := by
        have heq : EqOn (fun x => ENNReal.ofReal (min x T)) (fun _ => (0 : ENNReal)) (Iic 0) := by
          intro x hx
          simp only [mem_Iic] at hx
          show ENNReal.ofReal (min x T) = 0
          rw [min_eq_left (hx.trans hT)]
          exact ENNReal.ofReal_eq_zero.mpr hx
        rw [setLIntegral_congr_fun measurableSet_Iic heq]; simp
      have hIoc : ∫⁻ x in Ioc (0:ℝ) T, ENNReal.ofReal (min x T) ∂μ
          = ∫⁻ x in Ioc (0:ℝ) T, ENNReal.ofReal x ∂μ := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro x hx
        show ENNReal.ofReal (min x T) = ENNReal.ofReal x
        rw [min_eq_left hx.2]
      have hIoiT : ∫⁻ x in Ioi T, ENNReal.ofReal (min x T) ∂μ
          = ENNReal.ofReal T * μ (Ioi T) := by
        have heq : EqOn (fun x => ENNReal.ofReal (min x T)) (fun _ => ENNReal.ofReal T) (Ioi T) := by
          intro x hx
          simp only [mem_Ioi] at hx
          show ENNReal.ofReal (min x T) = ENNReal.ofReal T
          rw [min_eq_right hx.le]
        rw [setLIntegral_congr_fun measurableSet_Ioi heq]
        simp only [setLIntegral_const]
      rw [← lintegral_add_compl (fun x => ENNReal.ofReal (min x T)) measurableSet_Ioi,
          compl_Ioi, hz, add_zero, ← Ioc_union_Ioi_eq_Ioi hT,
          lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, hIoc, hIoiT]
    -- RHS: the tail integrand truncates to `Ioc 0 T`
    have hRHS : ∫⁻ t in Ioi 0, μ {x | t < min x T} = ∫⁻ t in Ioc (0:ℝ) T, μ (Ioi t) := by
      have hz : ∫⁻ t in Ioi T, μ {x | t < min x T} = 0 := by
        have heq : EqOn (fun t => μ {x | t < min x T}) (fun _ => (0 : ENNReal)) (Ioi T) := by
          intro t ht
          simp only [mem_Ioi] at ht
          show μ {x | t < min x T} = 0
          have hempty : {x : ℝ | t < min x T} = ∅ := by
            ext x
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
            intro hlt
            exact absurd (lt_min_iff.mp hlt).2 (not_lt.mpr ht.le)
          rw [hempty, measure_empty]
        rw [setLIntegral_congr_fun measurableSet_Ioi heq]; simp
      rw [← Ioc_union_Ioi_eq_Ioi hT,
          lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, hz, add_zero,
          ← restrict_Ioo_eq_restrict_Ioc]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [mem_Ioo] at ht
      show μ {x | t < min x T} = μ (Ioi t)
      congr 1
      ext x
      simp only [mem_setOf_eq, mem_Ioi, lt_min_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, ht.2⟩⟩
    rw [← hLHS, hlc, hRHS]
  -- `Ioc 0 n ↑ Ioi 0`
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc (0:ℝ) (n:ℝ)) := fun i j =>
    ⟨max i j,
      Ioc_subset_Ioc le_rfl (by exact_mod_cast le_max_left i j),
      Ioc_subset_Ioc le_rfl (by exact_mod_cast le_max_right i j)⟩
  have hunion : (⋃ n : ℕ, Ioc (0:ℝ) (n:ℝ)) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.2 (fun x _ => exists_nat_ge x)
  -- monotone convergence of the two truncated integrals
  have key_u : Tendsto (fun n : ℕ => ∫⁻ x in Ioc (0:ℝ) (n:ℝ), ENNReal.ofReal x ∂μ) atTop
      (nhds (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x ∂μ)) := by
    rw [← hunion, setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal x) hdir]
    exact tendsto_atTop_iSup (fun i j hij =>
      lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc le_rfl (by exact_mod_cast hij)) le_rfl)
        le_rfl)
  have key_v : Tendsto (fun n : ℕ => ∫⁻ t in Ioc (0:ℝ) (n:ℝ), μ (Ioi t)) atTop
      (nhds (∫⁻ t in Ioi (0:ℝ), μ (Ioi t))) := by
    rw [← hunion, setLIntegral_iUnion_of_directed (fun t => μ (Ioi t)) hdir]
    exact tendsto_atTop_iSup (fun i j hij =>
      lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc le_rfl (by exact_mod_cast hij)) le_rfl)
        le_rfl)
  -- the boundary term tends to `0` — this is where `hboundary` is genuinely consumed
  have hbdry : Tendsto (fun n : ℕ => ENNReal.ofReal (n:ℝ) * μ (Ioi (n:ℝ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => (n:ℝ) * (1 - (μ (Iic (n:ℝ))).toReal)) atTop (nhds 0) :=
      hboundary.comp tendsto_natCast_atTop_atTop
    have hreal2 : Tendsto (fun n : ℕ => (n:ℝ) * (μ (Ioi (n:ℝ))).toReal) atTop (nhds 0) := by
      refine hreal.congr (fun n => ?_)
      rw [hFG]
    have hof := ENNReal.tendsto_ofReal hreal2
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr (fun n => ?_)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_toReal (measure_ne_top μ _)]
  -- combine: the untruncated `ℝ≥0∞` identity
  have hAB : (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x ∂μ) = ∫⁻ t in Ioi (0:ℝ), μ (Ioi t) := by
    have hsum := key_u.add hbdry
    rw [add_zero] at hsum
    have h1 : Tendsto (fun n : ℕ => ∫⁻ t in Ioc (0:ℝ) (n:ℝ), μ (Ioi t)) atTop
        (nhds (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x ∂μ)) :=
      hsum.congr (fun n => core (n:ℝ) (Nat.cast_nonneg n))
    exact tendsto_nhds_unique h1 key_v
  -- transport back to the Bochner integrals
  have hlint_id : ∫⁻ x, ENNReal.ofReal x ∂μ = ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x ∂μ := by
    rw [← lintegral_add_compl (fun x => ENNReal.ofReal x) measurableSet_Ioi, compl_Ioi]
    have hz : ∫⁻ x in Iic (0:ℝ), ENNReal.ofReal x ∂μ = 0 := by
      have heq : EqOn (fun x => ENNReal.ofReal x) (fun _ => (0 : ENNReal)) (Iic 0) := by
        intro x hx
        simp only [mem_Iic] at hx
        show ENNReal.ofReal x = 0
        exact ENNReal.ofReal_eq_zero.mpr hx
      rw [setLIntegral_congr_fun measurableSet_Iic heq]; simp
    rw [hz, add_zero]
  have hlint_tail : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((μ (Ioi t)).toReal)
      = ∫⁻ t in Ioi (0:ℝ), μ (Ioi t) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact ENNReal.ofReal_toReal (measure_ne_top μ _)
  have hnn_id : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp] with x hx
    exact le_of_not_gt hx
  have hmeas_id : AEStronglyMeasurable (fun x : ℝ => x) μ := measurable_id.aestronglyMeasurable
  have hnn_tail : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun t => (μ (Ioi t)).toReal) :=
    Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  have hmeas_tail : AEStronglyMeasurable (fun t => (μ (Ioi t)).toReal)
      (volume.restrict (Ioi (0:ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ennreal_toReal ?_
    exact Antitone.measurable (fun a b hab => measure_mono (Ioi_subset_Ioi hab))
  have goalL : ∫ x, x ∂μ = (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x ∂μ).toReal := by
    rw [← hlint_id]
    exact integral_eq_lintegral_of_nonneg_ae hnn_id hmeas_id
  have goalR : ∫ t in Ioi (0:ℝ), (μ (Ioi t)).toReal
      = (∫⁻ t in Ioi (0:ℝ), μ (Ioi t)).toReal := by
    rw [← hlint_tail]
    exact integral_eq_lintegral_of_nonneg_ae hnn_tail hmeas_tail
  rw [goalL, goalR, hAB]
