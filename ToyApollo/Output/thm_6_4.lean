/-
TASK ID: thm_6_4
TYPE: Theorem_with_Proof
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter ENNReal Topology NNReal SimpleFunc

theorem thm_6_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ENNReal)
    (X : Ω → ENNReal) (h_meas : ∀ n, Measurable (Xn n)) (h_mono : Monotone Xn)
    (h_sup : ∀ ω, (⨆ n, Xn n ω) = X ω) :
    Tendsto (fun n => ∫⁻ ω, Xn n ω ∂μ) atTop (nhds (∫⁻ ω, X ω ∂μ)) := by
  have h_int_mono : Monotone fun n => ∫⁻ ω, Xn n ω ∂μ := by
    intro m n hmn
    exact lintegral_mono (fun ω => h_mono hmn ω)
  have source_mct :
      ∫⁻ ω, (⨆ n, Xn n ω) ∂μ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := by
    set c : NNReal → ENNReal := (↑)
    set F := fun ω : Ω => ⨆ n, Xn n ω
    refine le_antisymm ?_ (iSup_lintegral_le _)
    rw [lintegral_eq_nnreal]
    refine iSup_le fun s => iSup_le fun hsf => ?_
    refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
    rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
    have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
    let rs := s.map fun a => r * a
    have eq_rs : rs.map c = (const Ω r : SimpleFunc Ω ENNReal) * map c s := rfl
    have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ {ω | p ≤ Xn n ω} := by
      intro p
      rw [← inter_iUnion]
      nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
      refine Set.ext fun x => and_congr_right fun hx => (iff_of_eq (true_iff _)).2 ?_
      by_cases p_eq : p = 0
      · simp [p_eq]
      simp only [coe_map, mem_preimage, Function.comp_apply, mem_singleton_iff] at hx
      subst hx
      have hrs_ne : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
      have hs_ne : s x ≠ 0 := right_ne_zero_of_mul hrs_ne
      have hlt : (rs.map c) x < ⨆ n : ℕ, Xn n x := by
        refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ?_) (hsf x)
        suffices r * s x < 1 * s x by simpa
        gcongr
      rcases lt_iSup_iff.1 hlt with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
    have mono : ∀ p : ENNReal,
        Monotone fun n => rs.map c ⁻¹' {p} ∩ {ω | p ≤ Xn n ω} := by
      intro p i j hij
      refine inter_subset_inter_right _ ?_
      simp_rw [subset_def, mem_setOf]
      intro x hx
      exact le_trans hx (h_mono hij x)
    have h_threshold_meas : ∀ n, MeasurableSet {ω : Ω | map c rs ω ≤ Xn n ω} := fun n =>
      measurableSet_le (SimpleFunc.measurable _) (h_meas n)
    calc
      (r : ENNReal) * (s.map c).lintegral μ =
          ∑ p ∈ (rs.map c).range, p * μ (rs.map c ⁻¹' {p}) := by
        rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
      _ = ∑ p ∈ (rs.map c).range,
          p * μ (⋃ n, rs.map c ⁻¹' {p} ∩ {ω | p ≤ Xn n ω}) := by
        simp only [(eq _).symm]
      _ = ∑ p ∈ (rs.map c).range,
          ⨆ n, p * μ (rs.map c ⁻¹' {p} ∩ {ω | p ≤ Xn n ω}) :=
        Finset.sum_congr rfl fun p _ => by rw [(mono p).measure_iUnion, ENNReal.mul_iSup]
      _ = ⨆ n, ∑ p ∈ (rs.map c).range,
          p * μ (rs.map c ⁻¹' {p} ∩ {ω | p ≤ Xn n ω}) := by
        refine ENNReal.finsetSum_iSup_of_monotone fun p i j hij => ?_
        gcongr _ * μ ?_
        exact mono p hij
      _ ≤ ⨆ n : ℕ,
          ((rs.map c).restrict {ω | (rs.map c) ω ≤ Xn n ω}).lintegral μ := by
        gcongr with n
        rw [restrict_lintegral _ (h_threshold_meas n)]
        refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
        congr 2 with ω
        refine and_congr_right ?_
        simp +contextual
      _ ≤ ⨆ n, ∫⁻ ω, Xn n ω ∂μ := by
        simp only [← SimpleFunc.lintegral_eq_lintegral]
        gcongr with n ω
        simp only [map_apply] at h_threshold_meas
        simp only [coe_map, SimpleFunc.restrict_apply _ (h_threshold_meas _), (· ∘ ·)]
        exact indicator_apply_le id
  have h_lintegral :
      ∫⁻ ω, X ω ∂μ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := by
    calc
      ∫⁻ ω, X ω ∂μ = ∫⁻ ω, (⨆ n, Xn n ω) ∂μ := by simp [h_sup]
      _ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := source_mct
  rw [h_lintegral]
  exact tendsto_atTop_iSup h_int_mono
