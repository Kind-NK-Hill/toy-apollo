/-
TASK ID: prob_14_12_limit_truncation_tail_support
TYPE: Parent-owned support
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_14_3
import ToyApollo.Output.thm_14_5

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

def prob_14_12_convergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ => μ {ω : Ω | ε < |Xseq n ω - X ω|})
      atTop (𝓝 (0 : ℝ≥0∞))

def prob_14_12_aeSubsequenceRadius (k : ℕ) : ℝ :=
  ((2 : ℝ)⁻¹) ^ (k + 1)

theorem prob_14_12_aeSubsequenceRadius_pos (k : ℕ) :
    0 < prob_14_12_aeSubsequenceRadius k := by
  unfold prob_14_12_aeSubsequenceRadius
  positivity

theorem prob_14_12_aeSubsequenceRadius_tendsto_zero :
    Tendsto prob_14_12_aeSubsequenceRadius atTop (𝓝 (0 : ℝ)) := by
  unfold prob_14_12_aeSubsequenceRadius
  exact
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).comp
      (tendsto_add_atTop_nat 1)

theorem prob_14_12_aeSubsequenceRadius_tsum_ne_top :
    (∑' k : ℕ, ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k)) ≠ ∞ := by
  simp [prob_14_12_aeSubsequenceRadius, ENNReal.ofReal_inv_of_pos,
    ENNReal.inv_pow]
  rw [ENNReal.tsum_geometric_add_one]
  simp

theorem prob_14_12_choose_ae_subsequence_probability_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : prob_14_12_convergesInProbability μ Xseq X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k : ℕ,
        μ {ω : Ω |
            prob_14_12_aeSubsequenceRadius k <
              |Xseq (φ k) ω - X ω|} ≤
          ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k) := by
  classical
  have hchoose :
      ∀ lower k : ℕ, ∃ n : ℕ, lower ≤ n ∧
        μ {ω : Ω |
            prob_14_12_aeSubsequenceRadius k <
              |Xseq n ω - X ω|} ≤
          ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k) := by
    intro lower k
    have hsmall :
        ∃ N : ℕ, ∀ n ≥ N,
          μ {ω : Ω |
              prob_14_12_aeSubsequenceRadius k <
                |Xseq n ω - X ω|} ≤
            ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k) := by
      exact
        ENNReal.tendsto_atTop_zero.mp
          (hProb (prob_14_12_aeSubsequenceRadius k)
            (prob_14_12_aeSubsequenceRadius_pos k))
          (ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k))
          (ENNReal.ofReal_pos.mpr (prob_14_12_aeSubsequenceRadius_pos k))
    rcases hsmall with ⟨N, hN⟩
    refine ⟨max lower N, le_max_left lower N, ?_⟩
    exact hN (max lower N) (le_max_right lower N)
  choose next hnext using hchoose
  let φ : ℕ → ℕ :=
    fun k : ℕ =>
      Nat.rec (next 0 0)
        (fun j prev => next (prev + 1) (j + 1)) k
  have hstep : ∀ k : ℕ, φ k < φ (k + 1) := by
    intro k
    change φ k < next (φ k + 1) (k + 1)
    exact Nat.lt_of_succ_le (hnext (φ k + 1) (k + 1)).1
  have hmono : StrictMono φ := strictMono_nat_of_lt_succ hstep
  refine ⟨φ, hmono, ?_⟩
  intro k
  cases k with
  | zero =>
      simpa [φ] using (hnext 0 0).2
  | succ k =>
      change
        μ {ω : Ω |
            prob_14_12_aeSubsequenceRadius (k + 1) <
              |Xseq (next (φ k + 1) (k + 1)) ω - X ω|} ≤
          ENNReal.ofReal (prob_14_12_aeSubsequenceRadius (k + 1))
      exact (hnext (φ k + 1) (k + 1)).2

theorem prob_14_12_ae_tendsto_of_eventually_not_bad
    {Ω : Type*} {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {φ : ℕ → ℕ} {ω : Ω}
    (hω : ∀ᶠ k : ℕ in atTop,
      ω ∉ {η : Ω |
        prob_14_12_aeSubsequenceRadius k <
          |Xseq (φ k) η - X η|}) :
    Tendsto (fun k : ℕ => Xseq (φ k) ω) atTop (𝓝 (X ω)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hRadiusEventually :
      ∀ᶠ k : ℕ in atTop, prob_14_12_aeSubsequenceRadius k < ε :=
    prob_14_12_aeSubsequenceRadius_tendsto_zero.eventually
      (Iio_mem_nhds hε)
  filter_upwards [hω, hRadiusEventually] with k hnot hlt
  have habs_le :
      |Xseq (φ k) ω - X ω| ≤ prob_14_12_aeSubsequenceRadius k := by
    exact le_of_not_gt hnot
  simpa [Real.norm_eq_abs] using lt_of_le_of_lt habs_le hlt

theorem prob_14_12_convergence_probability_extracts_ae_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    prob_14_12_convergesInProbability μ Xseq X →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ᵐ ω ∂μ,
          Tendsto (fun k : ℕ => Xseq (φ k) ω) atTop (𝓝 (X ω))) := by
  intro hProb
  rcases prob_14_12_choose_ae_subsequence_probability_bound μ Xseq X hProb with
    ⟨φ, hφmono, hφbound⟩
  let bad : ℕ → Set Ω := fun k =>
    {ω : Ω |
      prob_14_12_aeSubsequenceRadius k <
        |Xseq (φ k) ω - X ω|}
  have hsum_le :
      (∑' k : ℕ, μ (bad k)) ≤
        ∑' k : ℕ, ENNReal.ofReal (prob_14_12_aeSubsequenceRadius k) := by
    exact ENNReal.tsum_le_tsum (by simpa [bad] using hφbound)
  have hsum_ne_top : (∑' k : ℕ, μ (bad k)) ≠ ∞ := by
    intro htop
    exact prob_14_12_aeSubsequenceRadius_tsum_ne_top
      (top_unique (by simpa [htop] using hsum_le))
  have hAeEventually : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ bad k :=
    MeasureTheory.ae_eventually_notMem hsum_ne_top
  refine ⟨φ, hφmono, ?_⟩
  exact hAeEventually.mono fun ω hω =>
    prob_14_12_ae_tendsto_of_eventually_not_bad (Xseq := Xseq) (X := X)
      (φ := φ) (ω := ω) (by simpa [bad] using hω)

theorem convergence_probability_extracts_ae_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    prob_14_12_convergesInProbability μ Xseq X →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ᵐ ω ∂μ,
          Tendsto (fun k : ℕ => Xseq (φ k) ω) atTop (𝓝 (X ω))) :=
  prob_14_12_convergence_probability_extracts_ae_subsequence μ Xseq X

def prob_14_12_obligation_5_geTailIntegrand
    {Ω : Type*} (X : Ω → ℝ) (M : ℝ) : Ω → ℝ≥0∞ :=
  fun ω => Set.indicator {η : Ω | M ≤ |X η|}
    (fun η : Ω => ENNReal.ofReal |X η|) ω

def prob_14_12_obligation_5_geTailExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, prob_14_12_obligation_5_geTailIntegrand X M ω ∂μ

def prob_14_12_variableTailExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (M : ℝ) : ℝ≥0∞ :=
  prob_14_12_obligation_5_geTailExpectation μ X M

def prob_14_12_uniformIntegrableVariables
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, prob_14_12_variableTailExpectation μ (Xseq n) M ≤ ENNReal.ofReal ε

theorem prob_14_12_uniformIntegrableVariables_subsequence_tail_bound_with_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ)
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ φ : ℕ → ℕ, ∀ᶠ k : ℕ in atTop,
        prob_14_12_obligation_5_geTailExpectation μ (Xseq (φ k)) M ≤
          ENNReal.ofReal ε := by
  rcases hUI ε hε with ⟨M, hM_nonneg, htail⟩
  refine ⟨M, hM_nonneg, ?_⟩
  intro φ
  exact Filter.Eventually.of_forall fun k => by
    simpa [prob_14_12_variableTailExpectation] using htail (φ k)

theorem prob_14_12_uniformIntegrableVariables_subsequence_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ)
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ,
      ∀ φ : ℕ → ℕ, ∀ᶠ k : ℕ in atTop,
        prob_14_12_obligation_5_geTailExpectation μ (Xseq (φ k)) M ≤
          ENNReal.ofReal ε := by
  rcases prob_14_12_uniformIntegrableVariables_subsequence_tail_bound_with_nonneg
      μ Xseq hUI hε with ⟨M, _hM_nonneg, htail⟩
  exact ⟨M, htail⟩

theorem sequence_ui_supplies_subsequence_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ)
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ,
      ∀ φ : ℕ → ℕ, ∀ᶠ k : ℕ in atTop,
        prob_14_12_obligation_5_geTailExpectation μ (Xseq (φ k)) M ≤
          ENNReal.ofReal ε :=
  prob_14_12_uniformIntegrableVariables_subsequence_tail_bound μ Xseq hUI hε

def prob_14_12_obligation_5_strictTailIntegrand
    {Ω : Type*} (X : Ω → ℝ) (R : ℝ) : Ω → ℝ≥0∞ :=
  fun ω => Set.indicator {η : Ω | R < |X η|}
    (fun η : Ω => ENNReal.ofReal |X η|) ω

def prob_14_12_obligation_5_strictTailExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, prob_14_12_obligation_5_strictTailIntegrand X R ω ∂μ

def prob_14_12_truncate (M : ℝ) (x : ℝ) : ℝ :=
  min (max x (-M)) M

theorem prob_14_12_truncation_error_abs_le_abs
    {M x : ℝ} (hM : 0 ≤ M) :
    |x - prob_14_12_truncate M x| ≤ |x| := by
  by_cases hxlo : x < -M
  · have hmax : max x (-M) = -M := max_eq_right (le_of_lt hxlo)
    have hmin : min (max x (-M)) M = -M := by
      rw [hmax]
      exact min_eq_left (by linarith)
    have hx_nonpos : x ≤ 0 := by linarith
    have habs_x : |x| = -x := abs_of_nonpos hx_nonpos
    have hdiff_nonpos : x - (-M) ≤ 0 := by linarith
    rw [prob_14_12_truncate, hmin, abs_of_nonpos hdiff_nonpos, habs_x]
    linarith
  · by_cases hxhi : M < x
    · have hmax : max x (-M) = x := max_eq_left (by linarith)
      have hmin : min (max x (-M)) M = M := by
        rw [hmax]
        exact min_eq_right (le_of_lt hxhi)
      have hx_nonneg : 0 ≤ x := by linarith
      have habs_x : |x| = x := abs_of_nonneg hx_nonneg
      have hdiff_nonneg : 0 ≤ x - M := by linarith
      rw [prob_14_12_truncate, hmin, abs_of_nonneg hdiff_nonneg, habs_x]
      linarith
    · have hge : -M ≤ x := le_of_not_gt hxlo
      have hle : x ≤ M := le_of_not_gt hxhi
      have hmax : max x (-M) = x := max_eq_left hge
      have hmin : min (max x (-M)) M = x := by
        rw [hmax]
        exact min_eq_left hle
      simp [prob_14_12_truncate, hmin]

theorem prob_14_12_truncate_eq_self_of_not_strict_tail
    {M x : ℝ} (hnot : ¬ M < |x|) :
    prob_14_12_truncate M x = x := by
  have hle_abs : |x| ≤ M := le_of_not_gt hnot
  have hge : -M ≤ x := (abs_le.mp hle_abs).1
  have hle : x ≤ M := (abs_le.mp hle_abs).2
  unfold prob_14_12_truncate
  rw [max_eq_left hge, min_eq_left hle]

theorem prob_14_12_obligation_5_geTailIntegrand_measurable
    {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
    (M : ℝ) :
    Measurable (prob_14_12_obligation_5_geTailIntegrand X M) := by
  have hAbs : Measurable fun ω : Ω => |X ω| := measurable_abs.comp hX
  have hSet : MeasurableSet {ω : Ω | M ≤ |X ω|} :=
    measurableSet_le measurable_const hAbs
  exact (ENNReal.measurable_ofReal.comp hAbs).indicator hSet

theorem prob_14_12_obligation_5_strictTail_le_liminf_geTail
    {Ω : Type*} (Y : ℕ → Ω → ℝ) (X : Ω → ℝ) {M R : ℝ}
    (hMR : M < R) {ω : Ω}
    (hω : Tendsto (fun n : ℕ => Y n ω) atTop (𝓝 (X ω))) :
    prob_14_12_obligation_5_strictTailIntegrand X R ω ≤
      liminf
        (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
        atTop := by
  by_cases htail : R < |X ω|
  · have hAbs : Tendsto (fun n : ℕ => |Y n ω|) atTop (𝓝 |X ω|) := hω.abs
    have hMlimit : M < |X ω| := lt_trans hMR htail
    have hEventuallyTail : ∀ᶠ n : ℕ in atTop, M ≤ |Y n ω| := by
      filter_upwards [hAbs.eventually (Ioi_mem_nhds hMlimit)] with n hn
      exact le_of_lt hn
    have hTailTendsto :
        Tendsto
          (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
          atTop (𝓝 (ENNReal.ofReal |X ω|)) := by
      have hOfReal :
          Tendsto (fun n : ℕ => ENNReal.ofReal |Y n ω|)
            atTop (𝓝 (ENNReal.ofReal |X ω|)) :=
        ENNReal.tendsto_ofReal hAbs
      refine hOfReal.congr' ?_
      filter_upwards [hEventuallyTail] with n hn
      simp [prob_14_12_obligation_5_geTailIntegrand, Set.indicator, hn]
    have hLeft :
        prob_14_12_obligation_5_strictTailIntegrand X R ω =
          ENNReal.ofReal |X ω| := by
      simp [prob_14_12_obligation_5_strictTailIntegrand, Set.indicator, htail]
    rw [hLeft, Filter.Tendsto.liminf_eq hTailTendsto]
  · have hLeft :
        prob_14_12_obligation_5_strictTailIntegrand X R ω = 0 := by
      simp [prob_14_12_obligation_5_strictTailIntegrand, Set.indicator, htail]
    rw [hLeft]
    exact zero_le _

theorem prob_14_12_obligation_5_lintegral_liminf_geTail_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hY : ∀ n : ℕ, Measurable (Y n)) (M : ℝ) :
    (∫⁻ ω,
        liminf
          (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
          atTop ∂μ) ≤
      liminf
        (fun n : ℕ =>
          prob_14_12_obligation_5_geTailExpectation μ (Y n) M)
        atTop := by
  simpa [prob_14_12_obligation_5_geTailExpectation] using
    lintegral_liminf_le
      (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand_measurable (hY n) M)

theorem prob_14_12_obligation_5_liminf_geTailExpectation_le_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (M : ℝ) {C : ℝ≥0∞}
    (hTailBound : ∀ᶠ n : ℕ in atTop,
      prob_14_12_obligation_5_geTailExpectation μ (Y n) M ≤ C) :
    liminf
        (fun n : ℕ =>
          prob_14_12_obligation_5_geTailExpectation μ (Y n) M)
        atTop ≤ C := by
  exact Filter.liminf_le_of_frequently_le hTailBound.frequently

theorem prob_14_12_ae_subsequence_fatou_tail_transfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hY : ∀ n : ℕ, Measurable (Y n)) {M R : ℝ} (hMR : M < R)
    {C : ℝ≥0∞}
    (hAeTendsto : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Y n ω) atTop (𝓝 (X ω)))
    (hTailBound : ∀ᶠ n : ℕ in atTop,
      prob_14_12_obligation_5_geTailExpectation μ (Y n) M ≤ C) :
    prob_14_12_obligation_5_strictTailExpectation μ X R ≤ C := by
  have hPointwise : ∀ᵐ ω ∂μ,
      prob_14_12_obligation_5_strictTailIntegrand X R ω ≤
        liminf
          (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
          atTop :=
    hAeTendsto.mono fun ω hω =>
      prob_14_12_obligation_5_strictTail_le_liminf_geTail Y X hMR hω
  have hLeftLeLiminf :
      prob_14_12_obligation_5_strictTailExpectation μ X R ≤
        ∫⁻ ω,
          liminf
            (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
            atTop ∂μ := by
    exact lintegral_mono_ae hPointwise
  have hFatou :
      (∫⁻ ω,
          liminf
            (fun n : ℕ => prob_14_12_obligation_5_geTailIntegrand (Y n) M ω)
            atTop ∂μ) ≤
        liminf
          (fun n : ℕ =>
            prob_14_12_obligation_5_geTailExpectation μ (Y n) M)
          atTop := by
    exact prob_14_12_obligation_5_lintegral_liminf_geTail_le μ Y hY M
  have hLiminfLe :
      liminf
          (fun n : ℕ =>
            prob_14_12_obligation_5_geTailExpectation μ (Y n) M)
          atTop ≤ C := by
    exact prob_14_12_obligation_5_liminf_geTailExpectation_le_of_eventually
      μ Y M hTailBound
  exact (hLeftLeLiminf.trans hFatou).trans hLiminfLe

theorem ae_subsequence_fatou_tail_transfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hY : ∀ n : ℕ, Measurable (Y n)) {M R : ℝ} (hMR : M < R)
    {C : ℝ≥0∞}
    (hAeTendsto : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Y n ω) atTop (𝓝 (X ω)))
    (hTailBound : ∀ᶠ n : ℕ in atTop,
      prob_14_12_obligation_5_geTailExpectation μ (Y n) M ≤ C) :
    prob_14_12_obligation_5_strictTailExpectation μ X R ≤ C :=
  prob_14_12_ae_subsequence_fatou_tail_transfer
    μ Y X hY hMR hAeTendsto hTailBound

theorem prob_14_12_truncation_error_le_strictTailIntegrand
    {Ω : Type*} (X : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M) (ω : Ω) :
    ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ≤
      prob_14_12_obligation_5_strictTailIntegrand X M ω := by
  by_cases htail : M < |X ω|
  · have hle :=
      prob_14_12_truncation_error_abs_le_abs (M := M) (x := X ω) hM
    have hle' :
        ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ≤
          ENNReal.ofReal |X ω| :=
      ENNReal.ofReal_le_ofReal hle
    simpa [prob_14_12_obligation_5_strictTailIntegrand, Set.indicator, htail]
      using hle'
  · have htrunc : prob_14_12_truncate M (X ω) = X ω :=
      prob_14_12_truncate_eq_self_of_not_strict_tail
        (M := M) (x := X ω) htail
    simp [prob_14_12_obligation_5_strictTailIntegrand, Set.indicator, htail, htrunc]

theorem prob_14_12_truncation_error_lintegral_le_strictTailExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ) ≤
      prob_14_12_obligation_5_strictTailExpectation μ X M := by
  simpa [prob_14_12_obligation_5_strictTailExpectation] using
    (lintegral_mono
      (fun ω => prob_14_12_truncation_error_le_strictTailIntegrand X hM ω))

theorem prob_14_12_strictTail_bound_controls_limit_truncation_error
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {ε R : ℝ} (hR : 0 ≤ R)
    (hStrictTail :
      prob_14_12_obligation_5_strictTailExpectation μ X R ≤
        ENNReal.ofReal ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ) ≤
        ENNReal.ofReal ε := by
  refine ⟨R, hR, ?_⟩
  exact
    (prob_14_12_truncation_error_lintegral_le_strictTailExpectation
      μ X hR).trans hStrictTail

theorem strict_tail_bound_to_limit_truncation_error
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {ε R : ℝ} (hR : 0 ≤ R)
    (hStrictTail :
      prob_14_12_obligation_5_strictTailExpectation μ X R ≤
        ENNReal.ofReal ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ) ≤
        ENNReal.ofReal ε :=
  prob_14_12_strictTail_bound_controls_limit_truncation_error
    μ X hR hStrictTail

theorem prob_14_12_limit_truncation_tail_obligation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n))
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq)
    (hProb : prob_14_12_convergesInProbability μ Xseq X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ) ≤
        ENNReal.ofReal ε := by
  rcases prob_14_12_convergence_probability_extracts_ae_subsequence
      μ Xseq X hProb with
    ⟨φ, _hφmono, hAeTendsto⟩
  rcases prob_14_12_uniformIntegrableVariables_subsequence_tail_bound_with_nonneg
      μ Xseq hUI hε with
    ⟨M0, hM0_nonneg, hTailAllSubseq⟩
  let Y : ℕ → Ω → ℝ := fun k ω => Xseq (φ k) ω
  let R : ℝ := M0 + 1
  have hMR : M0 < R := by
    simp [R]
  have hR_nonneg : 0 ≤ R := by
    linarith
  have hY : ∀ k : ℕ, Measurable (Y k) := by
    intro k
    exact hXseq (φ k)
  have hAeY :
      ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => Y k ω) atTop (𝓝 (X ω)) := by
    simpa [Y] using hAeTendsto
  have hTailBound :
      ∀ᶠ k : ℕ in atTop,
        prob_14_12_obligation_5_geTailExpectation μ (Y k) M0 ≤
          ENNReal.ofReal ε := by
    simpa [Y] using hTailAllSubseq φ
  have hStrictTail :
      prob_14_12_obligation_5_strictTailExpectation μ X R ≤
        ENNReal.ofReal ε :=
    prob_14_12_ae_subsequence_fatou_tail_transfer
      μ Y X hY hMR hAeY hTailBound
  exact
    prob_14_12_strictTail_bound_controls_limit_truncation_error
      (μ := μ) (X := X) (ε := ε) (R := R) hR_nonneg hStrictTail
