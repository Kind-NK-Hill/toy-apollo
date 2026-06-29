/-
TASK ID: prob_14_1_grid_cdf_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_1_finite_law_support

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

def prob_14_1_countGridSet (i : ℕ) : Set ℝ :=
  {x : ℝ | ∃ k : ℕ, k ≤ i ∧ x = (k : ℝ)}

theorem prob_14_1_countGridSet_measurable (i : ℕ) :
    MeasurableSet (prob_14_1_countGridSet i) := by
  rw [prob_14_1_countGridSet]
  have hset :
      {x : ℝ | ∃ k : ℕ, k ≤ i ∧ x = (k : ℝ)} =
        ⋃ k : ℕ, ⋃ _ : k ≤ i, ({x : ℝ | x = (k : ℝ)} : Set ℝ) := by
    ext x
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ =>
      (by
        simpa only [Set.setOf_eq_eq_singleton] using
          measurableSet_singleton (k : ℝ))

theorem prob_14_1_countGrid_support_of_nat_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℕ} {i : ℕ}
    (hX : Measurable fun ω : Ω => (X ω : ℝ))
    (hBound : ∀ ω : Ω, X ω ≤ i) :
    (Measure.map (fun ω : Ω => (X ω : ℝ)) P)
        (prob_14_1_countGridSet i)ᶜ = 0 := by
  have hMeas :
      MeasurableSet (prob_14_1_countGridSet i)ᶜ :=
    (prob_14_1_countGridSet_measurable i).compl
  rw [Measure.map_apply hX hMeas]
  have hpre :
      (fun ω : Ω => (X ω : ℝ)) ⁻¹'
          (prob_14_1_countGridSet i)ᶜ = ∅ := by
    ext ω
    constructor
    · intro hω
      exfalso
      exact hω ⟨X ω, hBound ω, rfl⟩
    · intro hω
      cases hω
  rw [hpre]
  simp

theorem prob_14_1_white_count_grid_support_of_nat_count_model
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ)
    (X : ℕ → Ω → ℕ)
    (hLaw :
      ∀ᶠ i in atTop,
        (whiteCountLaws i : Measure ℝ) =
          Measure.map (fun ω : Ω => (X i ω : ℝ)) P)
    (hMeas :
      ∀ᶠ i in atTop,
        Measurable fun ω : Ω => (X i ω : ℝ))
    (hBound :
      ∀ᶠ i in atTop, 1 ≤ i ∧ ∀ ω : Ω, X i ω ≤ i) :
    ∀ᶠ i in atTop,
      1 ≤ i ∧
        (whiteCountLaws i : Measure ℝ)
          (prob_14_1_countGridSet i)ᶜ = 0 := by
  filter_upwards [hLaw, hMeas, hBound] with i hLaw_i hMeas_i hBound_i
  constructor
  · exact hBound_i.1
  · rw [hLaw_i]
    exact prob_14_1_countGrid_support_of_nat_bound P hMeas_i hBound_i.2

theorem prob_14_1_polyaWhiteCountLaw_countGrid_support
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i : ℕ) :
    (prob_14_1_polyaWhiteCountLaw w b hw hb i : Measure ℝ)
      (prob_14_1_countGridSet i)ᶜ = 0 := by
  rw [prob_14_1_polyaWhiteCountLaw]
  change
    (((prob_14_1_polyaFinPathPMF w b hw hb i).map
      (fun path : prob_14_1_FinColorPath i =>
        (prob_14_1_finWhiteCount path : ℝ))).toMeasure)
      (prob_14_1_countGridSet i)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
    ((prob_14_1_polyaFinPathPMF w b hw hb i).map
      (fun path : prob_14_1_FinColorPath i =>
        (prob_14_1_finWhiteCount path : ℝ)))
    (prob_14_1_countGridSet_measurable i).compl]
  rw [PMF.support_map]
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  constructor
  · intro hx
    rcases hx.1 with ⟨path, _hpath, rfl⟩
    exact False.elim (hx.2
      ⟨prob_14_1_finWhiteCount path,
        prob_14_1_finWhiteCount_le_length path, rfl⟩)
  · intro hx
    cases hx

theorem prob_14_1_white_count_grid_support
    (S : prob_14_1_PolyaUrnBetaSetup) :
    ∀ᶠ i in atTop,
      1 ≤ i ∧
        (S.whiteCountLaws i : Measure ℝ)
          (prob_14_1_countGridSet i)ᶜ = 0 := by
  exact eventually_atTop.2
    ⟨1, fun i hi =>
      ⟨hi, by
        rw [prob_14_1_PolyaUrnBetaSetup.whiteCountLaws]
        exact prob_14_1_polyaWhiteCountLaw_countGrid_support
          S.w_pos S.b_pos i⟩⟩

def prob_14_1_scaledGridSet (i : ℕ) : Set ℝ :=
  {y : ℝ | ∃ k ∈ Finset.range (i + 1), y = (k : ℝ) / (i : ℝ)}

def prob_14_1_scaledPolyaGridCdf (w b : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (i + 1)).sum fun k : ℕ =>
    if (k : ℝ) / (i : ℝ) ≤ x then
      prob_14_1_polyaWhiteMassFormula w b i k
    else
      0

def prob_14_1_leftTailMass (w b : ℝ) (i : ℕ) (eps : ℝ) : ℝ :=
  (Finset.range (i + 1)).sum fun k : ℕ =>
    if (k : ℝ) / (i : ℝ) ≤ eps then
      prob_14_1_polyaWhiteMassFormula w b i k
    else
      0

def prob_14_1_rightTailMass (w b : ℝ) (i : ℕ) (eps : ℝ) : ℝ :=
  (Finset.range (i + 1)).sum fun k : ℕ =>
    if 1 - eps ≤ (k : ℝ) / (i : ℝ) then
      prob_14_1_polyaWhiteMassFormula w b i k
    else
      0

theorem prob_14_1_leftTailMass_eq_scaledPolyaGridCdf
    (w b : ℝ) (i : ℕ) (eps : ℝ) :
    prob_14_1_leftTailMass w b i eps =
      prob_14_1_scaledPolyaGridCdf w b i eps := by
  rfl

theorem prob_14_1_leftTailMass_nonneg
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (i : ℕ) (eps : ℝ) :
    0 ≤ prob_14_1_leftTailMass w b i eps := by
  rw [prob_14_1_leftTailMass]
  apply Finset.sum_nonneg
  intro k hk
  by_cases hk_eps : (k : ℝ) / (i : ℝ) ≤ eps
  · have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp [hk_eps, (prob_14_1_polyaWhiteMassFormula_pos hw hb hk_le_i).le]
  · simp [hk_eps]

theorem prob_14_1_rightTailMass_nonneg
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (i : ℕ) (eps : ℝ) :
    0 ≤ prob_14_1_rightTailMass w b i eps := by
  rw [prob_14_1_rightTailMass]
  apply Finset.sum_nonneg
  intro k hk
  by_cases hk_eps : 1 - eps ≤ (k : ℝ) / (i : ℝ)
  · have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp [hk_eps, (prob_14_1_polyaWhiteMassFormula_pos hw hb hk_le_i).le]
  · simp [hk_eps]

theorem prob_14_1_leftTailMass_mono_eps
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (i : ℕ) {eps₁ eps₂ : ℝ} (heps : eps₁ ≤ eps₂) :
    prob_14_1_leftTailMass w b i eps₁ ≤
      prob_14_1_leftTailMass w b i eps₂ := by
  rw [prob_14_1_leftTailMass, prob_14_1_leftTailMass]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk₁ : (k : ℝ) / (i : ℝ) ≤ eps₁
  · have hk₂ : (k : ℝ) / (i : ℝ) ≤ eps₂ := le_trans hk₁ heps
    simp [hk₁, hk₂]
  · by_cases hk₂ : (k : ℝ) / (i : ℝ) ≤ eps₂
    · have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [hk₁, hk₂, (prob_14_1_polyaWhiteMassFormula_pos hw hb hk_le_i).le]
    · simp [hk₁, hk₂]

theorem prob_14_1_rightTailMass_mono_eps
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (i : ℕ) {eps₁ eps₂ : ℝ} (heps : eps₁ ≤ eps₂) :
    prob_14_1_rightTailMass w b i eps₁ ≤
      prob_14_1_rightTailMass w b i eps₂ := by
  rw [prob_14_1_rightTailMass, prob_14_1_rightTailMass]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk₁ : 1 - eps₁ ≤ (k : ℝ) / (i : ℝ)
  · have hthreshold : 1 - eps₂ ≤ 1 - eps₁ := by linarith
    have hk₂ : 1 - eps₂ ≤ (k : ℝ) / (i : ℝ) := le_trans hthreshold hk₁
    simp [hk₁, hk₂]
  · by_cases hk₂ : 1 - eps₂ ≤ (k : ℝ) / (i : ℝ)
    · have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [hk₁, hk₂, (prob_14_1_polyaWhiteMassFormula_pos hw hb hk_le_i).le]
    · simp [hk₁, hk₂]

def prob_14_1_gridCdfLimit
    (w b : ℝ) (beta : prob_14_1_BetaLawData w b) : Prop :=
  ∀ x : ℝ,
    ContinuousAt (fun y : ℝ => ((beta.law : Measure ℝ) (Set.Iic y)).toReal) x →
      Tendsto
        (fun i : ℕ => prob_14_1_scaledPolyaGridCdf w b i x)
        atTop
        (𝓝 (((beta.law : Measure ℝ) (Set.Iic x)).toReal))

theorem prob_14_1_grid_point_nonneg_of_one_le {i k : ℕ} (hi : 1 ≤ i) :
    0 ≤ (k : ℝ) / (i : ℝ) := by
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi_pos_nat
  exact div_nonneg (by exact_mod_cast Nat.zero_le k) hi_pos.le

theorem prob_14_1_grid_point_le_one_of_mem_range {i k : ℕ}
    (hi : 1 ≤ i) (hk : k ∈ Finset.range (i + 1)) :
    (k : ℝ) / (i : ℝ) ≤ 1 := by
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi_pos_nat
  have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk_le_i_real : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hk_le_i
  rw [div_le_iff₀ hi_pos]
  simpa using hk_le_i_real

theorem prob_14_1_rightTailMass_reflect_leftTail
    {w b eps : ℝ} {i : ℕ} (hi : 1 ≤ i) :
    prob_14_1_rightTailMass w b i eps =
      prob_14_1_leftTailMass b w i eps := by
  rw [prob_14_1_rightTailMass, prob_14_1_leftTailMass]
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi_pos_nat
  refine Finset.sum_nbij'
    (s := Finset.range (i + 1)) (t := Finset.range (i + 1))
    (f := fun k : ℕ =>
      if 1 - eps ≤ (k : ℝ) / (i : ℝ) then
        prob_14_1_polyaWhiteMassFormula w b i k
      else
        0)
    (g := fun j : ℕ =>
      if (j : ℝ) / (i : ℝ) ≤ eps then
        prob_14_1_polyaWhiteMassFormula b w i j
      else
        0)
    (fun k : ℕ => i - k) (fun j : ℕ => i - j) ?_ ?_ ?_ ?_ ?_
  · intro k _hk
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le i k))
  · intro j _hj
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le i j))
  · intro k hk
    have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact Nat.sub_sub_self hk_le_i
  · intro j hj
    have hj_le_i : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact Nat.sub_sub_self hj_le_i
  · intro k hk
    have hk_le_i : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hratio :
        ((i - k : ℕ) : ℝ) / (i : ℝ) = 1 - (k : ℝ) / (i : ℝ) := by
      rw [Nat.cast_sub hk_le_i]
      field_simp [hi_pos.ne']
    have hiff :
        (1 - eps ≤ (k : ℝ) / (i : ℝ)) ↔
          ((i - k : ℕ) : ℝ) / (i : ℝ) ≤ eps := by
      rw [hratio]
      constructor <;> intro h <;> linarith
    by_cases hright : 1 - eps ≤ (k : ℝ) / (i : ℝ)
    · have hleft : ((i - k : ℕ) : ℝ) / (i : ℝ) ≤ eps := hiff.mp hright
      simp [hright, hleft,
        prob_14_1_polyaWhiteMassFormula_reflect (w := w) (b := b) hk_le_i]
    · have hleft : ¬ ((i - k : ℕ) : ℝ) / (i : ℝ) ≤ eps := by
        intro h
        exact hright (hiff.mpr h)
      simp [hright, hleft]

theorem prob_14_1_scaledPolyaGridCdf_eq_zero_of_lt_zero
    {w b x : ℝ} {i : ℕ} (hi : 1 ≤ i) (hx : x < 0) :
    prob_14_1_scaledPolyaGridCdf w b i x = 0 := by
  rw [prob_14_1_scaledPolyaGridCdf]
  apply Finset.sum_eq_zero
  intro k _hk
  have hnonneg : 0 ≤ (k : ℝ) / (i : ℝ) :=
    prob_14_1_grid_point_nonneg_of_one_le (i := i) (k := k) hi
  have hnot : ¬ (k : ℝ) / (i : ℝ) ≤ x :=
    not_le.mpr (lt_of_lt_of_le hx hnonneg)
  simp [hnot]

theorem prob_14_1_scaledPolyaGridCdf_eq_mass_zero_at_zero
    {w b : ℝ} {i : ℕ} (hi : 1 ≤ i) :
    prob_14_1_scaledPolyaGridCdf w b i 0 =
      prob_14_1_polyaWhiteMassFormula w b i 0 := by
  rw [prob_14_1_scaledPolyaGridCdf]
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi_pos_nat
  have hfilter :
      (Finset.range (i + 1)).filter
          (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ 0) = {0} := by
    ext k
    constructor
    · intro hk
      have hk_le_zero : (k : ℝ) / (i : ℝ) ≤ 0 :=
        (Finset.mem_filter.mp hk).2
      by_contra hk_ne_zero
      have hk_ne_zero_nat : k ≠ 0 := by
        intro hk_zero
        exact hk_ne_zero (by simp [hk_zero])
      have hk_pos_nat : 0 < k := Nat.pos_of_ne_zero hk_ne_zero_nat
      have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
      have hdiv_pos : 0 < (k : ℝ) / (i : ℝ) := div_pos hk_pos hi_pos
      linarith
    · intro hk
      have hk_zero : k = 0 := by simpa using hk
      rw [Finset.mem_filter]
      constructor
      · simp [hk_zero]
      · simp [hk_zero]
  rw [← Finset.sum_filter, hfilter]
  simp

theorem prob_14_1_scaledPolyaGridCdf_eq_total_mass_of_one_le
    {w b x : ℝ} {i : ℕ} (hi : 1 ≤ i) (hx : 1 ≤ x) :
    prob_14_1_scaledPolyaGridCdf w b i x =
      (Finset.range (i + 1)).sum
        (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b i k) := by
  rw [prob_14_1_scaledPolyaGridCdf]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le_one : (k : ℝ) / (i : ℝ) ≤ 1 :=
    prob_14_1_grid_point_le_one_of_mem_range (i := i) (k := k) hi hk
  have hk_le_x : (k : ℝ) / (i : ℝ) ≤ x := le_trans hk_le_one hx
  simp [hk_le_x]

theorem prob_14_1_betaDensity_eq_zero_of_nonpos
    {w b C y : ℝ} (hy : y ≤ 0) :
    prob_14_1_betaDensity w b C y = 0 := by
  simp [prob_14_1_betaDensity, Set.mem_Ioo, not_lt.mpr hy]

theorem prob_14_1_betaDensity_eq_zero_of_one_le
    {w b C y : ℝ} (hy : 1 ≤ y) :
    prob_14_1_betaDensity w b C y = 0 := by
  have hnot : ¬ y ∈ Set.Ioo (0 : ℝ) 1 := by
    intro hyIoo
    exact not_lt.mpr hy hyIoo.2
  simp [prob_14_1_betaDensity, hnot]

theorem prob_14_1_beta_law_Iic_eq_zero_of_nonpos
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b)
    {x : ℝ} (hx : x ≤ 0) :
    (beta.law : Measure ℝ) (Set.Iic x) = 0 := by
  rw [beta.density_represents_law (Set.Iic x) measurableSet_Iic]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ Set.Iic x
    · have hy_nonpos : y ≤ 0 := le_trans hy hx
      simp [Set.indicator_of_mem hy,
        prob_14_1_betaDensity_eq_zero_of_nonpos (w := w) (b := b)
          (C := beta.normalizingConstant) hy_nonpos]
    · simp [Set.indicator_of_notMem hy]

theorem prob_14_1_beta_law_Iic_toReal_eq_zero_of_nonpos
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b)
    {x : ℝ} (hx : x ≤ 0) :
    ((beta.law : Measure ℝ) (Set.Iic x)).toReal = 0 := by
  rw [prob_14_1_beta_law_Iic_eq_zero_of_nonpos beta hx]
  simp

theorem prob_14_1_left_of_support_gridCdf_tendsto
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b)
    {x : ℝ} (hx : x < 0) :
    Tendsto
      (fun i : ℕ => prob_14_1_scaledPolyaGridCdf w b i x)
      atTop
      (𝓝 (((beta.law : Measure ℝ) (Set.Iic x)).toReal)) := by
  have hgrid :
      ∀ᶠ i in atTop,
        prob_14_1_scaledPolyaGridCdf w b i x = 0 := by
    exact eventually_atTop.2
      ⟨1, fun i hi =>
        prob_14_1_scaledPolyaGridCdf_eq_zero_of_lt_zero
          (w := w) (b := b) (x := x) hi hx⟩
  have hbeta :
      ((beta.law : Measure ℝ) (Set.Iic x)).toReal = 0 :=
    prob_14_1_beta_law_Iic_toReal_eq_zero_of_nonpos beta (le_of_lt hx)
  simpa [hbeta] using
    (tendsto_const_nhds (x := (0 : ℝ))).congr'
      (hgrid.mono fun _ hi => hi.symm)

theorem prob_14_1_beta_law_Iic_eq_one_of_one_le
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b)
    {x : ℝ} (hx : 1 ≤ x) :
    (beta.law : Measure ℝ) (Set.Iic x) = 1 := by
  have hcompl :
      (beta.law : Measure ℝ) (Set.Iic x)ᶜ = 0 := by
    rw [beta.density_represents_law (Set.Iic x)ᶜ measurableSet_Iic.compl]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ (Set.Iic x)ᶜ
      · have hxy : x < y := not_le.mp hy
        have hy_one : 1 ≤ y := le_trans hx (le_of_lt hxy)
        rw [Set.indicator_of_mem hy]
        simp [prob_14_1_betaDensity_eq_zero_of_one_le (w := w) (b := b)
          (C := beta.normalizingConstant) hy_one]
      · rw [Set.indicator_of_notMem hy]
        rfl
  have hEq :
      (beta.law : Measure ℝ) (Set.Iic x) =
        (beta.law : Measure ℝ) Set.univ := by
    exact measure_eq_measure_of_null_diff
      (by intro y _hy; exact trivial)
      (by
        simpa [Set.diff_eq, Set.compl_inter, Set.univ_inter] using hcompl)
  rw [hEq]
  simpa using ProbabilityMeasure.coeFn_univ beta.law

theorem prob_14_1_beta_law_Iic_toReal_eq_one_of_one_le
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b)
    {x : ℝ} (hx : 1 ≤ x) :
    ((beta.law : Measure ℝ) (Set.Iic x)).toReal = 1 := by
  rw [prob_14_1_beta_law_Iic_eq_one_of_one_le beta hx]
  simp

theorem prob_14_1_right_of_support_gridCdf_tendsto
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (beta : prob_14_1_BetaLawData w b) {x : ℝ} (hx : 1 ≤ x) :
    Tendsto
      (fun i : ℕ => prob_14_1_scaledPolyaGridCdf w b i x)
      atTop
      (𝓝 (((beta.law : Measure ℝ) (Set.Iic x)).toReal)) := by
  have hgrid :
      ∀ᶠ i in atTop,
        prob_14_1_scaledPolyaGridCdf w b i x = 1 := by
    exact eventually_atTop.2
      ⟨1, fun i hi => by
        rw [prob_14_1_scaledPolyaGridCdf_eq_total_mass_of_one_le
          (w := w) (b := b) (x := x) hi hx]
        exact prob_14_1_polyaWhiteMassFormula_sum_range_eq_one hw hb i⟩
  have hbeta :
      ((beta.law : Measure ℝ) (Set.Iic x)).toReal = 1 :=
    prob_14_1_beta_law_Iic_toReal_eq_one_of_one_le beta hx
  simpa [hbeta] using
    (tendsto_const_nhds (x := (1 : ℝ))).congr'
      (hgrid.mono fun _ hi => hi.symm)

theorem prob_14_1_zero_gridCdf_tendsto
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (beta : prob_14_1_BetaLawData w b) :
    Tendsto
      (fun i : ℕ => prob_14_1_scaledPolyaGridCdf w b i 0)
      atTop
      (𝓝 (((beta.law : Measure ℝ) (Set.Iic 0)).toReal)) := by
  have hgrid :
      ∀ᶠ i in atTop,
        prob_14_1_scaledPolyaGridCdf w b i 0 =
          prob_14_1_polyaWhiteMassFormula w b i 0 := by
    exact eventually_atTop.2
      ⟨1, fun i hi =>
        prob_14_1_scaledPolyaGridCdf_eq_mass_zero_at_zero
          (w := w) (b := b) hi⟩
  have hbeta :
      ((beta.law : Measure ℝ) (Set.Iic 0)).toReal = 0 :=
    prob_14_1_beta_law_Iic_toReal_eq_zero_of_nonpos beta le_rfl
  simpa [hbeta] using
    (prob_14_1_polyaWhiteMassFormula_zero_tendsto_zero hw hb).congr'
      (hgrid.mono fun _ hi => hi.symm)

theorem prob_14_1_gridCdfLimit_of_interior
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (beta : prob_14_1_BetaLawData w b)
    (hInterior :
      ∀ x : ℝ,
        0 < x → x < 1 →
          ContinuousAt
            (fun y : ℝ => ((beta.law : Measure ℝ) (Set.Iic y)).toReal) x →
          Tendsto
            (fun i : ℕ => prob_14_1_scaledPolyaGridCdf w b i x)
            atTop
            (𝓝 (((beta.law : Measure ℝ) (Set.Iic x)).toReal))) :
    prob_14_1_gridCdfLimit w b beta := by
  intro x hxcont
  by_cases hxneg : x < 0
  · exact prob_14_1_left_of_support_gridCdf_tendsto beta hxneg
  · by_cases hxzero : x = 0
    · subst x
      exact prob_14_1_zero_gridCdf_tendsto hw hb beta
    · have hxpos : 0 < x := lt_of_le_of_ne (not_lt.mp hxneg) (Ne.symm hxzero)
      by_cases hxlt1 : x < 1
      · exact hInterior x hxpos hxlt1 hxcont
      · have hxge1 : 1 ≤ x := not_lt.mp hxlt1
        exact prob_14_1_right_of_support_gridCdf_tendsto hw hb beta hxge1

theorem prob_14_1_range_succ_filter_and_eq_Icc_min (n lo hi : ℕ) :
    (Finset.range (n + 1)).filter (fun k : ℕ => lo ≤ k ∧ k ≤ hi) =
      Finset.Icc lo (min hi n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, le_min_iff]
  omega

theorem prob_14_1_range_succ_filter_and_eq_Icc_of_hi_le
    {n lo hi : ℕ} (hhi : hi ≤ n) :
    (Finset.range (n + 1)).filter (fun k : ℕ => lo ≤ k ∧ k ≤ hi) =
      Finset.Icc lo hi := by
  rw [prob_14_1_range_succ_filter_and_eq_Icc_min]
  simp [min_eq_left hhi]

theorem prob_14_1_sum_range_succ_ite_index_bounds_eq_sum_Icc_min
    {α : Type*} [AddCommMonoid α] (g : ℕ → α) (n lo hi : ℕ) :
    (Finset.range (n + 1)).sum
        (fun k : ℕ => if lo ≤ k ∧ k ≤ hi then g k else 0) =
      (Finset.Icc lo (min hi n)).sum g := by
  rw [← Finset.sum_filter]
  rw [prob_14_1_range_succ_filter_and_eq_Icc_min]

theorem prob_14_1_sum_range_succ_ite_index_bounds_eq_sum_Icc
    {α : Type*} [AddCommMonoid α] (g : ℕ → α)
    {n lo hi : ℕ} (hhi : hi ≤ n) :
    (Finset.range (n + 1)).sum
        (fun k : ℕ => if lo ≤ k ∧ k ≤ hi then g k else 0) =
      (Finset.Icc lo hi).sum g := by
  rw [← Finset.sum_filter]
  rw [prob_14_1_range_succ_filter_and_eq_Icc_of_hi_le hhi]

theorem prob_14_1_grid_div_mem_Icc_iff_mul_le
    {a c : ℝ} {n k : ℕ} (hn : 0 < n) :
    ((k : ℝ) / (n : ℝ) ∈ Set.Icc a c) ↔
      a * (n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ c * (n : ℝ) := by
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro hk
    constructor
    · have h := mul_le_mul_of_nonneg_right hk.1 hnℝ.le
      rwa [div_mul_cancel₀ _ hnℝ.ne'] at h
    · have h := mul_le_mul_of_nonneg_right hk.2 hnℝ.le
      rwa [div_mul_cancel₀ _ hnℝ.ne'] at h
  · intro hk
    constructor
    · rw [le_div_iff₀ hnℝ]
      exact hk.1
    · rw [div_le_iff₀ hnℝ]
      exact hk.2

theorem prob_14_1_grid_div_bounds_iff_mul_le
    {a c : ℝ} {n k : ℕ} (hn : 0 < n) :
    (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
      a * (n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ c * (n : ℝ) := by
  simpa [Set.mem_Icc] using
    prob_14_1_grid_div_mem_Icc_iff_mul_le
      (a := a) (c := c) (n := n) (k := k) hn

theorem prob_14_1_inv_nat_mul_sum_range_succ_ite_index_bounds_eq_Icc_min
    (g : ℕ → ℝ) (n lo hi : ℕ) :
    (1 / (n : ℝ)) *
        (Finset.range (n + 1)).sum
          (fun k : ℕ => if lo ≤ k ∧ k ≤ hi then g k else 0) =
      (1 / (n : ℝ)) * (Finset.Icc lo (min hi n)).sum g := by
  rw [prob_14_1_sum_range_succ_ite_index_bounds_eq_sum_Icc_min]

theorem prob_14_1_inv_nat_mul_sum_range_succ_ite_index_bounds_eq_Icc
    (g : ℕ → ℝ) {n lo hi : ℕ} (hhi : hi ≤ n) :
    (1 / (n : ℝ)) *
        (Finset.range (n + 1)).sum
          (fun k : ℕ => if lo ≤ k ∧ k ≤ hi then g k else 0) =
      (1 / (n : ℝ)) * (Finset.Icc lo hi).sum g := by
  rw [prob_14_1_sum_range_succ_ite_index_bounds_eq_sum_Icc (g := g) hhi]

open scoped Pointwise

abbrev prob_14_1_punitIntLattice : Submodule ℤ (PUnit → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ PUnit))

theorem prob_14_1_punit_basisFun_range_eq_singleton :
    Set.range (Pi.basisFun ℝ PUnit) =
      ({Pi.basisFun ℝ PUnit PUnit.unit} : Set (PUnit → ℝ)) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    cases i
    simp
  · intro hv
    refine ⟨PUnit.unit, ?_⟩
    simpa using hv.symm

theorem prob_14_1_mem_punitIntLattice_iff_exists_int_coord
    (x : PUnit → ℝ) :
    x ∈ prob_14_1_punitIntLattice ↔
      ∃ m : ℤ, x PUnit.unit = (m : ℝ) := by
  rw [prob_14_1_punitIntLattice, prob_14_1_punit_basisFun_range_eq_singleton]
  constructor
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hcoord := congrArg (fun y : PUnit → ℝ => y PUnit.unit) hm
    simpa using hcoord.symm
  · rintro ⟨m, hm⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨m, ?_⟩
    ext i
    cases i
    simp [hm]

theorem prob_14_1_mem_scaled_punitIntLattice_iff_exists_int_div_coord
    (n : ℕ) (x : PUnit → ℝ) :
    x ∈ (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ)) ↔
      ∃ m : ℤ, x PUnit.unit = (m : ℝ) / (n : ℝ) := by
  constructor
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, hyx⟩
    rcases
      (prob_14_1_mem_punitIntLattice_iff_exists_int_coord y).mp hy with
      ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hcoord := congrArg (fun z : PUnit → ℝ => z PUnit.unit) hyx
    simpa [Pi.smul_apply, hm, div_eq_mul_inv, mul_comm] using hcoord.symm
  · rintro ⟨m, hm⟩
    refine Set.mem_smul_set.mpr ⟨fun _ : PUnit => (m : ℝ), ?_, ?_⟩
    · exact
        (prob_14_1_mem_punitIntLattice_iff_exists_int_coord _).mpr
          ⟨m, rfl⟩
    · ext i
      cases i
      simp [Pi.smul_apply, hm, div_eq_mul_inv, mul_comm]

theorem prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_int_div_coord
    (a c : ℝ) (n : ℕ) (x : PUnit → ℝ) :
    x ∈ ({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
        (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))) ↔
      ∃ m : ℤ,
        a ≤ (m : ℝ) / (n : ℝ) ∧
        (m : ℝ) / (n : ℝ) ≤ c ∧
        x PUnit.unit = (m : ℝ) / (n : ℝ) := by
  constructor
  · rintro ⟨hxI, hxL⟩
    rcases
      (prob_14_1_mem_scaled_punitIntLattice_iff_exists_int_div_coord n x).mp
        hxL with
      ⟨m, hm⟩
    refine ⟨m, ?_, ?_, hm⟩
    · simpa [hm] using hxI.1
    · simpa [hm] using hxI.2
  · rintro ⟨m, hma, hmc, hm⟩
    constructor
    · exact ⟨by simpa [hm] using hma, by simpa [hm] using hmc⟩
    · exact
        (prob_14_1_mem_scaled_punitIntLattice_iff_exists_int_div_coord n x).mpr
          ⟨m, hm⟩

theorem prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_nat_div_coord_of_nonneg
    {a c : ℝ} {n : ℕ} (ha : 0 ≤ a) (hn : 0 < n)
    (x : PUnit → ℝ) :
    x ∈ ({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
        (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))) ↔
      ∃ k : ℕ,
        a ≤ (k : ℝ) / (n : ℝ) ∧
        (k : ℝ) / (n : ℝ) ≤ c ∧
        x PUnit.unit = (k : ℝ) / (n : ℝ) := by
  constructor
  · intro hx
    rcases
      (prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_int_div_coord
        a c n x).mp hx with
      ⟨m, hma, hmc, hmx⟩
    have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
    have hm_div_nonneg : 0 ≤ (m : ℝ) / (n : ℝ) := le_trans ha hma
    have hm_cast_nonneg : 0 ≤ (m : ℝ) := by
      have hmul := mul_nonneg hm_div_nonneg hnℝ.le
      rwa [div_mul_cancel₀ _ hnℝ.ne'] at hmul
    have hm_nonneg : 0 ≤ m := by exact_mod_cast hm_cast_nonneg
    have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hm_nonneg)
    refine ⟨m.toNat, ?_, ?_, ?_⟩
    · simpa [hcast] using hma
    · simpa [hcast] using hmc
    · simpa [hcast] using hmx
  · rintro ⟨k, hka, hkc, hkx⟩
    exact
      (prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_int_div_coord
        a c n x).mpr
        ⟨(k : ℤ), by simpa using hka, by simpa using hkc, by simpa using hkx⟩

theorem prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_nat_mem_Icc_of_bounds
    {a c : ℝ} {n lo hi : ℕ} (ha : 0 ≤ a) (hn : 0 < n)
    (hIcc : ∀ k : ℕ,
      (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
        k ∈ Finset.Icc lo hi)
    (x : PUnit → ℝ) :
    x ∈ ({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
        (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))) ↔
      ∃ k : ℕ, k ∈ Finset.Icc lo hi ∧
        x PUnit.unit = (k : ℝ) / (n : ℝ) := by
  rw [prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_nat_div_coord_of_nonneg
    ha hn]
  constructor
  · rintro ⟨k, hka, hkc, hkx⟩
    exact ⟨k, (hIcc k).mp ⟨hka, hkc⟩, hkx⟩
  · rintro ⟨k, hkIcc, hkx⟩
    rcases (hIcc k).mpr hkIcc with ⟨hka, hkc⟩
    exact ⟨k, hka, hkc, hkx⟩

theorem prob_14_1_grid_nat_div_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (fun k : ℕ => fun _ : PUnit => (k : ℝ) / (n : ℝ)) := by
  intro k l hkl
  have hcoord := congrArg (fun x : PUnit → ℝ => x PUnit.unit) hkl
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmul : (k : ℝ) = (l : ℝ) := by
    have := congrArg (fun r : ℝ => r * (n : ℝ)) hcoord
    simpa [div_mul_cancel₀ _ hnℝ] using this
  exact Nat.cast_injective hmul

theorem prob_14_1_tsum_interval_scaled_punitIntLattice_eq_sum_Icc_of_bounds
    {a c : ℝ} {n lo hi : ℕ} (ha : 0 ≤ a) (hn : 0 < n)
    (hIcc : ∀ k : ℕ,
      (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
        k ∈ Finset.Icc lo hi)
    (F : (PUnit → ℝ) → ℝ) :
    (∑' x : ↑({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
        (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))), F x) =
      (Finset.Icc lo hi).sum
        (fun k : ℕ => F (fun _ : PUnit => (k : ℝ) / (n : ℝ))) := by
  classical
  let S : Set (PUnit → ℝ) :=
    {x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
      (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))
  change (∑' x : ↑S, F x) =
      (Finset.Icc lo hi).sum
        (fun k : ℕ => F (fun _ : PUnit => (k : ℝ) / (n : ℝ)))
  have hgrid_mem :
      ∀ k : {k : ℕ // k ∈ Finset.Icc lo hi},
        (fun _ : PUnit => (k.1 : ℝ) / (n : ℝ)) ∈ S := by
    intro k
    simpa [S] using
      ((prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_nat_mem_Icc_of_bounds
        (a := a) (c := c) (n := n) (lo := lo) (hi := hi) ha hn hIcc
        (fun _ : PUnit => (k.1 : ℝ) / (n : ℝ))).mpr
        ⟨k.1, k.2, rfl⟩)
  let gridEmbedding : {k : ℕ // k ∈ Finset.Icc lo hi} ↪ ↑S :=
    { toFun := fun k =>
        ⟨fun _ : PUnit => (k.1 : ℝ) / (n : ℝ), hgrid_mem k⟩
      inj' := by
        intro k l hkl
        apply Subtype.ext
        exact prob_14_1_grid_nat_div_injective hn (congrArg Subtype.val hkl) }
  let gridFinset : Finset ↑S :=
    (Finset.Icc lo hi).attach.map gridEmbedding
  have hcover : ∀ x : ↑S, x ∈ gridFinset := by
    intro x
    have hxS : (x : PUnit → ℝ) ∈
        ({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
          (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))) := by
      change (x : PUnit → ℝ) ∈ S
      exact x.2
    rcases
      (prob_14_1_mem_interval_scaled_punitIntLattice_iff_exists_nat_mem_Icc_of_bounds
        (a := a) (c := c) (n := n) (lo := lo) (hi := hi) ha hn hIcc
        (x : PUnit → ℝ)).mp hxS with
      ⟨k, hkIcc, hkx⟩
    change x ∈ (Finset.Icc lo hi).attach.map gridEmbedding
    rw [Finset.mem_map]
    refine ⟨⟨k, hkIcc⟩, by simp, ?_⟩
    apply Subtype.ext
    ext i
    cases i
    exact hkx.symm
  calc
    (∑' x : ↑S, F x) = gridFinset.sum (fun x : ↑S => F x) := by
      exact tsum_eq_sum
        (s := gridFinset) (fun x hx => (False.elim (hx (hcover x))))
    _ = (Finset.Icc lo hi).attach.sum
        (fun k : {k : ℕ // k ∈ Finset.Icc lo hi} =>
          F (fun _ : PUnit => (k.1 : ℝ) / (n : ℝ))) := by
      simp [gridFinset, gridEmbedding]
    _ = (Finset.Icc lo hi).sum
        (fun k : ℕ => F (fun _ : PUnit => (k : ℝ) / (n : ℝ))) := by
      simpa using
        (Finset.sum_attach (s := Finset.Icc lo hi)
          (f := fun k : ℕ => F (fun _ : PUnit => (k : ℝ) / (n : ℝ))))

theorem prob_14_1_tsum_interval_scaled_punitIntLattice_div_nat_eq_inv_mul_sum_Icc_of_bounds
    {a c : ℝ} {n lo hi : ℕ} (ha : 0 ≤ a) (hn : 0 < n)
    (hIcc : ∀ k : ℕ,
      (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
        k ∈ Finset.Icc lo hi)
    (F : (PUnit → ℝ) → ℝ) :
    ((∑' x : ↑({x : PUnit → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c} ∩
        (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit → ℝ))), F x) /
        (n : ℝ)) =
      (1 / (n : ℝ)) *
        (Finset.Icc lo hi).sum
          (fun k : ℕ => F (fun _ : PUnit => (k : ℝ) / (n : ℝ))) := by
  rw [prob_14_1_tsum_interval_scaled_punitIntLattice_eq_sum_Icc_of_bounds
    (a := a) (c := c) (n := n) (lo := lo) (hi := hi) ha hn hIcc F]
  ring

def prob_14_1_punitInterval (a c : ℝ) : Set (PUnit.{1} → ℝ) :=
  {x : PUnit.{1} → ℝ | a ≤ x PUnit.unit ∧ x PUnit.unit ≤ c}

theorem prob_14_1_punitInterval_ordConnected (a c : ℝ) :
    (prob_14_1_punitInterval a c).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro x hx y hy _hxy z hz
  exact ⟨le_trans hx.1 (hz.1 PUnit.unit),
    le_trans (hz.2 PUnit.unit) hy.2⟩

theorem prob_14_1_punitInterval_frontier_null (a c : ℝ) :
    volume (frontier (prob_14_1_punitInterval a c)) = 0 :=
  (prob_14_1_punitInterval_ordConnected a c).null_frontier

theorem prob_14_1_punitInterval_measurable (a c : ℝ) :
    MeasurableSet (prob_14_1_punitInterval a c) := by
  have hleft : MeasurableSet {x : PUnit.{1} → ℝ | a ≤ x PUnit.unit} :=
    measurableSet_Ici.preimage (continuous_apply PUnit.unit).measurable
  have hright : MeasurableSet {x : PUnit.{1} → ℝ | x PUnit.unit ≤ c} :=
    measurableSet_Iic.preimage (continuous_apply PUnit.unit).measurable
  simpa [prob_14_1_punitInterval, Set.setOf_and] using hleft.inter hright

theorem prob_14_1_punitInterval_isBounded (a c : ℝ) :
    Bornology.IsBounded (prob_14_1_punitInterval a c) := by
  refine
    (Metric.isBounded_Icc (fun _ : PUnit.{1} => a) (fun _ : PUnit.{1} => c)).subset ?_
  intro x hx
  change (fun _ : PUnit.{1} => a) ≤ x ∧ x ≤ (fun _ : PUnit.{1} => c)
  exact
    ⟨fun j => by cases j; exact hx.1,
      fun j => by cases j; exact hx.2⟩

theorem prob_14_1_unit_partition_tendsto_integral
    {a c : ℝ} {F : (PUnit.{1} → ℝ) → ℝ}
    (hF : Continuous F) :
    Tendsto
      (fun n : ℕ =>
        (∑' x : ↑(prob_14_1_punitInterval a c ∩
          (n : ℝ)⁻¹ • (prob_14_1_punitIntLattice : Set (PUnit.{1} → ℝ))), F x) /
          n ^ Fintype.card PUnit.{1})
      atTop
      (𝓝 (∫ x in prob_14_1_punitInterval a c, F x)) := by
  exact tendsto_tsum_div_pow_atTop_integral
    (s := prob_14_1_punitInterval a c)
    (ι := PUnit.{1})
    (F := F)
    hF (prob_14_1_punitInterval_isBounded a c)
    (prob_14_1_punitInterval_measurable a c)
    (prob_14_1_punitInterval_frontier_null a c)

theorem prob_14_1_unit_partition_Icc_sum_tendsto_integral_of_bounds
    {a c : ℝ} {F : (PUnit.{1} → ℝ) → ℝ}
    (hF : Continuous F) (ha : 0 ≤ a)
    (lo hi : ℕ → ℕ)
    (hIcc :
      Filter.Eventually (fun n : ℕ =>
        0 < n ∧
          ∀ k : ℕ,
            (a ≤ (k : ℝ) / (n : ℝ) ∧
              (k : ℝ) / (n : ℝ) ≤ c) ↔
              k ∈ Finset.Icc (lo n) (hi n)) atTop) :
    Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) *
          (Finset.Icc (lo n) (hi n)).sum
            (fun k : ℕ => F (fun _ : PUnit.{1} => (k : ℝ) / (n : ℝ))))
      atTop
      (𝓝 (∫ x in prob_14_1_punitInterval a c, F x)) := by
  have hbase :=
    prob_14_1_unit_partition_tendsto_integral
      (a := a) (c := c) (F := F) hF
  refine hbase.congr' ?_
  filter_upwards [hIcc] with n hn
  have hcard : Fintype.card PUnit.{1} = 1 := by simp
  rw [hcard, pow_one]
  simpa [prob_14_1_punitInterval] using
    prob_14_1_tsum_interval_scaled_punitIntLattice_div_nat_eq_inv_mul_sum_Icc_of_bounds
      (a := a) (c := c) (n := n) (lo := lo n) (hi := hi n)
      ha hn.1 hn.2 F

theorem prob_14_1_sum_scaled_error_bound
    (s : Finset ℕ) {n : ℕ} (hn : (n : ℝ) ≠ 0)
    (p f : ℕ → ℝ) {eps : ℝ}
    (hbound : ∀ k ∈ s, |(n : ℝ) * p k - f k| ≤ eps) :
    |s.sum p - (1 / (n : ℝ)) * s.sum f| ≤
      (s.card : ℝ) / (n : ℝ) * eps := by
  have hrewrite :
      s.sum p - (1 / (n : ℝ)) * s.sum f =
        (1 / (n : ℝ)) *
          s.sum (fun k : ℕ => (n : ℝ) * p k - f k) := by
    calc
      s.sum p - (1 / (n : ℝ)) * s.sum f
          = (1 / (n : ℝ)) *
              ((n : ℝ) * s.sum p - s.sum f) := by
            field_simp [hn]
      _ = (1 / (n : ℝ)) *
          s.sum (fun k : ℕ => (n : ℝ) * p k - f k) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hrewrite]
  have hnonneg_n : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn_pos : 0 < (n : ℝ) := lt_of_le_of_ne hnonneg_n (Ne.symm hn)
  calc
    |(1 / (n : ℝ)) * s.sum (fun k : ℕ => (n : ℝ) * p k - f k)|
        = (1 / (n : ℝ)) *
            |s.sum (fun k : ℕ => (n : ℝ) * p k - f k)| := by
          rw [abs_mul]
          have hinv_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
          rw [abs_of_nonneg hinv_nonneg]
    _ ≤ (1 / (n : ℝ)) *
          s.sum (fun k : ℕ => |(n : ℝ) * p k - f k|) := by
          gcongr
          exact Finset.abs_sum_le_sum_abs
            (fun k => (n : ℝ) * p k - f k) s
    _ ≤ (1 / (n : ℝ)) * s.sum (fun _k : ℕ => eps) := by
          gcongr with k hk
          exact hbound k hk
    _ = (s.card : ℝ) / (n : ℝ) * eps := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

theorem prob_14_1_sum_scaled_error_tendsto_zero
    (s : ℕ → Finset ℕ) (p f : ℕ → ℕ → ℝ) {M : ℝ}
    (hM : 0 < M)
    (hCard : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≠ 0 ∧ ((s n).card : ℝ) / (n : ℝ) ≤ M)
    (hUniform : ∀ eps > 0, ∀ᶠ n : ℕ in atTop,
      ∀ k ∈ s n, |(n : ℝ) * p n k - f n k| ≤ eps) :
    Tendsto
      (fun n : ℕ =>
        |(s n).sum (fun k : ℕ => p n k) -
          (1 / (n : ℝ)) * (s n).sum (fun k : ℕ => f n k)|)
      atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro eps heps
  let δ : ℝ := eps / (2 * M)
  have hδ_pos : 0 < δ := by positivity
  rcases eventually_atTop.1 (hCard.and (hUniform δ hδ_pos)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨hcard, huniform⟩
  have hsum_bound :=
    prob_14_1_sum_scaled_error_bound
      (s n) hcard.1 (fun k : ℕ => p n k) (fun k : ℕ => f n k) huniform
  have hcard_nonneg : 0 ≤ ((s n).card : ℝ) / (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hn_pos : 0 < (n : ℝ) := lt_of_le_of_ne hn_nonneg (Ne.symm hcard.1)
    positivity
  have hdelta_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hboundM :
      ((s n).card : ℝ) / (n : ℝ) * δ ≤ M * δ :=
    mul_le_mul_of_nonneg_right hcard.2 hdelta_nonneg
  have hmain :
      |(s n).sum (fun k : ℕ => p n k) -
          (1 / (n : ℝ)) * (s n).sum (fun k : ℕ => f n k)| < eps := by
    have hleM : M * δ < eps := by
      dsimp [δ]
      field_simp [ne_of_gt hM]
      nlinarith [heps, hM]
    exact lt_of_le_of_lt (le_trans hsum_bound hboundM) hleM
  have habs_nonneg :
      0 ≤
        |(s n).sum (fun k : ℕ => p n k) -
          (1 / (n : ℝ)) * (s n).sum (fun k : ℕ => f n k)| :=
    abs_nonneg _
  simpa [Real.dist_eq, abs_of_nonneg habs_nonneg] using hmain

lemma prob_14_1_scaledGridSet_measurable (i : ℕ) :
    MeasurableSet (prob_14_1_scaledGridSet i) := by
  rw [prob_14_1_scaledGridSet]
  have hset :
      {y : ℝ | ∃ k ∈ Finset.range (i + 1), y = (k : ℝ) / (i : ℝ)} =
        ⋃ k : ℕ, ⋃ _ : k ∈ Finset.range (i + 1),
          ({y : ℝ | y = (k : ℝ) / (i : ℝ)} : Set ℝ) := by
    ext y
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ =>
      (by
        simpa only [Set.setOf_eq_eq_singleton] using
          measurableSet_singleton ((k : ℝ) / (i : ℝ)))

lemma prob_14_1_scaled_grid_point_injective {i a b : ℕ}
    (hi : 1 ≤ i)
    (h : (a : ℝ) / (i : ℝ) = (b : ℝ) / (i : ℝ)) :
    a = b := by
  have hi_pos : 0 < i := Nat.succ_le_iff.mp hi
  have hi_ne : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi_pos)
  have hmul := congrArg (fun y : ℝ => y * (i : ℝ)) h
  have hreal : (a : ℝ) = (b : ℝ) := by
    simpa [hi_ne] using hmul
  exact_mod_cast hreal

lemma prob_14_1_scaled_grid_iic_eq_biUnion
    {i : ℕ} (_hi : 1 ≤ i) (x : ℝ) :
    Set.Iic x ∩ prob_14_1_scaledGridSet i =
      ⋃ k ∈ (Finset.range (i + 1)).filter
          (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ x),
        ({y : ℝ | y = (k : ℝ) / (i : ℝ)} : Set ℝ) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyx, k, hk, hy_eq⟩
    have hkx : (k : ℝ) / (i : ℝ) ≤ x := by
      simpa [hy_eq] using hyx
    refine mem_iUnion.mpr ?_
    refine ⟨k, mem_iUnion.mpr ?_⟩
    exact ⟨Finset.mem_filter.mpr ⟨hk, hkx⟩, hy_eq⟩
  · intro hy
    rcases mem_iUnion.mp hy with ⟨k, hkrest⟩
    rcases mem_iUnion.mp hkrest with ⟨hkfilter, hyk⟩
    have hk := (Finset.mem_filter.mp hkfilter).1
    have hkx := (Finset.mem_filter.mp hkfilter).2
    have hyx : y ≤ x := by
      rw [hyk]
      exact hkx
    exact ⟨hyx, k, hk, hyk⟩

lemma prob_14_1_scaled_grid_singletons_pairwiseDisjoint
    {i : ℕ} (hi : 1 ≤ i) (x : ℝ) :
    ((↑((Finset.range (i + 1)).filter
          (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ x))) : Set ℕ).PairwiseDisjoint
      (fun k : ℕ => ({y : ℝ | y = (k : ℝ) / (i : ℝ)} : Set ℝ)) := by
  intro a _ b _ hab
  change Disjoint
    ({y : ℝ | y = (a : ℝ) / (i : ℝ)})
    ({y : ℝ | y = (b : ℝ) / (i : ℝ)})
  rw [Set.disjoint_left]
  intro y hya hyb
  exact hab (prob_14_1_scaled_grid_point_injective hi (hya.symm.trans hyb))

theorem prob_14_1_scaled_support_of_count_support
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ) {i : ℕ}
    (hi : 1 ≤ i)
    (hSupport :
      (whiteCountLaws i : Measure ℝ) (prob_14_1_countGridSet i)ᶜ = 0) :
    (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
        (prob_14_1_scaledGridSet i)ᶜ = 0 := by
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_ne : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi_pos_nat)
  have hMeas : MeasurableSet ((prob_14_1_scaledGridSet i)ᶜ) :=
    (prob_14_1_scaledGridSet_measurable i).compl
  have hpre :
      (fun x : ℝ => x / (i : ℝ)) ⁻¹' (prob_14_1_scaledGridSet i)ᶜ =
        (prob_14_1_countGridSet i)ᶜ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
      intro hx_count
      rcases hx_count with ⟨k, hk, hxk⟩
      exact hx ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), by simp [hxk]⟩
    · intro hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
      intro hx_scaled
      rcases hx_scaled with ⟨k, hk, hxk⟩
      apply hx
      refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), ?_⟩
      have hmul := congrArg (fun y : ℝ => y * (i : ℝ)) hxk
      simpa [hi_ne] using hmul
  rw [prob_14_1_whiteFractionLaws, prob_14_1_scaledCountLaw,
    ProbabilityMeasure.map]
  change
    (Measure.map (fun x : ℝ => x / (i : ℝ)) (whiteCountLaws i : Measure ℝ))
        (prob_14_1_scaledGridSet i)ᶜ = 0
  rw [Measure.map_apply_of_aemeasurable
    (by fun_prop :
      AEMeasurable (fun x : ℝ => x / (i : ℝ))
        (whiteCountLaws i : Measure ℝ)) hMeas]
  rw [hpre]
  exact hSupport

theorem prob_14_1_scaled_iic_diff_support_of_count_support
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ) {i : ℕ}
    (hi : 1 ≤ i)
    (hSupport :
      (whiteCountLaws i : Measure ℝ) (prob_14_1_countGridSet i)ᶜ = 0)
    (x : ℝ) :
    (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
        (Set.Iic x \ prob_14_1_scaledGridSet i) = 0 := by
  have hscaled :=
    prob_14_1_scaled_support_of_count_support whiteCountLaws hi hSupport
  exact MeasureTheory.measure_mono_null
    (by
      intro y hy
      exact hy.2)
    hscaled

theorem prob_14_1_cdf_measure_eq_grid_sum_of_support
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ)
    {w b x : ℝ} {i : ℕ}
    (hi : 1 ≤ i)
    (hCountMass :
      ∀ k : ℕ, k ≤ i →
        (whiteCountLaws i : Measure ℝ) {y : ℝ | y = (k : ℝ)} =
          ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k))
    (hSupport :
      (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
        (Set.Iic x \ prob_14_1_scaledGridSet i) = 0) :
    (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ) (Set.Iic x) =
      (Finset.range (i + 1)).sum fun k : ℕ =>
        if (k : ℝ) / (i : ℝ) ≤ x then
          ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k)
        else
          0 := by
  let μ : Measure ℝ := prob_14_1_whiteFractionLaws whiteCountLaws i
  have hgridMeas : MeasurableSet (prob_14_1_scaledGridSet i) :=
    prob_14_1_scaledGridSet_measurable i
  have hsplit :
      μ (Set.Iic x ∩ prob_14_1_scaledGridSet i) = μ (Set.Iic x) := by
    have h := MeasureTheory.measure_inter_add_diff (μ := μ) (Set.Iic x) hgridMeas
    have h0 : μ (Set.Iic x \ prob_14_1_scaledGridSet i) = 0 := hSupport
    rw [h0, add_zero] at h
    exact h
  have hfinite :
      μ (Set.Iic x ∩ prob_14_1_scaledGridSet i) =
        ((Finset.range (i + 1)).filter
            (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ x)
          ).sum (fun k : ℕ => μ {y : ℝ | y = (k : ℝ) / (i : ℝ)}) := by
    rw [prob_14_1_scaled_grid_iic_eq_biUnion hi x]
    exact MeasureTheory.measure_biUnion_finset
      (prob_14_1_scaled_grid_singletons_pairwiseDisjoint hi x)
      (by
        intro k hk
        simpa only [Set.setOf_eq_eq_singleton] using
          measurableSet_singleton ((k : ℝ) / (i : ℝ)))
  calc
    μ (Set.Iic x)
        = μ (Set.Iic x ∩ prob_14_1_scaledGridSet i) := hsplit.symm
    _ = ((Finset.range (i + 1)).filter
          (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ x)
        ).sum (fun k : ℕ => μ {y : ℝ | y = (k : ℝ) / (i : ℝ)}) := hfinite
    _ = ((Finset.range (i + 1)).filter
          (fun k : ℕ => (k : ℝ) / (i : ℝ) ≤ x)
        ).sum (fun k : ℕ =>
          ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k)) := by
          apply Finset.sum_congr rfl
          intro k hkfilter
          have hk_range : k ∈ Finset.range (i + 1) :=
            (Finset.mem_filter.mp hkfilter).1
          have hk_le : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
          change
            (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
                {y : ℝ | y = (k : ℝ) / (i : ℝ)} =
              ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k)
          rw [prob_14_1_whiteFractionLaws,
            prob_14_1_scaled_count_law_atom (whiteCountLaws i) hi]
          exact hCountMass k hk_le
    _ = (Finset.range (i + 1)).sum fun k : ℕ =>
        if (k : ℝ) / (i : ℝ) ≤ x then
          ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k)
        else
          0 := by
          rw [Finset.sum_filter]

theorem prob_14_1_cdf_eq_grid_sum_of_support
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ)
    {w b x : ℝ} {i : ℕ}
    (hi : 1 ≤ i)
    (hCountMass :
      ∀ k : ℕ, k ≤ i →
        (whiteCountLaws i : Measure ℝ) {y : ℝ | y = (k : ℝ)} =
          ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k))
    (hMass_nonneg :
      ∀ k : ℕ, k ≤ i → 0 ≤ prob_14_1_polyaWhiteMassFormula w b i k)
    (hSupport :
      (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
        (Set.Iic x \ prob_14_1_scaledGridSet i) = 0) :
    ((prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
        (Set.Iic x)).toReal =
      prob_14_1_scaledPolyaGridCdf w b i x := by
  have hmeasure :=
    prob_14_1_cdf_measure_eq_grid_sum_of_support
      whiteCountLaws hi hCountMass hSupport
  rw [hmeasure, prob_14_1_scaledPolyaGridCdf]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hkx : (k : ℝ) / (i : ℝ) ≤ x
    · have hk_le : k ≤ i :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [hkx, ENNReal.toReal_ofReal (hMass_nonneg k hk_le)]
    · simp [hkx]
  · intro k hk
    by_cases hkx : (k : ℝ) / (i : ℝ) ≤ x
    · simp [hkx]
    · simp [hkx]

theorem prob_14_1_cdfConvergence_of_finiteMass_gridCdfLimit
    {whiteCountLaws : ℕ → ProbabilityMeasure ℝ}
    {w b : ℝ} {beta : prob_14_1_BetaLawData w b}
    (hCountMass :
      ∀ᶠ i in atTop, 1 ≤ i ∧
        ∀ k : ℕ, k ≤ i →
          (whiteCountLaws i : Measure ℝ) {y : ℝ | y = (k : ℝ)} =
            ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula w b i k))
    (hMass_nonneg :
      ∀ᶠ i in atTop,
        ∀ k : ℕ, k ≤ i → 0 ≤ prob_14_1_polyaWhiteMassFormula w b i k)
    (hSupport :
      ∀ᶠ i in atTop,
        ∀ x : ℝ,
          (prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
            (Set.Iic x \ prob_14_1_scaledGridSet i) = 0)
    (hGrid : prob_14_1_gridCdfLimit w b beta) :
    prob_14_1_cdfConvergence
      (prob_14_1_whiteFractionLaws whiteCountLaws) beta.law := by
  have hCdfEq :
      ∀ᶠ i in atTop, ∀ x : ℝ,
        ((prob_14_1_whiteFractionLaws whiteCountLaws i : Measure ℝ)
            (Set.Iic x)).toReal =
          prob_14_1_scaledPolyaGridCdf w b i x := by
    filter_upwards [hCountMass, hMass_nonneg, hSupport] with
      i hCount_i hNonneg_i hSupport_i x
    exact prob_14_1_cdf_eq_grid_sum_of_support
      whiteCountLaws hCount_i.1 hCount_i.2 hNonneg_i (hSupport_i x)
  intro x hx
  exact (hGrid x hx).congr'
    (hCdfEq.mono fun _ hi => (hi x).symm)

theorem prob_14_1_cdfConvergence_of_setup_finiteMass_countSupport_gridCdfLimit
    (S : prob_14_1_PolyaUrnBetaSetup)
    (hMass : prob_14_1_finitePolyaWhiteCountMass S)
    (hCountSupport :
      ∀ᶠ i in atTop,
        1 ≤ i ∧
          (S.whiteCountLaws i : Measure ℝ) (prob_14_1_countGridSet i)ᶜ = 0)
    (hGrid : prob_14_1_gridCdfLimit S.w S.b S.beta) :
    prob_14_1_cdfConvergence
      (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law := by
  have hCountMass :
      ∀ᶠ i in atTop, 1 ≤ i ∧
        ∀ k : ℕ, k ≤ i →
          (S.whiteCountLaws i : Measure ℝ) {y : ℝ | y = (k : ℝ)} =
            ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k) := by
    exact eventually_atTop.2 ⟨1, fun i hi => ⟨hi, fun k hk => hMass i k hi hk⟩⟩
  have hMass_nonneg :
      ∀ᶠ i in atTop,
        ∀ k : ℕ, k ≤ i → 0 ≤ prob_14_1_polyaWhiteMassFormula S.w S.b i k :=
    Filter.Eventually.of_forall fun _ k hk =>
      prob_14_1_polyaWhiteMassFormula_nonneg S.w_pos S.b_pos hk
  have hScaledSupport :
      ∀ᶠ i in atTop,
        ∀ x : ℝ,
          (prob_14_1_whiteFractionLaws S.whiteCountLaws i : Measure ℝ)
            (Set.Iic x \ prob_14_1_scaledGridSet i) = 0 := by
    filter_upwards [hCountSupport] with i hi x
    exact prob_14_1_scaled_iic_diff_support_of_count_support
      S.whiteCountLaws hi.1 hi.2 x
  exact prob_14_1_cdfConvergence_of_finiteMass_gridCdfLimit
    hCountMass hMass_nonneg hScaledSupport hGrid

theorem prob_14_1_stirling_beta_cdf_convergence_from_gridCdfLimit
    (S : prob_14_1_PolyaUrnBetaSetup)
    (hGrid : prob_14_1_gridCdfLimit S.w S.b S.beta) :
    prob_14_1_stirlingBetaCdfConvergence S := by
  simpa [prob_14_1_stirlingBetaCdfConvergence] using
    prob_14_1_cdfConvergence_of_setup_finiteMass_countSupport_gridCdfLimit
      S (prob_14_1_finite_polya_white_count_mass S)
      (prob_14_1_white_count_grid_support S) hGrid
