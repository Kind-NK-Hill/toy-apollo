/-
TASK ID: prob_14_1_tail_endpoint_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_1_tail_riemann_support

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

theorem prob_14_1_leftTailMass_add_Icc_grid_sum_le_one
    {w b a c eps : ℝ} {n : ℕ}
    (hw : 0 < w) (hb : 0 < b) (hn : 0 < n)
    (heps_lt_a : eps < a) (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    prob_14_1_leftTailMass w b n eps +
      (Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (c * (n : ℝ)))).sum
        (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) ≤ 1 := by
  let tail : Finset ℕ := (Finset.range (n + 1)).filter
    (fun k : ℕ => (k : ℝ) / (n : ℝ) ≤ eps)
  let core : Finset ℕ :=
    Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (c * (n : ℝ)))
  have hc_nonneg : 0 ≤ c := le_trans ha.le hac
  have hcore_subset_range : core ⊆ Finset.range (n + 1) := by
    intro k hk
    have hk_hi : k ≤ Nat.floor (c * (n : ℝ)) :=
      (Finset.mem_Icc.mp hk).2
    have hhi_le_n : Nat.floor (c * (n : ℝ)) ≤ n :=
      prob_14_1_floor_mul_le_self_nat_of_lt_one
        (c := c) (n := n) hc_nonneg hc
    exact Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (le_trans hk_hi hhi_le_n))
  have htail_subset_range : tail ⊆ Finset.range (n + 1) :=
    Finset.filter_subset _ _
  have hdisjoint : Disjoint tail core := by
    rw [Finset.disjoint_left]
    intro k hk_tail hk_core
    have hk_tail_ratio : (k : ℝ) / (n : ℝ) ≤ eps :=
      (Finset.mem_filter.mp hk_tail).2
    have hk_core_bounds :=
      (prob_14_1_grid_bounds_Icc_ceil_floor
        (a := a) (c := c) (n := n) hn ha.le hc_nonneg k).mpr hk_core
    linarith
  have htail_sum :
      prob_14_1_leftTailMass w b n eps =
        tail.sum (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) := by
    dsimp [prob_14_1_leftTailMass, tail]
    rw [← Finset.sum_filter]
  rw [htail_sum]
  change
    tail.sum (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) +
      core.sum (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) ≤ 1
  rw [← Finset.sum_union hdisjoint]
  have hunion_subset : tail ∪ core ⊆ Finset.range (n + 1) :=
    Finset.union_subset htail_subset_range hcore_subset_range
  have hle_total :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (s := tail ∪ core) (t := Finset.range (n + 1))
      (f := fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k)
      hunion_subset
      (by
        intro k hk_range _hk_not
        have hk_le : k ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
        exact prob_14_1_polyaWhiteMassFormula_nonneg hw hb hk_le)
  exact le_trans hle_total
    (le_of_eq (prob_14_1_polyaWhiteMassFormula_sum_range_eq_one hw hb n))

theorem prob_14_1_leftTailMass_uniform_small
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    ∀ η > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      prob_14_1_leftTailMass w b n δ < η := by
  intro η hη
  let beta := prob_14_1_standardBetaLawData hw hb
  have hη2 : 0 < η / 2 := by positivity
  rcases prob_14_1_beta_law_exists_Icc_core_gt (w := w) (b := b)
      (η := η / 2) beta hη2 with
    ⟨a, c, ha, hac, hc, hcoreMass⟩
  let δ : ℝ := a / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_lt_a : δ < a := by
    dsimp [δ]
    linarith
  refine ⟨δ, hδ_pos, ?_⟩
  have hconv :=
    prob_14_1_Icc_grid_sum_tendsto_beta_law_Icc
      (w := w) (b := b) (a := a) (c := c) hw hb ha hac hc
  have hcoreEventually :
      ∀ᶠ n : ℕ in atTop,
        1 - η <
          (Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (c * (n : ℝ)))).sum
            (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) := by
    exact hconv (isOpen_Ioi.mem_nhds (by
      linarith :
        1 - η < (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
          (Set.Icc a c)).toReal))
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn => Nat.succ_le_iff.mp hn⟩
  filter_upwards [hnpos, hcoreEventually] with n hn hcore
  have hle :=
    prob_14_1_leftTailMass_add_Icc_grid_sum_le_one
      (w := w) (b := b) (a := a) (c := c) (eps := δ)
      (n := n) hw hb hn hδ_lt_a ha hac hc
  linarith

theorem prob_14_1_beta_law_Iic_lt_of_Icc_core_gt
    {w b a c δ η : ℝ} (beta : prob_14_1_BetaLawData w b)
    (hδa : δ < a)
    (hcore : 1 - η < ((beta.law : Measure ℝ) (Set.Icc a c)).toReal) :
    ((beta.law : Measure ℝ) (Set.Iic δ)).toReal < η := by
  let μ : Measure ℝ := beta.law
  have hsubset : Set.Iic δ ⊆ (Set.Icc a c)ᶜ := by
    intro y hy hcoremem
    exact not_le_of_gt hδa (le_trans hcoremem.1 hy)
  have hle_compl_en : μ (Set.Iic δ) ≤ μ (Set.Icc a c)ᶜ :=
    measure_mono hsubset
  have hcore_meas : MeasurableSet (Set.Icc a c) := measurableSet_Icc
  have hcore_ne_top : μ (Set.Icc a c) ≠ ⊤ := measure_ne_top μ (Set.Icc a c)
  have hcompl_eq : μ (Set.Icc a c)ᶜ = μ Set.univ - μ (Set.Icc a c) :=
    measure_compl hcore_meas hcore_ne_top
  have huniv : μ Set.univ = 1 := by
    simp [μ]
  have hcompl_toReal :
      (μ (Set.Icc a c)ᶜ).toReal = 1 - (μ (Set.Icc a c)).toReal := by
    rw [hcompl_eq, huniv]
    exact ENNReal.toReal_sub_of_le
      (by
        simpa using
          (measure_mono (Set.subset_univ (Set.Icc a c) :
            Set.Icc a c ⊆ Set.univ) : μ (Set.Icc a c) ≤ μ Set.univ))
      (by simp)
  have hcompl_ne_top : μ (Set.Icc a c)ᶜ ≠ ⊤ := by
    rw [hcompl_eq, huniv]
    simp
  have hleft_le_real :
      (μ (Set.Iic δ)).toReal ≤ (μ (Set.Icc a c)ᶜ).toReal :=
    ENNReal.toReal_mono hcompl_ne_top hle_compl_en
  rw [hcompl_toReal] at hleft_le_real
  linarith

theorem prob_14_1_leftTailMass_and_beta_Iic_uniform_small
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    ∀ η > 0, ∃ δ > 0,
      (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
        (Set.Iic δ)).toReal < η ∧
      ∀ᶠ n in atTop, prob_14_1_leftTailMass w b n δ < η := by
  intro η hη
  let beta := prob_14_1_standardBetaLawData hw hb
  have hη2 : 0 < η / 2 := by positivity
  rcases prob_14_1_beta_law_exists_Icc_core_gt (w := w) (b := b)
      (η := η / 2) beta hη2 with
    ⟨a, c, ha, hac, hc, hcoreMass⟩
  let δ : ℝ := a / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_lt_a : δ < a := by
    dsimp [δ]
    linarith
  refine ⟨δ, hδ_pos, ?_, ?_⟩
  · have hleft :=
      prob_14_1_beta_law_Iic_lt_of_Icc_core_gt
        (w := w) (b := b) (a := a) (c := c) (δ := δ)
        (η := η / 2) beta hδ_lt_a hcoreMass
    simpa [beta] using (show
      (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
          (Set.Iic δ)).toReal < η from by
        linarith)
  · have hconv :=
      prob_14_1_Icc_grid_sum_tendsto_beta_law_Icc
        (w := w) (b := b) (a := a) (c := c) hw hb ha hac hc
    have hcoreEventually :
        ∀ᶠ n : ℕ in atTop,
          1 - η <
            (Finset.Icc (Nat.ceil (a * (n : ℝ)))
                (Nat.floor (c * (n : ℝ)))).sum
              (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) := by
      exact hconv (isOpen_Ioi.mem_nhds (by
        linarith :
          1 - η < (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
            (Set.Icc a c)).toReal))
    have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      eventually_atTop.2 ⟨1, fun n hn => Nat.succ_le_iff.mp hn⟩
    filter_upwards [hnpos, hcoreEventually] with n hn hcore
    have hle :=
      prob_14_1_leftTailMass_add_Icc_grid_sum_le_one
        (w := w) (b := b) (a := a) (c := c) (eps := δ)
        (n := n) hw hb hn hδ_lt_a ha hac hc
    linarith

theorem prob_14_1_Icc_grid_sum_le_scaledPolyaGridCdf
    {w b a x : ℝ} {n : ℕ} (hw : 0 < w) (hb : 0 < b)
    (hn : 0 < n) (ha : 0 ≤ a) (hax : a ≤ x) (hx : x < 1) :
    (Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (x * (n : ℝ)))).sum
        (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) ≤
      prob_14_1_scaledPolyaGridCdf w b n x := by
  let core : Finset ℕ :=
    Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (x * (n : ℝ)))
  let range : Finset ℕ := Finset.range (n + 1)
  let mass : ℕ → ℝ := fun k => prob_14_1_polyaWhiteMassFormula w b n k
  let cdfBranch : ℕ → ℝ := fun k =>
    if (k : ℝ) / (n : ℝ) ≤ x then mass k else 0
  have hx_nonneg : 0 ≤ x := le_trans ha hax
  have hhi_le_n : Nat.floor (x * (n : ℝ)) ≤ n :=
    prob_14_1_floor_mul_le_self_nat_of_lt_one
      (c := x) (n := n) hx_nonneg hx
  have hcore_subset_range : core ⊆ range := by
    intro k hk
    have hk_hi : k ≤ Nat.floor (x * (n : ℝ)) :=
      (Finset.mem_Icc.mp hk).2
    exact Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (le_trans hk_hi hhi_le_n))
  have hcore_eq :
      core.sum mass = core.sum cdfBranch := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk_bounds :=
      (prob_14_1_grid_bounds_Icc_ceil_floor
        (a := a) (c := x) (n := n) hn ha hx_nonneg k).mpr hk
    have hkx : (k : ℝ) / (n : ℝ) ≤ x := hk_bounds.2
    simp [cdfBranch, mass, hkx]
  have hle :
      core.sum cdfBranch ≤ range.sum cdfBranch :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (s := core) (t := range) (f := cdfBranch)
      hcore_subset_range
      (by
        intro k hk_range _hk_not
        by_cases hkx : (k : ℝ) / (n : ℝ) ≤ x
        · have hk_le_n : k ≤ n :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
          simp [cdfBranch, mass, hkx,
            (prob_14_1_polyaWhiteMassFormula_nonneg hw hb hk_le_n)]
        · simp [cdfBranch, hkx])
  rw [hcore_eq]
  simpa [prob_14_1_scaledPolyaGridCdf, range, cdfBranch, mass] using hle

theorem prob_14_1_scaledPolyaGridCdf_le_leftTailMass_add_Icc_grid_sum
    {w b a x : ℝ} {n : ℕ} (hw : 0 < w) (hb : 0 < b)
    (hn : 0 < n) (ha : 0 ≤ a) (hax : a ≤ x) (hx : x < 1) :
    prob_14_1_scaledPolyaGridCdf w b n x ≤
      prob_14_1_leftTailMass w b n a +
        (Finset.Icc (Nat.ceil (a * (n : ℝ)))
            (Nat.floor (x * (n : ℝ)))).sum
          (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) := by
  let range : Finset ℕ := Finset.range (n + 1)
  let lo : ℕ := Nat.ceil (a * (n : ℝ))
  let hi : ℕ := Nat.floor (x * (n : ℝ))
  let mass : ℕ → ℝ := fun k => prob_14_1_polyaWhiteMassFormula w b n k
  let cdfBranch : ℕ → ℝ := fun k =>
    if (k : ℝ) / (n : ℝ) ≤ x then mass k else 0
  let leftBranch : ℕ → ℝ := fun k =>
    if (k : ℝ) / (n : ℝ) ≤ a then mass k else 0
  let middleBranch : ℕ → ℝ := fun k =>
    if lo ≤ k ∧ k ≤ hi then mass k else 0
  have hx_nonneg : 0 ≤ x := le_trans ha hax
  have hhi_le_n : hi ≤ n :=
    prob_14_1_floor_mul_le_self_nat_of_lt_one
      (c := x) (n := n) hx_nonneg hx
  have hpoint :
      ∀ k ∈ range, cdfBranch k ≤ leftBranch k + middleBranch k := by
    intro k hk_range
    have hk_le_n : k ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
    have hmass_nonneg : 0 ≤ mass k :=
      prob_14_1_polyaWhiteMassFormula_nonneg hw hb hk_le_n
    have hidx_iff :
        (lo ≤ k ∧ k ≤ hi) ↔
          a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ x := by
      constructor
      · intro hidx
        have hmem : k ∈ Finset.Icc lo hi := Finset.mem_Icc.mpr hidx
        exact
          (prob_14_1_grid_bounds_Icc_ceil_floor
            (a := a) (c := x) (n := n) hn ha hx_nonneg k).mpr hmem
      · intro hbds
        have hmem :
            k ∈ Finset.Icc lo hi :=
          (prob_14_1_grid_bounds_Icc_ceil_floor
            (a := a) (c := x) (n := n) hn ha hx_nonneg k).mp hbds
        exact Finset.mem_Icc.mp hmem
    by_cases hkx : (k : ℝ) / (n : ℝ) ≤ x
    · by_cases hka : (k : ℝ) / (n : ℝ) ≤ a
      · by_cases hidx : lo ≤ k ∧ k ≤ hi
        · simp [cdfBranch, leftBranch, middleBranch, hkx, hka, hidx,
            hmass_nonneg]
        · simp [cdfBranch, leftBranch, middleBranch, hkx, hka, hidx]
      · have hak : a ≤ (k : ℝ) / (n : ℝ) := le_of_lt (not_le.mp hka)
        have hidx : lo ≤ k ∧ k ≤ hi := hidx_iff.mpr ⟨hak, hkx⟩
        simp [cdfBranch, leftBranch, middleBranch, hkx, hka, hidx]
    · have hleft_nonneg : 0 ≤ leftBranch k := by
        by_cases hka : (k : ℝ) / (n : ℝ) ≤ a
        · simp [leftBranch, hka, hmass_nonneg]
        · simp [leftBranch, hka]
      have hmid_nonneg : 0 ≤ middleBranch k := by
        by_cases hidx : lo ≤ k ∧ k ≤ hi
        · simp [middleBranch, hidx, hmass_nonneg]
        · simp [middleBranch, hidx]
      have hsum_nonneg : 0 ≤ leftBranch k + middleBranch k :=
        add_nonneg hleft_nonneg hmid_nonneg
      simpa [cdfBranch, hkx] using hsum_nonneg
  have hsum_le :
      range.sum cdfBranch ≤
        range.sum (fun k : ℕ => leftBranch k + middleBranch k) :=
    Finset.sum_le_sum hpoint
  have hmid_eq :
      range.sum middleBranch =
        (Finset.Icc lo hi).sum mass := by
    simpa [range, middleBranch, lo, hi, mass] using
      prob_14_1_sum_range_succ_ite_index_bounds_eq_sum_Icc
        (g := mass) (n := n) (lo := lo) (hi := hi) hhi_le_n
  calc
    prob_14_1_scaledPolyaGridCdf w b n x = range.sum cdfBranch := by
      simp [prob_14_1_scaledPolyaGridCdf, range, cdfBranch, mass]
    _ ≤ range.sum (fun k : ℕ => leftBranch k + middleBranch k) := hsum_le
    _ = range.sum leftBranch + range.sum middleBranch := by
      rw [Finset.sum_add_distrib]
    _ = prob_14_1_leftTailMass w b n a + (Finset.Icc lo hi).sum mass := by
      simp [prob_14_1_leftTailMass, range, leftBranch, hmid_eq, mass]
    _ = prob_14_1_leftTailMass w b n a +
        (Finset.Icc (Nat.ceil (a * (n : ℝ)))
            (Nat.floor (x * (n : ℝ)))).sum
          (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k) := by
      rfl

theorem prob_14_1_beta_law_Icc_toReal_le_Iic
    {w b a x : ℝ} (beta : prob_14_1_BetaLawData w b) :
    ((beta.law : Measure ℝ) (Set.Icc a x)).toReal ≤
      ((beta.law : Measure ℝ) (Set.Iic x)).toReal := by
  let μ : Measure ℝ := beta.law
  have hsubset : Set.Icc a x ⊆ Set.Iic x := by
    intro y hy
    exact hy.2
  exact ENNReal.toReal_mono (measure_ne_top μ (Set.Iic x))
    (measure_mono hsubset)

theorem prob_14_1_beta_law_Iic_toReal_le_Iic_add_Icc
    {w b a x : ℝ} (beta : prob_14_1_BetaLawData w b) (_hax : a ≤ x) :
    ((beta.law : Measure ℝ) (Set.Iic x)).toReal ≤
      ((beta.law : Measure ℝ) (Set.Iic a)).toReal +
        ((beta.law : Measure ℝ) (Set.Icc a x)).toReal := by
  let μ : Measure ℝ := beta.law
  have hsubset : Set.Iic x ⊆ Set.Iic a ∪ Set.Icc a x := by
    intro y hy
    by_cases hya : y ≤ a
    · exact Or.inl hya
    · exact Or.inr ⟨le_of_lt (not_le.mp hya), hy⟩
  have hle_en :
      μ (Set.Iic x) ≤ μ (Set.Iic a) + μ (Set.Icc a x) :=
    le_trans (measure_mono hsubset)
      (measure_union_le (Set.Iic a) (Set.Icc a x))
  have hsum_ne_top :
      μ (Set.Iic a) + μ (Set.Icc a x) ≠ ⊤ := by
    exact ENNReal.add_ne_top.2
      ⟨measure_ne_top μ (Set.Iic a), measure_ne_top μ (Set.Icc a x)⟩
  have hle_real :
      (μ (Set.Iic x)).toReal ≤
        (μ (Set.Iic a) + μ (Set.Icc a x)).toReal :=
    ENNReal.toReal_mono hsum_ne_top hle_en
  rwa [ENNReal.toReal_add
    (measure_ne_top μ (Set.Iic a)) (measure_ne_top μ (Set.Icc a x))] at hle_real

theorem prob_14_1_interior_gridCdf_tendsto
    {w b x : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hx0 : 0 < x) (hx1 : x < 1)
    (_hxcont :
      ContinuousAt
        (fun y : ℝ =>
          (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
            (Set.Iic y)).toReal) x) :
    Tendsto
      (fun n : ℕ => prob_14_1_scaledPolyaGridCdf w b n x)
      atTop
      (𝓝 ((((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
        (Set.Iic x)).toReal)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let η : ℝ := ε / 3
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases prob_14_1_leftTailMass_and_beta_Iic_uniform_small
      (w := w) (b := b) hw hb η hη with
    ⟨δ, hδ_pos, hbetaδ_small, hleftδ_small⟩
  let a : ℝ := min δ (x / 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min hδ_pos (by positivity)
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have ha_le_delta : a ≤ δ := by
    dsimp [a]
    exact min_le_left _ _
  have ha_le_x_half : a ≤ x / 2 := by
    dsimp [a]
    exact min_le_right _ _
  have ha_le_x : a ≤ x := by
    linarith
  have ha_lt_one : a < 1 := lt_of_le_of_lt ha_le_x hx1
  let beta := prob_14_1_standardBetaLawData hw hb
  let middle : ℕ → ℝ := fun n : ℕ =>
    (Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (x * (n : ℝ)))).sum
      (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k)
  let betaLeft : ℝ := ((beta.law : Measure ℝ) (Set.Iic a)).toReal
  let betaMiddle : ℝ := ((beta.law : Measure ℝ) (Set.Icc a x)).toReal
  let betaCdf : ℝ := ((beta.law : Measure ℝ) (Set.Iic x)).toReal
  have hbetaLeft_small : betaLeft < η := by
    let μ : Measure ℝ := beta.law
    have hsubset : Set.Iic a ⊆ Set.Iic δ := by
      intro y hy
      exact le_trans hy ha_le_delta
    have hle_en : μ (Set.Iic a) ≤ μ (Set.Iic δ) := measure_mono hsubset
    have hle_real :
        (μ (Set.Iic a)).toReal ≤ (μ (Set.Iic δ)).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ (Set.Iic δ)) hle_en
    have hδ_small :
        (μ (Set.Iic δ)).toReal < η := by
      simpa [μ, beta, prob_14_1_standardBetaLawData] using hbetaδ_small
    dsimp [betaLeft, μ] at hle_real
    exact lt_of_le_of_lt hle_real hδ_small
  have hlefta_small :
      ∀ᶠ n : ℕ in atTop, prob_14_1_leftTailMass w b n a < η := by
    filter_upwards [hleftδ_small] with n hnδ
    have hmono :=
      prob_14_1_leftTailMass_mono_eps
        (w := w) (b := b) hw hb n ha_le_delta
    exact lt_of_le_of_lt hmono hnδ
  have hmiddle_tendsto :
      Tendsto middle atTop (𝓝 betaMiddle) := by
    simpa [middle, betaMiddle, beta, prob_14_1_standardBetaLawData] using
      prob_14_1_Icc_grid_sum_tendsto_beta_law_Icc
        (w := w) (b := b) (a := a) (c := x) hw hb
        ha_pos ha_le_x hx1
  have hmiddle_small :
      ∀ᶠ n : ℕ in atTop, |middle n - betaMiddle| < η := by
    rcases Metric.tendsto_atTop.mp hmiddle_tendsto η hη with ⟨N, hN⟩
    exact eventually_atTop.2
      ⟨N, fun n hn => by
        have hdist := hN n hn
        simpa [Real.dist_eq] using hdist⟩
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn => Nat.succ_le_iff.mp hn⟩
  have htwoη_lt : η + η < ε := by
    dsimp [η]
    linarith
  rcases eventually_atTop.1 (hnpos.and (hlefta_small.and hmiddle_small)) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  rcases hN n hnN with ⟨hn, hleft_small, hmid_small⟩
  let cdf : ℝ := prob_14_1_scaledPolyaGridCdf w b n x
  let left : ℝ := prob_14_1_leftTailMass w b n a
  let mid : ℝ := middle n
  have hmid_le_cdf : mid ≤ cdf := by
    simpa [mid, cdf, middle] using
      prob_14_1_Icc_grid_sum_le_scaledPolyaGridCdf
        (w := w) (b := b) (a := a) (x := x) (n := n)
        hw hb hn ha_nonneg ha_le_x hx1
  have hcdf_le : cdf ≤ left + mid := by
    simpa [cdf, left, mid, middle] using
      prob_14_1_scaledPolyaGridCdf_le_leftTailMass_add_Icc_grid_sum
        (w := w) (b := b) (a := a) (x := x) (n := n)
        hw hb hn ha_nonneg ha_le_x hx1
  have hbeta_mid_le_cdf : betaMiddle ≤ betaCdf := by
    simpa [betaMiddle, betaCdf, beta] using
      prob_14_1_beta_law_Icc_toReal_le_Iic
        (w := w) (b := b) (a := a) (x := x) beta
  have hbeta_cdf_le : betaCdf ≤ betaLeft + betaMiddle := by
    simpa [betaCdf, betaLeft, betaMiddle, beta] using
      prob_14_1_beta_law_Iic_toReal_le_Iic_add_Icc
        (w := w) (b := b) (a := a) (x := x) beta ha_le_x
  have hmid_abs_left : betaMiddle - mid ≤ |mid - betaMiddle| := by
    have h := neg_le_abs (mid - betaMiddle)
    linarith
  have hmid_abs_right : mid - betaMiddle ≤ |mid - betaMiddle| :=
    le_abs_self _
  have hlower : betaCdf - cdf < ε := by
    have hle : betaCdf - cdf ≤ betaLeft + (betaMiddle - mid) := by
      linarith
    have hsum : betaLeft + (betaMiddle - mid) < ε := by
      have hmid : betaMiddle - mid < η :=
        lt_of_le_of_lt hmid_abs_left hmid_small
      linarith
    exact lt_of_le_of_lt hle hsum
  have hupper : cdf - betaCdf < ε := by
    have hle : cdf - betaCdf ≤ left + (mid - betaMiddle) := by
      linarith
    have hsum : left + (mid - betaMiddle) < ε := by
      have hmid : mid - betaMiddle < η :=
        lt_of_le_of_lt hmid_abs_right hmid_small
      linarith
    exact lt_of_le_of_lt hle hsum
  have habs : |cdf - betaCdf| < ε :=
    abs_lt.mpr ⟨by linarith, hupper⟩
  simpa [Real.dist_eq, cdf, betaCdf, beta, prob_14_1_standardBetaLawData] using habs

theorem prob_14_1_rightTailMass_uniform_small
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    ∀ η > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      prob_14_1_rightTailMass w b n δ < η := by
  intro η hη
  rcases prob_14_1_leftTailMass_uniform_small hb hw η hη with
    ⟨δ, hδ_pos, hδ_small⟩
  refine ⟨δ, hδ_pos, ?_⟩
  have hnpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    eventually_atTop.2 ⟨1, fun n hn => hn⟩
  filter_upwards [hnpos, hδ_small] with n hn hsmall
  rw [prob_14_1_rightTailMass_reflect_leftTail (w := w) (b := b)
    (eps := δ) (i := n) hn]
  exact hsmall
