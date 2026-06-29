import Mathlib
import ToyApollo.Output.thm_10_8_quantile_space

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

/-- CDF data in the form needed for the Skorokhod quantile construction:
a bundled monotone right-continuous Stieltjes function with probability-limit
normalization at both infinities. -/
structure thm_10_8_ProbabilityCdf where
  stieltjes : StieltjesFunction ℝ
  tendsto_atBot : Tendsto (stieltjes : ℝ → ℝ) atBot (nhds 0)
  tendsto_atTop : Tendsto (stieltjes : ℝ → ℝ) atTop (nhds 1)

/-- The probability CDF associated to a real-line probability measure. -/
def thm_10_8_probabilityCdfOfMeasure
    (mu : Measure ℝ) : thm_10_8_ProbabilityCdf where
  stieltjes := cdf mu
  tendsto_atBot := tendsto_cdf_atBot mu
  tendsto_atTop := tendsto_cdf_atTop mu

theorem thm_10_8_probabilityCdf_monotone
    (F : thm_10_8_ProbabilityCdf) :
    Monotone (F.stieltjes : ℝ → ℝ) :=
  F.stieltjes.mono

theorem thm_10_8_probabilityCdf_right_continuous
    (F : thm_10_8_ProbabilityCdf) (x : ℝ) :
    ContinuousWithinAt (F.stieltjes : ℝ → ℝ) (Ici x) x :=
  F.stieltjes.right_continuous' x

/-- The lower generalized inverse used in the textbook definition
`sup {y : F y < omega}`. -/
def thm_10_8_lowerQuantile
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) : ℝ :=
  sSup {y : ℝ | F.stieltjes y < omega}

/-- The upper generalized inverse used for the comparison argument:
`inf {y : omega < F y}`. -/
def thm_10_8_upperQuantile
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) : ℝ :=
  sInf {y : ℝ | omega < F.stieltjes y}

def thm_10_8_lowerQuantileSet
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) : Set ℝ :=
  {y : ℝ | F.stieltjes y < omega}

def thm_10_8_upperQuantileSet
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) : Set ℝ :=
  {y : ℝ | omega < F.stieltjes y}

@[simp]
theorem thm_10_8_mem_lowerQuantileSet
    (F : thm_10_8_ProbabilityCdf) (omega y : ℝ) :
    y ∈ thm_10_8_lowerQuantileSet F omega ↔ F.stieltjes y < omega :=
  Iff.rfl

@[simp]
theorem thm_10_8_mem_upperQuantileSet
    (F : thm_10_8_ProbabilityCdf) (omega y : ℝ) :
    y ∈ thm_10_8_upperQuantileSet F omega ↔ omega < F.stieltjes y :=
  Iff.rfl

theorem thm_10_8_lowerQuantile_eq_sSup
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) :
    thm_10_8_lowerQuantile F omega =
      sSup (thm_10_8_lowerQuantileSet F omega) := by
  rfl

theorem thm_10_8_upperQuantile_eq_sInf
    (F : thm_10_8_ProbabilityCdf) (omega : ℝ) :
    thm_10_8_upperQuantile F omega =
      sInf (thm_10_8_upperQuantileSet F omega) := by
  rfl

/-- The lower-quantile random variable on the unit-interval witness space. -/
def thm_10_8_lowerQuantileVariable
    (F : thm_10_8_ProbabilityCdf) : ℝ → ℝ :=
  fun omega => if 0 < omega ∧ omega < 1 then thm_10_8_lowerQuantile F omega else 0

/-- The upper-quantile random variable used for the limsup comparison. -/
def thm_10_8_upperQuantileVariable
    (F : thm_10_8_ProbabilityCdf) : ℝ → ℝ :=
  fun omega => thm_10_8_upperQuantile F omega

/-- Sequence of lower-quantile variables for a sequence of CDFs. -/
def thm_10_8_lowerQuantileSeq
    (Fs : ℕ → thm_10_8_ProbabilityCdf) : ℕ → ℝ → ℝ :=
  fun n omega => thm_10_8_lowerQuantile (Fs n) omega

/-- Sequence of upper-quantile variables for a sequence of CDFs. -/
def thm_10_8_upperQuantileSeq
    (Fs : ℕ → thm_10_8_ProbabilityCdf) : ℕ → ℝ → ℝ :=
  fun n omega => thm_10_8_upperQuantile (Fs n) omega

theorem thm_10_8_lowerQuantileSet_bddAbove_of_lt_one
    (F : thm_10_8_ProbabilityCdf) {omega : ℝ} (homega : omega < 1) :
    BddAbove {y : ℝ | F.stieltjes y < omega} := by
  have hmid_gt : omega < (omega + 1) / 2 := by linarith
  have hmid_lt : (omega + 1) / 2 < 1 := by linarith
  have h_ev : ∀ᶠ x in atTop, (omega + 1) / 2 < F.stieltjes x :=
    F.tendsto_atTop (Ioi_mem_nhds hmid_lt)
  rw [eventually_atTop] at h_ev
  rcases h_ev with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro y hy
  by_contra hle
  have hlt : M < y := not_le.mp hle
  have hFy : (omega + 1) / 2 < F.stieltjes y := hM y hlt.le
  have hyomega : F.stieltjes y < omega := hy
  linarith

theorem thm_10_8_lowerQuantileSet_nonempty_of_pos
    (F : thm_10_8_ProbabilityCdf) {omega : ℝ} (homega : 0 < omega) :
    ({y : ℝ | F.stieltjes y < omega} : Set ℝ).Nonempty := by
  have h_ev : ∀ᶠ x in atBot, F.stieltjes x < omega :=
    F.tendsto_atBot (Iio_mem_nhds homega)
  rw [eventually_atBot] at h_ev
  rcases h_ev with ⟨M, hM⟩
  exact ⟨M, hM M le_rfl⟩

theorem thm_10_8_exists_right_of_stieltjes_lt
    (F : thm_10_8_ProbabilityCdf) {y omega : ℝ}
    (hy : F.stieltjes y < omega) :
    ∃ z : ℝ, y < z ∧ F.stieltjes z < omega := by
  have h_ev : ∀ᶠ z in 𝓝[Ici y] y, F.stieltjes z < omega :=
    (F.stieltjes.right_continuous' y).eventually (Iio_mem_nhds hy)
  change {z : ℝ | F.stieltjes z < omega} ∈ 𝓝[Ici y] y at h_ev
  rw [Metric.mem_nhdsWithin_iff] at h_ev
  rcases h_ev with ⟨ε, hεpos, hε⟩
  refine ⟨y + ε / 2, ?_, ?_⟩
  · linarith
  · exact hε ⟨by
        rw [Metric.mem_ball, Real.dist_eq]
        have hnonneg : 0 ≤ ε / 2 := by linarith
        have hεhalf : |y + ε / 2 - y| = ε / 2 := by
          rw [add_sub_cancel_left, abs_of_nonneg hnonneg]
        rw [hεhalf]
        linarith, by
        change y ≤ y + ε / 2
        linarith⟩

theorem thm_10_8_lowerQuantile_le_iff
    (F : thm_10_8_ProbabilityCdf) {omega y : ℝ}
    (homega0 : 0 < omega) (homega1 : omega < 1) :
    thm_10_8_lowerQuantile F omega ≤ y ↔ omega ≤ F.stieltjes y := by
  constructor
  · intro hQ
    by_contra hnot
    have hylt : F.stieltjes y < omega := lt_of_not_ge hnot
    rcases thm_10_8_exists_right_of_stieltjes_lt F hylt with ⟨z, hyz, hzlt⟩
    have hbdd := thm_10_8_lowerQuantileSet_bddAbove_of_lt_one F homega1
    have hz_le_Q : z ≤ thm_10_8_lowerQuantile F omega := by
      simpa [thm_10_8_lowerQuantile] using
        (le_csSup hbdd (show z ∈ {u : ℝ | F.stieltjes u < omega} from hzlt))
    linarith
  · intro homega_le
    have hne := thm_10_8_lowerQuantileSet_nonempty_of_pos F homega0
    have hupper : ∀ z ∈ ({u : ℝ | F.stieltjes u < omega} : Set ℝ), z ≤ y := by
      intro z hz
      by_contra hzy
      have hyz : y < z := not_le.mp hzy
      have hFle : F.stieltjes y ≤ F.stieltjes z :=
        (thm_10_8_probabilityCdf_monotone F) hyz.le
      have hzomega : F.stieltjes z < omega := hz
      linarith
    simpa [thm_10_8_lowerQuantile] using
      (csSup_le hne hupper)

theorem thm_10_8_lowerQuantileVariable_measurable
    (F : thm_10_8_ProbabilityCdf) :
    Measurable (thm_10_8_lowerQuantileVariable F) := by
  refine measurable_of_Iic ?_
  intro y
  by_cases hy0 : 0 ≤ y
  · have hpre :
        (thm_10_8_lowerQuantileVariable F) ⁻¹' Iic y =
          Set.inter (Ioo (0 : ℝ) 1) (Iic (F.stieltjes y)) ∪ (Ioo (0 : ℝ) 1)ᶜ := by
      ext omega
      by_cases hunit : 0 < omega ∧ omega < 1
      · have hiff := thm_10_8_lowerQuantile_le_iff F hunit.1 hunit.2 (y := y)
        simp [thm_10_8_lowerQuantileVariable, hunit, hiff]
        constructor
        · intro hle
          exact ⟨hunit, hle⟩
        · intro hmem
          exact hmem.2
      · simp [thm_10_8_lowerQuantileVariable, hunit, hy0]
    rw [hpre]
    exact (measurableSet_Ioo.inter measurableSet_Iic).union measurableSet_Ioo.compl
  · have hpre :
        (thm_10_8_lowerQuantileVariable F) ⁻¹' Iic y =
          Set.inter (Ioo (0 : ℝ) 1) (Iic (F.stieltjes y)) := by
      ext omega
      by_cases hunit : 0 < omega ∧ omega < 1
      · have hiff := thm_10_8_lowerQuantile_le_iff F hunit.1 hunit.2 (y := y)
        simp [thm_10_8_lowerQuantileVariable, hunit, hiff]
        constructor
        · intro hle
          exact ⟨hunit, hle⟩
        · intro hmem
          exact hmem.2
      · simp [thm_10_8_lowerQuantileVariable, hunit, hy0]
        intro hmem
        exact hunit hmem.1
    rw [hpre]
    exact measurableSet_Ioo.inter measurableSet_Iic
