import Mathlib
import ToyApollo.Output.def_14_2

/-
TASK ID: prob_14_6
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.6.} Given an arbitrary sequence of random variables (Xn)\infty

n=1. Show that we can

find positive constants cn,f o rn \geq1, such that cnXn converges weakly to 0.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

/-- Convergence in probability to zero for a scaled sequence `c_n X_n`.

This is the standard route for Problem 14.6: choose `c_n > 0` so that the
scaled variables are small with high probability, then use convergence in
probability to obtain weak convergence to the zero random variable. -/
def prob_14_6_scaledConvergesInProbabilityToZero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ => μ.real {ω : Ω | ε ≤ |c n * Xseq n ω|})
      atTop (𝓝 (0 : ℝ))

/-- A concrete construction package for the positive constants promised in
Problem 14.6.  The key mathematical obligation is the quantile/tail choice of
`c_n`, producing convergence in probability to zero; the final field records
the standard implication from convergence in probability to weak convergence. -/
structure prob_14_6_PositiveScalingSupport
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) where
  scales : ℕ → ℝ
  scales_positive : ∀ n : ℕ, 0 < scales n
  scaled_measurable :
    ∀ n : ℕ, Measurable (fun ω : Ω => scales n * Xseq n ω)
  scaled_converges_in_probability_to_zero :
    prob_14_6_scaledConvergesInProbabilityToZero μ Xseq scales
  convergence_in_probability_to_weak_zero :
    prob_14_6_scaledConvergesInProbabilityToZero μ Xseq scales →
      def_14_2 μ
        (fun n : ℕ => fun ω : Ω => scales n * Xseq n ω)
        (fun _ω : Ω => (0 : ℝ))
        scaled_measurable
        measurable_const

/-- For a single real-valued random variable, the tails
`{|X| ≥ M}` have probability tending to zero as `M → ∞`. -/
private theorem prob_14_6_tail_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) :
    Tendsto (fun M : ℕ => μ {ω : Ω | (M : ℝ) ≤ |X ω|}) atTop (𝓝 0) := by
  let s : ℕ → Set Ω := fun M => {ω : Ω | (M : ℝ) ≤ |X ω|}
  have hs_meas : ∀ M, NullMeasurableSet (s M) μ := by
    intro M
    exact (hX.abs measurableSet_Ici).nullMeasurableSet
  have hs_anti : Antitone s := by
    intro M N hMN ω hω
    change (M : ℝ) ≤ |X ω|
    change (N : ℝ) ≤ |X ω| at hω
    exact le_trans (by exact_mod_cast hMN) hω
  have hs_inter : (⋂ M : ℕ, s M) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    let M : ℕ := Nat.floor |X ω| + 1
    have hM : ω ∈ s M := (Set.mem_iInter.mp hω) M
    have hbad : (M : ℝ) ≤ |X ω| := by
      simpa [s, M] using hM
    have hlt : |X ω| < (M : ℝ) := by
      simpa [M, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one |X ω|
    exact (not_le_of_gt hlt) hbad
  have hfin : ∃ M, μ (s M) ≠ ∞ := ⟨0, measure_ne_top μ (s 0)⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := s) hs_meas hs_anti hfin
  rw [hs_inter, measure_empty] at h
  exact h

/-- Choose a finite tail cutoff whose tail probability is at most `1 / (n + 1)`. -/
private theorem prob_14_6_exists_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (n : ℕ) :
    ∃ M : ℕ, μ.real {ω : Ω | (M : ℝ) ≤ |X ω|} ≤ 1 / ((n : ℝ) + 1) := by
  let f : ℕ → ℝ≥0∞ := fun M => μ {ω : Ω | (M : ℝ) ≤ |X ω|}
  have htail : Tendsto f atTop (𝓝 0) := by
    simp [f, prob_14_6_tail_tendsto_zero μ hX]
  have htoreal : Tendsto (fun M : ℕ => (f M).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (f := f) (fun M => by
      simp [f, measure_ne_top μ {ω : Ω | (M : ℝ) ≤ |X ω|}])).mpr htail
  have hreal : Tendsto (fun M : ℕ => μ.real {ω : Ω | (M : ℝ) ≤ |X ω|})
      atTop (𝓝 0) := by
    simpa [f, Measure.real_def] using htoreal
  have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
  have hev : ∀ᶠ M : ℕ in atTop,
      μ.real {ω : Ω | (M : ℝ) ≤ |X ω|} < 1 / ((n : ℝ) + 1) :=
    hreal.eventually (Iio_mem_nhds hpos)
  rcases eventually_atTop.1 hev with ⟨M, hM⟩
  exact ⟨M, (hM M le_rfl).le⟩

/-- A tail cutoff for the `n`-th random variable. -/
private noncomputable def prob_14_6_tailBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (n : ℕ) : ℕ :=
  Classical.choose (prob_14_6_exists_tail_bound μ (hXseq n) n)

private theorem prob_14_6_tailBound_spec
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (n : ℕ) :
    μ.real {ω : Ω | ((prob_14_6_tailBound μ Xseq hXseq n : ℕ) : ℝ) ≤ |Xseq n ω|} ≤
      1 / ((n : ℝ) + 1) :=
  Classical.choose_spec (prob_14_6_exists_tail_bound μ (hXseq n) n)

/-- The concrete positive constants used in Problem 14.6. -/
private noncomputable def prob_14_6_scale
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) *
    (((prob_14_6_tailBound μ Xseq hXseq n : ℕ) : ℝ) + 1))⁻¹

private theorem prob_14_6_scale_pos
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) :
    ∀ n : ℕ, 0 < prob_14_6_scale μ Xseq hXseq n := by
  intro n
  unfold prob_14_6_scale
  positivity

/-- The chosen scalings force convergence to zero in measure. -/
private theorem prob_14_6_scaled_tendstoInMeasure_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) :
    TendstoInMeasure μ
      (fun n ω => prob_14_6_scale μ Xseq hXseq n * Xseq n ω)
      atTop
      (fun _ω => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  refine squeeze_zero' (Eventually.of_forall fun _ => MeasureTheory.measureReal_nonneg) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ ε * ((n + 1 : ℕ) : ℝ) := by
    have hsucc : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      refine Filter.tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
      exact_mod_cast Nat.le_succ n
    have htop : Tendsto (fun n : ℕ => ε * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos hε).mpr hsucc
    exact htop.eventually (Ici_mem_atTop 1)
  filter_upwards [hev] with n hn
  let M : ℕ := prob_14_6_tailBound μ Xseq hXseq n
  let A : ℝ := ((n + 1 : ℕ) : ℝ) * ((M : ℝ) + 1)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hcpos : 0 < prob_14_6_scale μ Xseq hXseq n :=
    prob_14_6_scale_pos μ Xseq hXseq n
  have hsubset :
      {ω : Ω | ε ≤ ‖prob_14_6_scale μ Xseq hXseq n * Xseq n ω - (0 : ℝ)‖} ⊆
        {ω : Ω | (M : ℝ) ≤ |Xseq n ω|} := by
    intro ω hω
    have hω' : ε ≤ A⁻¹ * |Xseq n ω| := by
      change ε ≤ ‖prob_14_6_scale μ Xseq hXseq n * Xseq n ω - (0 : ℝ)‖ at hω
      rw [sub_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hcpos] at hω
      simpa [prob_14_6_scale, M, A, mul_comm, mul_left_comm, mul_assoc] using hω
    have hmul := mul_le_mul_of_nonneg_left hω' hApos.le
    have hxA : ε * A ≤ |Xseq n ω| := by
      have hleft_le : ε * A ≤ A * (A⁻¹ * |Xseq n ω|) := by
        simpa [mul_comm] using hmul
      calc
        ε * A ≤ A * (A⁻¹ * |Xseq n ω|) := hleft_le
        _ = |Xseq n ω| := by
          rw [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul]
    have hMA : (M : ℝ) ≤ ε * A := by
      dsimp [A]
      have hMnonneg : 0 ≤ (M : ℝ) + 1 := by positivity
      have hscaleM : (M : ℝ) + 1 ≤ (ε * ((n + 1 : ℕ) : ℝ)) * ((M : ℝ) + 1) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hn hMnonneg
      nlinarith
    exact le_trans hMA hxA
  calc
    μ.real {ω : Ω | ε ≤ ‖prob_14_6_scale μ Xseq hXseq n * Xseq n ω - (0 : ℝ)‖}
        ≤ μ.real {ω : Ω | (M : ℝ) ≤ |Xseq n ω|} :=
          MeasureTheory.measureReal_mono hsubset
    _ ≤ 1 / ((n : ℝ) + 1) := by
          simpa [M] using prob_14_6_tailBound_spec μ Xseq hXseq n

/-- Mathlib's convergence-in-distribution bridge gives the weak convergence
formulation used by Definition 14.2. -/
private theorem prob_14_6_scaled_weak_convergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) :
    def_14_2 μ
      (fun n : ℕ => fun ω : Ω => prob_14_6_scale μ Xseq hXseq n * Xseq n ω)
      (fun _ω : Ω => (0 : ℝ))
      (fun n => measurable_const.mul (hXseq n))
      measurable_const :=
by
  have hdist :
      TendstoInDistribution
        (fun n : ℕ => fun ω : Ω => prob_14_6_scale μ Xseq hXseq n * Xseq n ω)
        atTop
        (fun _ω : Ω => (0 : ℝ))
        (fun _ : ℕ => μ)
        μ :=
    (prob_14_6_scaled_tendstoInMeasure_zero μ Xseq hXseq).tendstoInDistribution
      (fun n => (measurable_const.mul (hXseq n)).aemeasurable)
  unfold def_14_2 def_14_1_randomVariableWeakConvergence
  have ht := hdist.tendsto
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at ht
  intro h
  exact ht h

/-- Problem 14.6: for an arbitrary sequence of real random variables, there
are positive constants `c_n` such that `c_n X_n` converges weakly to zero. -/
theorem prob_14_6
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (hXseq : ∀ n : ℕ, Measurable (Xseq n)) :
    ∃ c : ℕ → ℝ,
      (∀ n : ℕ, 0 < c n) ∧
        ∃ hScaled : ∀ n : ℕ,
          Measurable (fun ω : Ω => c n * Xseq n ω),
          def_14_2 μ
            (fun n : ℕ => fun ω : Ω => c n * Xseq n ω)
            (fun _ω : Ω => (0 : ℝ))
            hScaled
            measurable_const := by
  refine ⟨prob_14_6_scale μ Xseq hXseq, prob_14_6_scale_pos μ Xseq hXseq, ?_⟩
  exact ⟨fun n => measurable_const.mul (hXseq n),
    prob_14_6_scaled_weak_convergence μ Xseq hXseq⟩
