import Mathlib
import ToyApollo.Output.prob_14_12_limit_truncation_tail_support
import ToyApollo.Output.def_14_3
import ToyApollo.Output.thm_14_5

/-
SUPPORT FOR: prob_14_12
TYPE: Parent-owned support
SOURCE PLAN: chapter14-problems
TASK CONTENT:
This file contains the parent-owned mean-convergence support for Problem
14.12(b). It assembles the source-faithful truncation route: sequence
truncation tails, bounded truncation convergence, limit-tail transfer, and the
final three-term triangle estimate.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

/-- Convergence in mean in the nonnegative extended-real `L1` form used by the
Problem 14.12(b) truncation route. -/
def prob_14_12_convergesInMean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal |Xseq n ω - X ω| ∂μ)
    atTop (𝓝 (0 : ℝ≥0∞))

/-- Truncated sequence at level `M`, using the reviewed truncation interface. -/
def prob_14_12_truncatedSequence
    {Ω : Type*} (Xseq : ℕ → Ω → ℝ) (M : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => prob_14_12_truncate M (Xseq n ω)

/-- Truncated limit at level `M`, using the reviewed truncation interface. -/
def prob_14_12_truncatedLimit
    {Ω : Type*} (X : Ω → ℝ) (M : ℝ) : Ω → ℝ :=
  fun ω => prob_14_12_truncate M (X ω)

/-- Symmetric truncation is `1`-Lipschitz on `ℝ`. -/
theorem prob_14_12_truncate_lipschitz (M x y : ℝ) :
    |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤ |x - y| := by
  have hmax : |max x (-M) - max y (-M)| ≤ |x - y| := by
    simpa using abs_max_sub_max_le_abs x y (-M)
  have hmin :
      |min (max x (-M)) M - min (max y (-M)) M| ≤
        |max x (-M) - max y (-M)| := by
    have h :=
      abs_min_sub_min_le_max (max x (-M)) M (max y (-M)) M
    simpa using h
  exact hmin.trans hmax

/-- A truncation value lies in the truncation interval. -/
theorem prob_14_12_abs_truncate_le
    {M x : ℝ} (hM : 0 ≤ M) : |prob_14_12_truncate M x| ≤ M := by
  have hle : prob_14_12_truncate M x ≤ M := min_le_right _ _
  have hge : -M ≤ prob_14_12_truncate M x := by
    have hleft : -M ≤ max x (-M) := le_max_right x (-M)
    have hright : -M ≤ M := by linarith
    exact le_min hleft hright
  exact abs_le.mpr ⟨hge, hle⟩

/-- The difference between two level-`M` truncations is bounded by `2M`. -/
theorem prob_14_12_abs_truncate_sub_le_two_mul
    {M x y : ℝ} (hM : 0 ≤ M) :
    |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤ 2 * M := by
  have hx := prob_14_12_abs_truncate_le (M := M) (x := x) hM
  have hy := prob_14_12_abs_truncate_le (M := M) (x := y) hM
  have hxle : prob_14_12_truncate M x ≤ M := (abs_le.mp hx).2
  have hxge : -M ≤ prob_14_12_truncate M x := (abs_le.mp hx).1
  have hyle : prob_14_12_truncate M y ≤ M := (abs_le.mp hy).2
  have hyge : -M ≤ prob_14_12_truncate M y := (abs_le.mp hy).1
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise small/bad-set bound for bounded truncations. -/
theorem prob_14_12_truncated_deviation_pointwise_bound
    {M δ x y : ℝ} (hM : 0 ≤ M) :
    ENNReal.ofReal |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤
      ENNReal.ofReal δ +
        Set.indicator {_p : Unit | δ < |x - y|}
          (fun _ : Unit => ENNReal.ofReal (2 * M)) () := by
  by_cases hbad : δ < |x - y|
  · have hbound :=
      prob_14_12_abs_truncate_sub_le_two_mul (M := M) (x := x) (y := y) hM
    have hle : ENNReal.ofReal |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤
        ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal hbound
    have : ENNReal.ofReal |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤
        ENNReal.ofReal δ + ENNReal.ofReal (2 * M) :=
      hle.trans (le_add_left (le_refl (ENNReal.ofReal (2 * M))))
    simpa [Set.indicator, hbad] using this
  · have hnot : |x - y| ≤ δ := le_of_not_gt hbad
    have hlip := prob_14_12_truncate_lipschitz M x y
    have hle_real :
        |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤ δ :=
      hlip.trans hnot
    have hle : ENNReal.ofReal |prob_14_12_truncate M x - prob_14_12_truncate M y| ≤
        ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hle_real
    exact hle.trans (le_add_right le_rfl)

/-- Integral form of the elementary estimate
`|T_M X_n - T_M X| <= δ + 2M 1{|X_n-X|>δ}`. -/
theorem prob_14_12_bounded_truncation_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    {M δ : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
        |prob_14_12_truncate M (Xseq n ω) -
          prob_14_12_truncate M (X ω)| ∂μ) ≤
      ENNReal.ofReal δ * μ Set.univ +
        ENNReal.ofReal (2 * M) *
          μ {ω : Ω | δ < |Xseq n ω - X ω|} := by
  let bad : Set Ω := {ω : Ω | δ < |Xseq n ω - X ω|}
  let c : ℝ≥0∞ := ENNReal.ofReal (2 * M)
  have hpoint :
      (fun ω : Ω =>
        ENNReal.ofReal
          |prob_14_12_truncate M (Xseq n ω) -
            prob_14_12_truncate M (X ω)|) ≤
        (fun ω : Ω => ENNReal.ofReal δ + bad.indicator (fun _ => c) ω) := by
    intro ω
    have h :=
      prob_14_12_truncated_deviation_pointwise_bound
        (M := M) (δ := δ) (x := Xseq n ω) (y := X ω) hM
    by_cases hbad : ω ∈ bad
    · have hunit : () ∈ ({p : Unit | δ < |Xseq n ω - X ω|}) := hbad
      simpa [bad, c, Set.indicator, hbad, hunit] using h
    · have hunit : () ∉ ({p : Unit | δ < |Xseq n ω - X ω|}) := hbad
      simpa [bad, c, Set.indicator, hbad, hunit] using h
  calc
    (∫⁻ ω, ENNReal.ofReal
        |prob_14_12_truncate M (Xseq n ω) -
          prob_14_12_truncate M (X ω)| ∂μ)
        ≤ ∫⁻ ω, ENNReal.ofReal δ + bad.indicator (fun _ => c) ω ∂μ :=
          lintegral_mono hpoint
    _ = ENNReal.ofReal δ * μ Set.univ +
        ∫⁻ ω, bad.indicator (fun _ => c) ω ∂μ := by
          rw [lintegral_add_left measurable_const]
          simp
    _ ≤ ENNReal.ofReal δ * μ Set.univ + c * μ bad := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left (lintegral_indicator_const_le (μ := μ) bad c)
              (ENNReal.ofReal δ * μ Set.univ))

/-- Bounded truncations converge in mean from convergence in probability on a
finite measure space. -/
theorem prob_14_12_bounded_truncations_convergeInMean_obligation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    prob_14_12_convergesInProbability μ Xseq X →
      ∀ M : ℝ, 0 ≤ M →
        prob_14_12_convergesInMean μ
          (prob_14_12_truncatedSequence Xseq M)
          (prob_14_12_truncatedLimit X M) := by
  intro hprob M hM
  rw [prob_14_12_convergesInMean]
  refine ENNReal.tendsto_nhds_zero.mpr ?_
  intro ε hε
  by_cases hεtop : ε = ∞
  · filter_upwards [] with n
    rw [hεtop]
    exact le_top
  · have hεhalf_pos : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hεhalf_ne_zero : ε / 2 ≠ 0 := ne_of_gt hεhalf_pos
    have hμ_ne_top : μ Set.univ ≠ ∞ := by finiteness
    rcases ENNReal.exists_nnreal_pos_mul_lt hμ_ne_top hεhalf_ne_zero with
      ⟨δnn, hδnn_pos, hδnn_mul⟩
    let δ : ℝ := (δnn : ℝ)
    have hδ_pos : 0 < δ := by exact_mod_cast hδnn_pos
    have hterm :
        Tendsto
          (fun n : ℕ =>
            ENNReal.ofReal (2 * M) *
              μ {ω : Ω | δ < |Xseq n ω - X ω|})
          atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [mul_zero] using
        (ENNReal.Tendsto.const_mul
          (a := ENNReal.ofReal (2 * M)) (hprob δ hδ_pos)
          (Or.inr ENNReal.ofReal_ne_top))
    have heventually :=
      (ENNReal.tendsto_nhds_zero.mp hterm) (ε / 2) hεhalf_pos
    filter_upwards [heventually] with n hn
    have hmain :=
      prob_14_12_bounded_truncation_lintegral_bound
        μ Xseq X (M := M) (δ := δ) hM n
    have hmain' :
        (∫⁻ ω, ENNReal.ofReal
            |prob_14_12_truncatedSequence Xseq M n ω -
              prob_14_12_truncatedLimit X M ω| ∂μ) ≤
          (δnn : ℝ≥0∞) * μ Set.univ +
            ENNReal.ofReal (2 * M) *
              μ {ω : Ω | δ < |Xseq n ω - X ω|} := by
      simpa [prob_14_12_truncatedSequence, prob_14_12_truncatedLimit,
        δ, ENNReal.ofReal_coe_nnreal] using hmain
    have hsum_le :
        (δnn : ℝ≥0∞) * μ Set.univ +
            ENNReal.ofReal (2 * M) *
              μ {ω : Ω | δ < |Xseq n ω - X ω|} ≤
          (δnn : ℝ≥0∞) * μ Set.univ + ε / 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hn ((δnn : ℝ≥0∞) * μ Set.univ))
    have hεhalf_ne_top : ε / 2 ≠ ∞ := by finiteness
    have hsum_lt :
        (δnn : ℝ≥0∞) * μ Set.univ + ε / 2 < ε := by
      calc
        (δnn : ℝ≥0∞) * μ Set.univ + ε / 2
            < ε / 2 + ε / 2 :=
              ENNReal.add_lt_add_of_lt_of_le hεhalf_ne_top hδnn_mul le_rfl
        _ = ε := ENNReal.add_halves ε
    exact le_of_lt (lt_of_le_of_lt (hmain'.trans hsum_le) hsum_lt)

/-- The L1 error created by truncating a variable is bounded by the same
absolute tail integral used in the local uniform-integrability definition. -/
theorem prob_14_12_truncation_error_lintegral_le_tailExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M) :
    (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ) ≤
      prob_14_12_variableTailExpectation μ X M := by
  refine lintegral_mono ?_
  intro ω
  by_cases htail : M ≤ |X ω|
  · have hle := prob_14_12_truncation_error_abs_le_abs (M := M) (x := X ω) hM
    have hle' : ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ≤
        ENNReal.ofReal |X ω| := ENNReal.ofReal_le_ofReal hle
    simpa [prob_14_12_variableTailExpectation,
      prob_14_12_obligation_5_geTailExpectation,
      prob_14_12_obligation_5_geTailIntegrand, Set.indicator, htail] using hle'
  · have htrunc : prob_14_12_truncate M (X ω) = X ω :=
      prob_14_12_truncate_eq_self_of_not_strict_tail
        (M := M) (x := X ω) (by
          exact fun hstrict => htail (le_of_lt hstrict))
    simp [prob_14_12_obligation_5_geTailIntegrand, Set.indicator, htail, htrunc]

/-- Theorem-level landing for the sequence-tail part of the source truncation
route. -/
theorem prob_14_12_sequence_truncation_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) :
    prob_14_12_uniformIntegrableVariables μ Xseq →
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
        ∀ n : ℕ,
          (∫⁻ ω, ENNReal.ofReal
            |Xseq n ω - prob_14_12_truncate M (Xseq n ω)| ∂μ) ≤
            ENNReal.ofReal ε := by
  intro hUI ε hε
  rcases hUI ε hε with ⟨M, hM, htail⟩
  refine ⟨M, hM, ?_⟩
  intro n
  exact le_trans
    (prob_14_12_truncation_error_lintegral_le_tailExpectation μ (Xseq n) hM)
    (htail n)

/-- Increasing the symmetric truncation level can only decrease the pointwise
truncation error. -/
theorem prob_14_12_truncation_error_mono
    {M R x : ℝ} (hM : 0 ≤ M) (hMR : M ≤ R) :
    |x - prob_14_12_truncate R x| ≤
      |x - prob_14_12_truncate M x| := by
  have hR : 0 ≤ R := hM.trans hMR
  by_cases hxloR : x < -R
  · have hxloM : x < -M := by linarith
    have hmaxR : max x (-R) = -R := max_eq_right (le_of_lt hxloR)
    have hminR : min (max x (-R)) R = -R := by
      rw [hmaxR]
      exact min_eq_left (by linarith)
    have hmaxM : max x (-M) = -M := max_eq_right (le_of_lt hxloM)
    have hminM : min (max x (-M)) M = -M := by
      rw [hmaxM]
      exact min_eq_left (by linarith)
    have hdiffR : x - (-R) ≤ 0 := by linarith
    have hdiffM : x - (-M) ≤ 0 := by linarith
    have htrR : prob_14_12_truncate R x = -R := by
      simpa [prob_14_12_truncate] using hminR
    have htrM : prob_14_12_truncate M x = -M := by
      simpa [prob_14_12_truncate] using hminM
    rw [htrR, htrM, abs_of_nonpos hdiffR, abs_of_nonpos hdiffM]
    linarith
  · by_cases hxhiR : R < x
    · have hxhiM : M < x := lt_of_le_of_lt hMR hxhiR
      have hmaxR : max x (-R) = x := max_eq_left (by linarith)
      have hminR : min (max x (-R)) R = R := by
        rw [hmaxR]
        exact min_eq_right (le_of_lt hxhiR)
      have hmaxM : max x (-M) = x := max_eq_left (by linarith)
      have hminM : min (max x (-M)) M = M := by
        rw [hmaxM]
        exact min_eq_right (le_of_lt hxhiM)
      have hdiffR : 0 ≤ x - R := by linarith
      have hdiffM : 0 ≤ x - M := by linarith
      have htrR : prob_14_12_truncate R x = R := by
        simpa [prob_14_12_truncate] using hminR
      have htrM : prob_14_12_truncate M x = M := by
        simpa [prob_14_12_truncate] using hminM
      rw [htrR, htrM, abs_of_nonneg hdiffR, abs_of_nonneg hdiffM]
      linarith
    · have hgeR : -R ≤ x := le_of_not_gt hxloR
      have hleR : x ≤ R := le_of_not_gt hxhiR
      have hmaxR : max x (-R) = x := max_eq_left hgeR
      have hminR : min (max x (-R)) R = x := by
        rw [hmaxR]
        exact min_eq_left hleR
      have htrR : prob_14_12_truncate R x = x := by
        simpa [prob_14_12_truncate] using hminR
      rw [htrR, sub_self, abs_zero]
      exact abs_nonneg _

/-- Integral monotonicity form of truncation-error monotonicity. -/
theorem prob_14_12_truncation_error_lintegral_mono
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {M R : ℝ} (hM : 0 ≤ M) (hMR : M ≤ R) :
    (∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate R (X ω)| ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal |X ω - prob_14_12_truncate M (X ω)| ∂μ := by
  refine lintegral_mono ?_
  intro ω
  exact ENNReal.ofReal_le_ofReal
    (prob_14_12_truncation_error_mono (M := M) (R := R) (x := X ω) hM hMR)

theorem prob_14_12_truncation_route_pointwise_triangle
    {Ω : Type*} (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (M : ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal |Xseq n ω - X ω| ≤
      ENNReal.ofReal
          |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| +
        ENNReal.ofReal
          |prob_14_12_truncatedSequence Xseq M n ω -
            prob_14_12_truncatedLimit X M ω| +
        ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| := by
  set a : ℝ := Xseq n ω
  set b : ℝ := prob_14_12_truncatedSequence Xseq M n ω
  set c : ℝ := prob_14_12_truncatedLimit X M ω
  set d : ℝ := X ω
  have hreal : |a - d| ≤ |a - b| + |b - c| + |d - c| := by
    have hbd : |b - d| ≤ |b - c| + |c - d| := abs_sub_le b c d
    calc
      |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
      _ ≤ |a - b| + (|b - c| + |c - d|) := by linarith
      _ = |a - b| + |b - c| + |d - c| := by
        rw [abs_sub_comm c d]
        abel
  calc
    ENNReal.ofReal |Xseq n ω - X ω|
        ≤ ENNReal.ofReal
          (|Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| +
            |prob_14_12_truncatedSequence Xseq M n ω -
              prob_14_12_truncatedLimit X M ω| +
            |X ω - prob_14_12_truncatedLimit X M ω|) := by
          simpa [a, b, c, d] using ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal
          |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| +
        ENNReal.ofReal
          |prob_14_12_truncatedSequence Xseq M n ω -
            prob_14_12_truncatedLimit X M ω| +
        ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| := by
          rw [ENNReal.ofReal_add
            (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]

/-- The three-term `L1` truncation triangle estimate used in the final
assembly step. -/
theorem prob_14_12_truncation_route_lintegral_triangle
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (M : ℝ) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal |Xseq n ω - X ω| ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal
        |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) +
      (∫⁻ ω, ENNReal.ofReal
        |prob_14_12_truncatedSequence Xseq M n ω -
          prob_14_12_truncatedLimit X M ω| ∂μ) +
      (∫⁻ ω, ENNReal.ofReal
        |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) := by
  let A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω|
  let B : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal
      |prob_14_12_truncatedSequence Xseq M n ω -
        prob_14_12_truncatedLimit X M ω|
  let C : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal |X ω - prob_14_12_truncatedLimit X M ω|
  have hA : AEMeasurable A μ := by
    apply Measurable.aemeasurable
    dsimp [A, prob_14_12_truncatedSequence, prob_14_12_truncate]
    measurability
  have hB : AEMeasurable B μ := by
    apply Measurable.aemeasurable
    dsimp [B, prob_14_12_truncatedSequence, prob_14_12_truncatedLimit,
      prob_14_12_truncate]
    measurability
  calc
    (∫⁻ ω, ENNReal.ofReal |Xseq n ω - X ω| ∂μ)
        ≤ ∫⁻ ω, A ω + B ω + C ω ∂μ := by
          refine lintegral_mono ?_
          intro ω
          simpa [A, B, C] using
            prob_14_12_truncation_route_pointwise_triangle Xseq X M n ω
    _ = (∫⁻ ω, A ω + B ω ∂μ) + ∫⁻ ω, C ω ∂μ := by
          rw [lintegral_add_left' (hA.add hB)]
    _ = ((∫⁻ ω, A ω ∂μ) + ∫⁻ ω, B ω ∂μ) + ∫⁻ ω, C ω ∂μ := by
          rw [lintegral_add_left' hA]
    _ = (∫⁻ ω, ENNReal.ofReal
          |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) +
        (∫⁻ ω, ENNReal.ofReal
          |prob_14_12_truncatedSequence Xseq M n ω -
            prob_14_12_truncatedLimit X M ω| ∂μ) +
        (∫⁻ ω, ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) := by
          simp [A, B, C, add_assoc]

/-- Final truncation-route assembly. -/
theorem prob_14_12_truncation_route_assembles_mean_obligation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hSeqTail :
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
        ∀ n : ℕ,
          (∫⁻ ω, ENNReal.ofReal
            |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) ≤
            ENNReal.ofReal ε)
    (hBounded :
      ∀ M : ℝ, 0 ≤ M →
        prob_14_12_convergesInMean μ
          (prob_14_12_truncatedSequence Xseq M)
          (prob_14_12_truncatedLimit X M))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
        (∫⁻ ω, ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) ≤
          ENNReal.ofReal ε) :
    prob_14_12_convergesInMean μ Xseq X := by
  rw [prob_14_12_convergesInMean]
  refine ENNReal.tendsto_nhds_zero.mpr ?_
  intro ε hε
  by_cases hεtop : ε = ∞
  · filter_upwards [] with n
    rw [hεtop]
    exact le_top
  · rcases ENNReal.exists_nnreal_pos_mul_lt
      (a := (3 : ℝ≥0∞)) (b := ε) (by norm_num) hε.ne' with
      ⟨δnn, hδnn_pos, hδnn_mul⟩
    let δ : ℝ := (δnn : ℝ)
    have hδ_pos : 0 < δ := by exact_mod_cast hδnn_pos
    rcases hSeqTail δ hδ_pos with ⟨Mseq, hMseq, hSeqTailMseq⟩
    rcases hLimitTail δ hδ_pos with ⟨Mlim, hMlim, hLimitTailMlim⟩
    let M : ℝ := max Mseq Mlim
    have hM : 0 ≤ M := le_trans hMseq (le_max_left Mseq Mlim)
    have hMseqM : Mseq ≤ M := le_max_left Mseq Mlim
    have hMlimM : Mlim ≤ M := le_max_right Mseq Mlim
    have hSeqTailM :
        ∀ n : ℕ,
          (∫⁻ ω, ENNReal.ofReal
            |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) ≤
            ENNReal.ofReal δ := by
      intro n
      exact
        (prob_14_12_truncation_error_lintegral_mono
          (μ := μ) (X := Xseq n) (M := Mseq) (R := M) hMseq hMseqM).trans
          (by simpa [prob_14_12_truncatedSequence] using hSeqTailMseq n)
    have hLimitTailM :
        (∫⁻ ω, ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) ≤
            ENNReal.ofReal δ := by
      exact
        (prob_14_12_truncation_error_lintegral_mono
          (μ := μ) (X := X) (M := Mlim) (R := M) hMlim hMlimM).trans
          (by simpa [prob_14_12_truncatedLimit] using hLimitTailMlim)
    have hBoundedM := hBounded M hM
    rw [prob_14_12_convergesInMean] at hBoundedM
    have hδenn_pos : 0 < (δnn : ℝ≥0∞) := by exact_mod_cast hδnn_pos
    have hBoundedEventually :=
      (ENNReal.tendsto_nhds_zero.mp hBoundedM)
        (δnn : ℝ≥0∞) hδenn_pos
    filter_upwards [hBoundedEventually] with n hMid
    have hTriangle :=
      prob_14_12_truncation_route_lintegral_triangle
        μ Xseq X hXseq hX M n
    have hSeqN :
        (∫⁻ ω, ENNReal.ofReal
          |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) ≤
          (δnn : ℝ≥0∞) := by
      simpa [δ, ENNReal.ofReal_coe_nnreal] using hSeqTailM n
    have hLimitN :
        (∫⁻ ω, ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) ≤
          (δnn : ℝ≥0∞) := by
      simpa [δ, ENNReal.ofReal_coe_nnreal] using hLimitTailM
    have hsum :
        (∫⁻ ω, ENNReal.ofReal
          |Xseq n ω - prob_14_12_truncatedSequence Xseq M n ω| ∂μ) +
        (∫⁻ ω, ENNReal.ofReal
          |prob_14_12_truncatedSequence Xseq M n ω -
            prob_14_12_truncatedLimit X M ω| ∂μ) +
        (∫⁻ ω, ENNReal.ofReal
          |X ω - prob_14_12_truncatedLimit X M ω| ∂μ) ≤
          (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞) := by
      exact add_le_add (add_le_add hSeqN hMid) hLimitN
    have hthree :
        (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞) < ε := by
      calc
        (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞) + (δnn : ℝ≥0∞)
            = (δnn : ℝ≥0∞) * (3 : ℝ≥0∞) := by
              conv_rhs =>
                rw [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num]
                rw [mul_add, mul_add, mul_one]
        _ < ε := hδnn_mul
    exact le_of_lt (lt_of_le_of_lt (hTriangle.trans hsum) hthree)

/-- Source-facing proof of Problem 14.12(b)'s mean-convergence implication,
using the reviewed truncation route. -/
theorem prob_14_12_uniformIntegrable_probability_to_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq)
    (hProb : prob_14_12_convergesInProbability μ Xseq X) :
    prob_14_12_convergesInMean μ Xseq X := by
  exact prob_14_12_truncation_route_assembles_mean_obligation
    μ Xseq X hXseq hX
    (prob_14_12_sequence_truncation_tail μ Xseq hUI)
    (prob_14_12_bounded_truncations_convergeInMean_obligation μ Xseq X hProb)
    (fun ε hε =>
      prob_14_12_limit_truncation_tail_obligation
        μ Xseq X hXseq hUI hProb hε)

