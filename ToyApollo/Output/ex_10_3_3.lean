import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_4

/-
TASK ID: ex_10_3_3
TYPE: Example_Proof
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\textbf{Example 10.3.3 (Convergence in Distribution But Not in Probability)} \\
Consider two independent random variables $X$ and $Y$. Each of them is distributed according to $\operatorname{Ber}(1/2)$. Define $X_n$ to be equal to $X$ for all $n\geq 1$. We trivially have $X_n$ converging to $Y$ in distribution, because all distributions are identical. However, $X_n$ does not converge to $Y$ in probability, because
\[
P(\lvert X_n-Y\rvert=1)=\frac{1}{2}
\]
for all $n$. Hence, $P(\lvert X_n-Y\rvert\geq 0.99)=1/2$ for all $n$, and the sequence does not converge to $Y$ in probability.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal

abbrev ex_10_3_3_SampleSpace := Bool × Bool

lemma ex_10_3_3_quarter_add_quarter : (4⁻¹ : ENNReal) + 4⁻¹ = 2⁻¹ := by
  change ((↑(4 : NNReal) : ENNReal)⁻¹ + (↑(4 : NNReal) : ENNReal)⁻¹ =
    (↑(2 : NNReal) : ENNReal)⁻¹)
  rw [← ENNReal.coe_inv' (r := (4 : NNReal))]
  rw [← ENNReal.coe_inv' (r := (2 : NNReal))]
  change (↑(((4 : NNReal)⁻¹ + (4 : NNReal)⁻¹)) : ENNReal) =
    ↑((2 : NNReal)⁻¹)
  congr
  exact NNReal.eq (by norm_num)

lemma ex_10_3_3_half_add_quarter_add_quarter :
    (2⁻¹ : ENNReal) + 4⁻¹ + 4⁻¹ = 2⁻¹ + 2⁻¹ := by
  rw [add_assoc, ex_10_3_3_quarter_add_quarter]

/-- The four-point product space for two fair Bernoulli coordinates. -/
noncomputable def ex_10_3_3_mu : Measure ex_10_3_3_SampleSpace :=
  (1 / 4 : ENNReal) • Measure.dirac (true, true) +
  (1 / 4 : ENNReal) • Measure.dirac (true, false) +
  (1 / 4 : ENNReal) • Measure.dirac (false, true) +
  (1 / 4 : ENNReal) • Measure.dirac (false, false)

/-- First Bernoulli coordinate, encoded as a real-valued random variable. -/
def ex_10_3_3_X (ω : ex_10_3_3_SampleSpace) : ℝ :=
  if ω.1 then 1 else 0

/-- Second Bernoulli coordinate, encoded as a real-valued random variable. -/
def ex_10_3_3_Y (ω : ex_10_3_3_SampleSpace) : ℝ :=
  if ω.2 then 1 else 0

/-- The textbook sequence `X_n = X` for every `n`. -/
def ex_10_3_3_Xseq (_ : ℕ) : ex_10_3_3_SampleSpace → ℝ :=
  ex_10_3_3_X

/-- The Bernoulli `Ber(1/2)` law on `{0, 1}` as a measure on `ℝ`. -/
noncomputable def ex_10_3_3_bernoulliHalf : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
  (1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)

/-- Each joint atom of the two fair coordinates has probability `1/4`. -/
theorem ex_10_3_3_joint_atom_probability (a b : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.1 = a ∧ ω.2 = b} =
      (1 / 4 : ENNReal) := by
  cases a <;> cases b <;> simp [ex_10_3_3_mu]

/-- The first coordinate has Bernoulli one-bit marginal probabilities. -/
theorem ex_10_3_3_X_atom_probability (a : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.1 = a} =
      (1 / 2 : ENNReal) := by
  cases a <;> simp [ex_10_3_3_mu, ex_10_3_3_quarter_add_quarter]

/-- The second coordinate has Bernoulli one-bit marginal probabilities. -/
theorem ex_10_3_3_Y_atom_probability (b : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.2 = b} =
      (1 / 2 : ENNReal) := by
  cases b <;> simp [ex_10_3_3_mu, ex_10_3_3_quarter_add_quarter]

/-- The first coordinate is distributed as `Ber(1/2)`. -/
theorem ex_10_3_3_X_law :
    Measure.map ex_10_3_3_X ex_10_3_3_mu = ex_10_3_3_bernoulliHalf := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by measurability : Measurable ex_10_3_3_X) hs]
  simp only [ex_10_3_3_mu, ex_10_3_3_bernoulliHalf, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  unfold ex_10_3_3_X
  simp [Set.indicator]
  by_cases h0 : (0 : ℝ) ∈ s <;> by_cases h1 : (1 : ℝ) ∈ s <;>
    simp [h0, h1, ex_10_3_3_quarter_add_quarter,
      ex_10_3_3_half_add_quarter_add_quarter]

/-- The second coordinate is distributed as `Ber(1/2)`. -/
theorem ex_10_3_3_Y_law :
    Measure.map ex_10_3_3_Y ex_10_3_3_mu = ex_10_3_3_bernoulliHalf := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by measurability : Measurable ex_10_3_3_Y) hs]
  simp only [ex_10_3_3_mu, ex_10_3_3_bernoulliHalf, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  unfold ex_10_3_3_Y
  simp [Set.indicator]
  by_cases h0 : (0 : ℝ) ∈ s <;> by_cases h1 : (1 : ℝ) ∈ s <;>
    simp [h0, h1, ex_10_3_3_quarter_add_quarter,
      ex_10_3_3_half_add_quarter_add_quarter]

/-- Since both coordinates have the same Bernoulli law, the laws are identical. -/
theorem ex_10_3_3_equal_law :
    Measure.map ex_10_3_3_X ex_10_3_3_mu =
      Measure.map ex_10_3_3_Y ex_10_3_3_mu := by
  rw [ex_10_3_3_X_law, ex_10_3_3_Y_law]

/-- The textbook equality-event calculation: `P(|X_n - Y| = 1) = 1/2`. -/
theorem ex_10_3_3_unit_gap_probability (n : ℕ) :
    ex_10_3_3_mu
        {ω : ex_10_3_3_SampleSpace | |ex_10_3_3_Xseq n ω - ex_10_3_3_Y ω| = 1} =
      (1 / 2 : ENNReal) := by
  simp [ex_10_3_3_mu, ex_10_3_3_Xseq, ex_10_3_3_X, ex_10_3_3_Y,
    ex_10_3_3_quarter_add_quarter]

/-- The `0.99` deviation event also has probability `1/2`. -/
theorem ex_10_3_3_separation_probability (n : ℕ) :
    ex_10_3_3_mu
        (deviationEvent ex_10_3_3_Xseq ex_10_3_3_Y n ((99 : ℝ) / 100)) =
      (1 / 2 : ENNReal) := by
  simp [deviationEvent, ex_10_3_3_mu, ex_10_3_3_Xseq, ex_10_3_3_X,
    ex_10_3_3_Y, Set.indicator]
  norm_num
  exact ex_10_3_3_quarter_add_quarter

/-- The constant sequence has the same law as `Y`, hence converges in distribution. -/
theorem ex_10_3_3_converges_in_distribution :
    RandomVariablesConvergeInDistribution
      ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y := by
  intro x _
  simpa [RandomVariablesConvergeInDistribution, MeasuresConvergeInDistribution,
    CdfConvergesInDistribution, measureCdf, ex_10_3_3_Xseq, ex_10_3_3_equal_law] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (Measure.map ex_10_3_3_Y ex_10_3_3_mu).real (Iic x))
          atTop
          (nhds ((Measure.map ex_10_3_3_Y ex_10_3_3_mu).real (Iic x))))

/-- The positive separation probability prevents convergence in probability. -/
theorem ex_10_3_3_not_converges_in_probability :
    ¬ ConvergesInProbability ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y := by
  intro hprob
  have hε : (0 : ℝ) < (99 : ℝ) / 100 := by norm_num
  have hzero := hprob ((99 : ℝ) / 100) hε
  have hconst :
      Tendsto
        (fun n : ℕ =>
          ex_10_3_3_mu
            (deviationEvent ex_10_3_3_Xseq ex_10_3_3_Y n ((99 : ℝ) / 100)))
        atTop (nhds (1 / 2 : ENNReal)) := by
    simpa [ex_10_3_3_separation_probability] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ENNReal)) atTop (nhds (1 / 2 : ENNReal)))
  have huniq := tendsto_nhds_unique hzero hconst
  have hne : (1 / 2 : ENNReal) ≠ 0 := by norm_num
  exact hne huniq.symm

/--
Example 10.3.3: a constant sequence can converge in distribution to a random
variable without converging to it in probability.
-/
theorem ex_10_3_3 :
    RandomVariablesConvergeInDistribution
      ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y ∧
      ¬ ConvergesInProbability ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y := by
  exact ⟨ex_10_3_3_converges_in_distribution,
    ex_10_3_3_not_converges_in_probability⟩
