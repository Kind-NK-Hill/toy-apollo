/-
TASK ID: ex_14_4_2
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.common_support.chapter14_triangular_array_support
import ProbabilityTheory.chapter_14.thm_14_7




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

 
def ex_14_4_2_poissonMean (lam : ℝ) : ℝ :=
  lam

 
def ex_14_4_2_poissonVariance (lam : ℝ) : ℝ :=
  lam

theorem ex_14_4_2_poissonMean_one :
    ex_14_4_2_poissonMean 1 = 1 := by
  rfl

theorem ex_14_4_2_poissonVariance_one :
    ex_14_4_2_poissonVariance 1 = 1 := by
  rfl

 
def ex_14_4_2_poissonCharacteristic (lam : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1))



def ex_14_4_2_poissonSumCharacteristic (n : ℕ) (t : ℝ) : ℂ :=
  ex_14_4_2_poissonCharacteristic (n + 1 : ℝ) t

theorem ex_14_4_2_poissonSumCharacteristic_eq (n : ℕ) (t : ℝ) :
    ex_14_4_2_poissonSumCharacteristic n t =
      ex_14_4_2_poissonCharacteristic (n + 1 : ℝ) t := by
  rfl



def ex_14_4_2_poissonRealMeasure (lam : NNReal) : Measure ℝ :=
  (ProbabilityTheory.poissonMeasure lam).map (fun n : ℕ => (n : ℝ))

instance ex_14_4_2_poissonRealMeasure.instIsProbabilityMeasure (lam : NNReal) :
    IsProbabilityMeasure (ex_14_4_2_poissonRealMeasure lam) := by
  unfold ex_14_4_2_poissonRealMeasure
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable)

private lemma ex_14_4_2_poissonPMF_toReal (lam : NNReal) (n : ℕ) :
    ((ProbabilityTheory.poissonPMF lam) n).toReal =
      ProbabilityTheory.poissonPMFReal lam n := by
  rw [← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF lam n]
  exact ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg

private lemma ex_14_4_2_poissonMeasure_eq_poissonPMF_toMeasure (lam : NNReal) :
    ProbabilityTheory.poissonMeasure lam =
      (ProbabilityTheory.poissonPMF lam).toMeasure := by
  apply Measure.ext_of_singleton
  intro n
  rw [ProbabilityTheory.poissonMeasure_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
    ← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF]
  rfl

theorem ex_14_4_2_poissonRealMeasure_charFun (lam : NNReal) (t : ℝ) :
    charFun (ex_14_4_2_poissonRealMeasure lam) t =
      ex_14_4_2_poissonCharacteristic (lam : ℝ) t := by
  unfold ex_14_4_2_poissonRealMeasure ex_14_4_2_poissonCharacteristic
  rw [charFun_apply_real]
  rw [integral_map]
  · rw [ex_14_4_2_poissonMeasure_eq_poissonPMF_toMeasure]
    rw [PMF.integral_eq_tsum]
    · have hseries :
          HasSum
            (fun n : ℕ =>
              (((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ))) ^ n) /
                (n.factorial : ℂ))
            (Complex.exp ((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ)))) := by
        simpa [← Complex.exp_eq_exp_ℂ] using
          (NormedSpace.expSeries_div_hasSum_exp
            ((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ))) : HasSum
              (fun n : ℕ =>
                (((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ))) ^ n) /
                  (n.factorial : ℂ))
              (NormedSpace.exp ((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ)))))
      have hscaled := hseries.mul_left (Complex.exp (-(lam : ℂ)))
      have hsum := hscaled.tsum_eq
      calc
        (∑' (a : ℕ), ((ProbabilityTheory.poissonPMF lam) a).toReal •
            Complex.exp ((t : ℂ) * (a : ℂ) * Complex.I))
            = ∑' n : ℕ,
                Complex.exp (-(lam : ℂ)) *
                  ((((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ))) ^ n) /
                    (n.factorial : ℂ)) := by
              refine tsum_congr fun n => ?_
              have hexp_pow :
                  Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) =
                    Complex.exp (Complex.I * (t : ℂ)) ^ n := by
                rw [← Complex.exp_nat_mul (Complex.I * (t : ℂ)) n]
                congr 1
                ring
              rw [ex_14_4_2_poissonPMF_toReal, ProbabilityTheory.poissonPMFReal,
                hexp_pow]
              simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
                Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_exp,
                Complex.ofReal_neg]
              ring_nf
        _ = Complex.exp (-(lam : ℂ)) *
              Complex.exp ((lam : ℂ) * Complex.exp (Complex.I * (t : ℂ))) := hsum
        _ = Complex.exp ((lam : ℂ) *
              (Complex.exp (Complex.I * (t : ℂ)) - 1)) := by
            rw [← Complex.exp_add]
            congr 1
            ring
    · exact (integrable_const (1 : ℂ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  · exact AEStronglyMeasurable.of_discrete.aemeasurable
  · exact (by fun_prop)

theorem ex_14_4_2_poissonCharacteristic_mul
    (lam mu t : ℝ) :
    ex_14_4_2_poissonCharacteristic lam t *
        ex_14_4_2_poissonCharacteristic mu t =
      ex_14_4_2_poissonCharacteristic (lam + mu) t := by
  unfold ex_14_4_2_poissonCharacteristic
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_add]
  ring_nf

 
def ex_14_4_2_poissonCanonicalIntegrability : Prop :=
  Integrable (fun x : ℝ => x)
    (ex_14_4_2_poissonRealMeasure (1 : NNReal))

lemma ex_14_4_2_summable_nat_div_factorial :
    Summable (fun n : ℕ => (n : ℝ) / n.factorial) := by
  rw [← summable_nat_add_iff 1]
  exact (Real.summable_pow_div_factorial (1 : ℝ)).congr fun n => by
    rw [Nat.factorial_succ]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [Nat.cast_mul, hn]
    rw [Nat.cast_mul]
    norm_num
    ring

lemma ex_14_4_2_poisson_one_first_moment_terms_summable :
    Summable (fun n : ℕ =>
      ((ProbabilityTheory.poissonPMF (1 : NNReal) n).toReal) * ‖(n : ℝ)‖) := by
  exact (Summable.mul_left (Real.exp (-1))
      ex_14_4_2_summable_nat_div_factorial).congr fun n => by
    rw [← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF (1 : NNReal) n]
    rw [ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg]
    simp [ProbabilityTheory.poissonPMFReal, div_eq_mul_inv]
    ring

lemma ex_14_4_2_poisson_one_natCast_integrable :
    Integrable (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure (1 : NNReal)) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  exact
    (Summable.mul_left (Real.exp (-1))
      ex_14_4_2_summable_nat_div_factorial).congr fun n => by
        simp [div_eq_mul_inv]
        ring

 
theorem ex_14_4_2_poissonCanonicalIntegrability_proved :
    ex_14_4_2_poissonCanonicalIntegrability := by
  unfold ex_14_4_2_poissonCanonicalIntegrability ex_14_4_2_poissonRealMeasure
  exact (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x) (f := fun n : ℕ => (n : ℝ))
      (by fun_prop)
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable)).2 (by
    simpa [Function.comp_def] using ex_14_4_2_poisson_one_natCast_integrable)

 
def ex_14_4_2_poissonCanonicalSquareIntegrability : Prop :=
  Integrable (fun x : ℝ => x ^ 2)
    (ex_14_4_2_poissonRealMeasure (1 : NNReal))

lemma ex_14_4_2_summable_nat_sq_div_factorial :
    Summable (fun n : ℕ => ((n : ℝ) ^ 2) / n.factorial) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / n.factorial) := by
    simpa using Real.summable_pow_div_factorial (1 : ℝ)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n + 1).factorial) := by
    simpa using ((summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) ^ n / n.factorial) 1).2
        (Real.summable_pow_div_factorial (1 : ℝ)))
  rw [← summable_nat_add_iff 2]
  exact (h0.add h1).congr fun n => by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hn1, hn2, hnf]
    ring

lemma ex_14_4_2_poisson_one_second_moment_terms_summable :
    Summable (fun n : ℕ =>
      ((ProbabilityTheory.poissonPMF (1 : NNReal) n).toReal) * ‖((n : ℝ) ^ 2)‖) := by
  exact (Summable.mul_left (Real.exp (-1))
      ex_14_4_2_summable_nat_sq_div_factorial).congr fun n => by
    rw [← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF (1 : NNReal) n]
    rw [ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg]
    simp [ProbabilityTheory.poissonPMFReal, div_eq_mul_inv]
    ring

lemma ex_14_4_2_poisson_one_natCast_sq_integrable :
    Integrable (fun n : ℕ => ((n : ℝ) ^ 2))
      (ProbabilityTheory.poissonMeasure (1 : NNReal)) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  exact
    (Summable.mul_left (Real.exp (-1))
      ex_14_4_2_summable_nat_sq_div_factorial).congr fun n => by
        simp [div_eq_mul_inv]
        ring

 
theorem ex_14_4_2_poissonCanonicalSquareIntegrability_proved :
    ex_14_4_2_poissonCanonicalSquareIntegrability := by
  unfold ex_14_4_2_poissonCanonicalSquareIntegrability ex_14_4_2_poissonRealMeasure
  exact (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x ^ 2) (f := fun n : ℕ => (n : ℝ))
      (by fun_prop)
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable)).2 (by
    simpa [Function.comp_def] using ex_14_4_2_poisson_one_natCast_sq_integrable)

 
def ex_14_4_2_poissonCanonicalMeanOne : Prop :=
  (∫ x : ℝ, x ∂(ex_14_4_2_poissonRealMeasure (1 : NNReal))) =
    ex_14_4_2_poissonMean 1

lemma ex_14_4_2_tsum_one_div_factorial :
    (∑' n : ℕ, (1 : ℝ) / n.factorial) = Real.exp 1 := by
  simpa [← Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).tsum_eq

lemma ex_14_4_2_tsum_nat_div_factorial :
    (∑' n : ℕ, (n : ℝ) / n.factorial) = Real.exp 1 := by
  rw [ex_14_4_2_summable_nat_div_factorial.tsum_eq_zero_add]
  norm_num
  calc
    (∑' n : ℕ, ((n : ℝ) + 1) / (n + 1).factorial) =
        ∑' n : ℕ, (1 : ℝ) / n.factorial := by
      apply tsum_congr
      intro n
      rw [Nat.factorial_succ]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp [Nat.cast_mul, hn]
      rw [Nat.cast_mul]
      norm_num
    _ = Real.exp 1 := ex_14_4_2_tsum_one_div_factorial

lemma ex_14_4_2_poisson_one_natCast_integral :
    (∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure (1 : NNReal)) = 1 := by
  calc
    (∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure (1 : NNReal)) =
        ∑' n : ℕ, Real.exp (-1) * ((n : ℝ) / n.factorial) := by
      rw [ProbabilityTheory.integral_poissonMeasure]
      apply tsum_congr
      intro n
      simp [smul_eq_mul, div_eq_mul_inv]
      ring
    _ = Real.exp (-1) * (∑' n : ℕ, (n : ℝ) / n.factorial) := by
      rw [tsum_mul_left]
    _ = 1 := by
      rw [ex_14_4_2_tsum_nat_div_factorial, ← Real.exp_add]
      norm_num

 
theorem ex_14_4_2_poissonCanonicalMeanOne_proved :
    ex_14_4_2_poissonCanonicalMeanOne := by
  unfold ex_14_4_2_poissonCanonicalMeanOne ex_14_4_2_poissonRealMeasure
    ex_14_4_2_poissonMean
  rw [MeasureTheory.integral_map
    ((MeasurableEmbedding.natCast (α := ℝ)).measurable.aemeasurable)
    (by fun_prop)]
  exact ex_14_4_2_poisson_one_natCast_integral

 
def ex_14_4_2_poissonCanonicalSecondMomentTwo : Prop :=
  (∫ x : ℝ, x ^ 2 ∂(ex_14_4_2_poissonRealMeasure (1 : NNReal))) = (2 : ℝ)

lemma ex_14_4_2_tsum_shifted_one_div_factorial :
    (∑' n : ℕ, (1 : ℝ) / (n + 1).factorial) = Real.exp 1 - 1 := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / n.factorial) := by
    simpa using Real.summable_pow_div_factorial (1 : ℝ)
  have hsplit :
      Real.exp 1 = (1 : ℝ) + ∑' n : ℕ, (1 : ℝ) / (n + 1).factorial := by
    rw [← ex_14_4_2_tsum_one_div_factorial]
    simpa using h0.tsum_eq_zero_add
  linarith

lemma ex_14_4_2_tsum_nat_sq_div_factorial :
    (∑' n : ℕ, ((n : ℝ) ^ 2) / n.factorial) = 2 * Real.exp 1 := by
  let f : ℕ → ℝ := fun n => ((n : ℝ) ^ 2) / n.factorial
  have hsq : Summable f := by
    simpa [f] using ex_14_4_2_summable_nat_sq_div_factorial
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / n.factorial) := by
    simpa using Real.summable_pow_div_factorial (1 : ℝ)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n + 1).factorial) := by
    simpa using ((summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) ^ n / n.factorial) 1).2
        (Real.summable_pow_div_factorial (1 : ℝ)))
  have htail_sum :
      (∑' n : ℕ, f (n + 2)) = 2 * Real.exp 1 - 1 := by
    calc
      (∑' n : ℕ, f (n + 2)) =
          ∑' n : ℕ, ((1 : ℝ) / n.factorial + (1 : ℝ) / (n + 1).factorial) := by
        apply tsum_congr
        intro n
        simp only [f, Nat.cast_add, Nat.cast_ofNat, Nat.factorial_succ,
          Nat.cast_mul]
        have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
        have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
        field_simp [hn1, hn2, hnf]
        ring
      _ =
          (∑' n : ℕ, (1 : ℝ) / n.factorial) +
            ∑' n : ℕ, (1 : ℝ) / (n + 1).factorial := by
        exact h0.tsum_add h1
      _ = Real.exp 1 + (Real.exp 1 - 1) := by
        rw [ex_14_4_2_tsum_one_div_factorial,
          ex_14_4_2_tsum_shifted_one_div_factorial]
      _ = 2 * Real.exp 1 - 1 := by ring
  have htail_summable : Summable (fun n : ℕ => f (n + 2)) := by
    exact (summable_nat_add_iff (f := f) 2).2 hsq
  have htail_hasSum : HasSum (fun n : ℕ => f (n + 2)) (2 * Real.exp 1 - 1) := by
    rw [← htail_sum]
    exact htail_summable.hasSum
  have hfull_hasSum : HasSum f ((2 * Real.exp 1 - 1) +
      Finset.sum (Finset.range 2) f) :=
    (hasSum_nat_add_iff (f := f) 2).1 htail_hasSum
  have hinit : Finset.sum (Finset.range 2) f = (1 : ℝ) := by
    norm_num [f]
  calc
    (∑' n : ℕ, ((n : ℝ) ^ 2) / n.factorial) = ∑' n : ℕ, f n := by
      rfl
    _ = (2 * Real.exp 1 - 1) + Finset.sum (Finset.range 2) f := by
      exact hfull_hasSum.tsum_eq
    _ = 2 * Real.exp 1 := by
      rw [hinit]
      ring

lemma ex_14_4_2_poisson_one_natCast_sq_integral :
    (∫ n : ℕ, ((n : ℝ) ^ 2) ∂ProbabilityTheory.poissonMeasure (1 : NNReal)) = 2 := by
  calc
    (∫ n : ℕ, ((n : ℝ) ^ 2) ∂ProbabilityTheory.poissonMeasure (1 : NNReal)) =
        ∑' n : ℕ, Real.exp (-1) * (((n : ℝ) ^ 2) / n.factorial) := by
      rw [ProbabilityTheory.integral_poissonMeasure]
      apply tsum_congr
      intro n
      simp [smul_eq_mul, div_eq_mul_inv]
      ring
    _ = Real.exp (-1) * (∑' n : ℕ, ((n : ℝ) ^ 2) / n.factorial) := by
      rw [tsum_mul_left]
    _ = 2 := by
      rw [ex_14_4_2_tsum_nat_sq_div_factorial]
      calc
        Real.exp (-1) * (2 * Real.exp 1) =
            2 * (Real.exp (-1) * Real.exp 1) := by ring
        _ = 2 * Real.exp ((-1 : ℝ) + 1) := by rw [← Real.exp_add]
        _ = 2 := by norm_num

 
theorem ex_14_4_2_poissonCanonicalSecondMomentTwo_proved :
    ex_14_4_2_poissonCanonicalSecondMomentTwo := by
  unfold ex_14_4_2_poissonCanonicalSecondMomentTwo ex_14_4_2_poissonRealMeasure
  rw [MeasureTheory.integral_map
    ((MeasurableEmbedding.natCast (α := ℝ)).measurable.aemeasurable)
    (by fun_prop)]
  exact ex_14_4_2_poisson_one_natCast_sq_integral

 
def ex_14_4_2_poissonCanonicalVarianceOne : Prop :=
  ProbabilityTheory.variance (fun x : ℝ => x)
      (ex_14_4_2_poissonRealMeasure (1 : NNReal)) = (1 : ℝ) ^ 2



theorem ex_14_4_2_poissonCanonicalVarianceOne_proved :
    ex_14_4_2_poissonCanonicalVarianceOne := by
  let μ := ex_14_4_2_poissonRealMeasure (1 : NNReal)
  have hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = (2 : ℝ) := by
    change ex_14_4_2_poissonCanonicalSecondMomentTwo
    exact ex_14_4_2_poissonCanonicalSecondMomentTwo_proved
  have hmean : (∫ x : ℝ, x ∂μ) = (1 : ℝ) := by
    simpa [μ, ex_14_4_2_poissonCanonicalMeanOne, ex_14_4_2_poissonMean] using
      ex_14_4_2_poissonCanonicalMeanOne_proved
  have hsquare_int : Integrable (fun x : ℝ => x ^ 2) μ := by
    change ex_14_4_2_poissonCanonicalSquareIntegrability
    exact ex_14_4_2_poissonCanonicalSquareIntegrability_proved
  have h_id_aestrong : AEStronglyMeasurable (fun x : ℝ => x) μ := by
    fun_prop
  have h_id_memLp : MemLp (fun x : ℝ => x) 2 μ := by
    exact (MeasureTheory.memLp_two_iff_integrable_sq h_id_aestrong).2 hsquare_int
  unfold ex_14_4_2_poissonCanonicalVarianceOne
  change ProbabilityTheory.variance (fun x : ℝ => x) μ = (1 : ℝ) ^ 2
  rw [ProbabilityTheory.variance_eq_sub h_id_memLp]
  change (∫ x : ℝ, x ^ 2 ∂μ) - (∫ x : ℝ, x ∂μ) ^ 2 = (1 : ℝ) ^ 2
  rw [hsecond, hmean]
  norm_num

 
def ex_14_4_2_hasPoissonLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (lam : NNReal) : Prop :=
  P.map X = ex_14_4_2_poissonRealMeasure lam

theorem ex_14_4_2_independent_sum_has_poisson_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} {lam mu : NNReal}
    (hXmeas : AEMeasurable X P) (hYmeas : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y)
    (hXlaw : ex_14_4_2_hasPoissonLaw P X lam)
    (hYlaw : ex_14_4_2_hasPoissonLaw P Y mu) :
    ex_14_4_2_hasPoissonLaw P (fun ω => X ω + Y ω) (lam + mu) := by
  unfold ex_14_4_2_hasPoissonLaw
  apply Measure.ext_of_charFun
  ext t
  calc
    charFun (P.map fun ω => X ω + Y ω) t
        = (charFun (P.map X) * charFun (P.map Y)) t := by
            rw [hXY.charFun_map_fun_add_eq_mul hXmeas hYmeas]
    _ = charFun (P.map X) t * charFun (P.map Y) t := rfl
    _ = charFun (ex_14_4_2_poissonRealMeasure lam) t *
          charFun (ex_14_4_2_poissonRealMeasure mu) t := by
            rw [hXlaw, hYlaw]
    _ = ex_14_4_2_poissonCharacteristic (lam : ℝ) t *
          ex_14_4_2_poissonCharacteristic (mu : ℝ) t := by
            rw [ex_14_4_2_poissonRealMeasure_charFun,
              ex_14_4_2_poissonRealMeasure_charFun]
    _ = ex_14_4_2_poissonCharacteristic ((lam + mu : NNReal) : ℝ) t := by
            simpa [NNReal.coe_add] using
              ex_14_4_2_poissonCharacteristic_mul (lam : ℝ) (mu : ℝ) t
    _ = charFun (ex_14_4_2_poissonRealMeasure (lam + mu)) t := by
            rw [ex_14_4_2_poissonRealMeasure_charFun]



structure ex_14_4_2_PoissonSourceSetup
    (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure P
  X : ℕ → Ω → ℝ
  hX : ∀ k : ℕ, AEMeasurable (X k) P
  hIndep : ProbabilityTheory.iIndepFun X P
  hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P



def ex_14_4_2_poissonSourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  ∀ k : ℕ, ex_14_4_2_hasPoissonLaw S.P (S.X k) (1 : NNReal)



def ex_14_4_2_partialSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k : Fin (n + 1), X k.val ω

theorem ex_14_4_2_partialSum_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ k : ℕ, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (ex_14_4_2_partialSum X n) P := by
  unfold ex_14_4_2_partialSum
  fun_prop

theorem ex_14_4_2_partialSum_eq_range
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    ex_14_4_2_partialSum X n =
      ∑ k ∈ Finset.range (n + 1), X k := by
  funext ω
  unfold ex_14_4_2_partialSum
  simpa using Fin.sum_univ_eq_sum_range (fun k => X k ω) (n + 1)

theorem ex_14_4_2_partialSum_succ
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    ex_14_4_2_partialSum X (n + 1) =
      fun ω => ex_14_4_2_partialSum X n ω + X (n + 1) ω := by
  rw [ex_14_4_2_partialSum_eq_range X (n + 1),
    ex_14_4_2_partialSum_eq_range X n]
  funext ω
  simp [Finset.sum_range_succ]

theorem ex_14_4_2_partialSum_indep_next
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) (n : ℕ) :
    ex_14_4_2_partialSum X n ⟂ᵢ[P] X (n + 1) := by
  have hRange :
      (∑ j ∈ Finset.range (n + 1), X j) ⟂ᵢ[P] X (n + 1) := by
    simpa using hIndep.indepFun_finset_sum_of_notMem₀ hX
      (s := Finset.range (n + 1)) (i := n + 1) (by simp)
  exact hRange.congr
    (by rw [ex_14_4_2_partialSum_eq_range X n]) Filter.EventuallyEq.rfl



def ex_14_4_2_poissonSumLaws
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) :
    ℕ → ProbabilityMeasure ℝ :=
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  fun n =>
    thm_14_7_law S.P (ex_14_4_2_partialSum S.X n)
      (ex_14_4_2_partialSum_aemeasurable S.X S.hX n)



def ex_14_4_2_poissonMomentBridge
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  Integrable (S.X 0) S.P ∧
    Integrable (fun ω => (S.X 0 ω) ^ 2) S.P ∧
      S.P[S.X 0] = ex_14_4_2_poissonMean 1 ∧
        ProbabilityTheory.variance (S.X 0) S.P = (1 : ℝ) ^ 2



def ex_14_4_2_canonicalPoissonMomentBridge : Prop :=
  ex_14_4_2_poissonCanonicalIntegrability ∧
    ex_14_4_2_poissonCanonicalSquareIntegrability ∧
      ex_14_4_2_poissonCanonicalMeanOne ∧
        ex_14_4_2_poissonCanonicalVarianceOne

theorem ex_14_4_2_canonicalPoissonMomentBridge_of_parts
    (hIntegrable : ex_14_4_2_poissonCanonicalIntegrability)
    (hSquareIntegrable : ex_14_4_2_poissonCanonicalSquareIntegrability)
    (hMean : ex_14_4_2_poissonCanonicalMeanOne)
    (hVariance : ex_14_4_2_poissonCanonicalVarianceOne) :
    ex_14_4_2_canonicalPoissonMomentBridge := by
  exact ⟨hIntegrable, hSquareIntegrable, hMean, hVariance⟩



theorem ex_14_4_2_canonicalPoissonMomentBridge_proved :
    ex_14_4_2_canonicalPoissonMomentBridge := by
  exact ex_14_4_2_canonicalPoissonMomentBridge_of_parts
    ex_14_4_2_poissonCanonicalIntegrability_proved
    ex_14_4_2_poissonCanonicalSquareIntegrability_proved
    ex_14_4_2_poissonCanonicalMeanOne_proved
    ex_14_4_2_poissonCanonicalVarianceOne_proved



theorem ex_14_4_2_poissonMomentBridge_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S)
    (hCanonical : ex_14_4_2_canonicalPoissonMomentBridge) :
    ex_14_4_2_poissonMomentBridge S := by
  rcases hCanonical with ⟨hIntegrable, hSquareIntegrable, hMean, hVariance⟩
  have hMap : Measure.map (S.X 0) S.P =
      ex_14_4_2_poissonRealMeasure (1 : NNReal) := hSource 0
  have hIntegrableMap :
      Integrable (fun x : ℝ => x) (Measure.map (S.X 0) S.P) := by
    simpa [ex_14_4_2_poissonCanonicalIntegrability, hMap] using hIntegrable
  have hSquareIntegrableMap :
      Integrable (fun x : ℝ => x ^ 2) (Measure.map (S.X 0) S.P) := by
    simpa [ex_14_4_2_poissonCanonicalSquareIntegrability, hMap] using
      hSquareIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using
      (MeasureTheory.integrable_map_measure
        (g := fun x : ℝ => x) (by fun_prop) (S.hX 0)).1 hIntegrableMap
  · simpa [Function.comp_def] using
      (MeasureTheory.integrable_map_measure
        (g := fun x : ℝ => x ^ 2) (by fun_prop) (S.hX 0)).1 hSquareIntegrableMap
  · have hMeanMap :
        (∫ x : ℝ, x ∂Measure.map (S.X 0) S.P) =
          ex_14_4_2_poissonMean 1 := by
      simpa [ex_14_4_2_poissonCanonicalMeanOne, ex_14_4_2_poissonMean, hMap] using hMean
    have hIntegralMap :
        (∫ x : ℝ, x ∂Measure.map (S.X 0) S.P) = S.P[S.X 0] := by
      simpa [Function.comp_def] using
        (MeasureTheory.integral_map (S.hX 0)
          (by fun_prop :
            AEStronglyMeasurable (fun x : ℝ => x)
              (Measure.map (S.X 0) S.P)))
    rw [← hIntegralMap]
    exact hMeanMap
  · have hVarianceMap :
        ProbabilityTheory.variance (fun x : ℝ => x) (Measure.map (S.X 0) S.P) =
          (1 : ℝ) ^ 2 := by
      simpa [ex_14_4_2_poissonCanonicalVarianceOne, hMap] using hVariance
    have hVarianceId :
        ProbabilityTheory.variance (fun x : ℝ => x) (Measure.map (S.X 0) S.P) =
          ProbabilityTheory.variance (S.X 0) S.P := by
      change ProbabilityTheory.variance id (Measure.map (S.X 0) S.P) =
        ProbabilityTheory.variance (S.X 0) S.P
      exact ProbabilityTheory.variance_id_map (X := S.X 0) (μ := S.P) (S.hX 0)
    rw [← hVarianceId]
    exact hVarianceMap



theorem ex_14_4_2_poissonMomentBridge_of_sourceLaw_final
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ex_14_4_2_poissonMomentBridge S := by
  exact ex_14_4_2_poissonMomentBridge_of_sourceLaw S hSource
    ex_14_4_2_canonicalPoissonMomentBridge_proved

theorem ex_14_4_2_poissonMomentBridge_of_sourceLaw_and_canonical_parts
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S)
    (hIntegrable : ex_14_4_2_poissonCanonicalIntegrability)
    (hSquareIntegrable : ex_14_4_2_poissonCanonicalSquareIntegrability)
    (hMean : ex_14_4_2_poissonCanonicalMeanOne)
    (hVariance : ex_14_4_2_poissonCanonicalVarianceOne) :
    ex_14_4_2_poissonMomentBridge S := by
  exact ex_14_4_2_poissonMomentBridge_of_sourceLaw S hSource
    (ex_14_4_2_canonicalPoissonMomentBridge_of_parts
      hIntegrable hSquareIntegrable hMean hVariance)



def ex_14_4_2_poissonFiniteSumBridge
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  (∀ n : ℕ,
      ex_14_4_2_hasPoissonLaw S.P (ex_14_4_2_partialSum S.X n)
        ((n + 1 : ℕ) : NNReal)) ∧
    (∀ n : ℕ, ∀ t : ℝ,
      thm_14_1_characteristicFunction
          (ex_14_4_2_poissonSumLaws S n) t =
        ex_14_4_2_poissonSumCharacteristic n t)

theorem ex_14_4_2_partialSum_hasPoissonLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ∀ n : ℕ,
      ex_14_4_2_hasPoissonLaw S.P (ex_14_4_2_partialSum S.X n)
        (((n + 1 : ℕ) : NNReal)) := by
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  intro n
  induction n with
  | zero =>
      have hsum0 : ex_14_4_2_partialSum S.X 0 = S.X 0 := by
        funext ω
        unfold ex_14_4_2_partialSum
        simp
      simpa [ex_14_4_2_poissonSourceLaw, hsum0] using hSource 0
  | succ n ih =>
      have hInd :
          ex_14_4_2_partialSum S.X n ⟂ᵢ[S.P] S.X (n + 1) :=
        ex_14_4_2_partialSum_indep_next S.hX S.hIndep n
      have hAdd :
          ex_14_4_2_hasPoissonLaw S.P
            (fun ω => ex_14_4_2_partialSum S.X n ω + S.X (n + 1) ω)
            ((((n + 1 : ℕ) : NNReal) + (1 : NNReal))) := by
        exact ex_14_4_2_independent_sum_has_poisson_law
          (X := ex_14_4_2_partialSum S.X n) (Y := S.X (n + 1))
          (ex_14_4_2_partialSum_aemeasurable S.X S.hX n)
          (S.hX (n + 1)) hInd ih (hSource (n + 1))
      have hsum :
          ex_14_4_2_partialSum S.X (n + 1) =
            fun ω => ex_14_4_2_partialSum S.X n ω + S.X (n + 1) ω :=
        ex_14_4_2_partialSum_succ S.X n
      simpa [hsum, Nat.cast_add] using hAdd

theorem ex_14_4_2_poissonFiniteSumBridge_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ex_14_4_2_poissonFiniteSumBridge S := by
  let hLaw := ex_14_4_2_partialSum_hasPoissonLaw S hSource
  refine ⟨hLaw, ?_⟩
  intro n t
  change charFun (Measure.map (ex_14_4_2_partialSum S.X n) S.P) t =
    ex_14_4_2_poissonSumCharacteristic n t
  rw [hLaw n, ex_14_4_2_poissonRealMeasure_charFun]
  simp [ex_14_4_2_poissonSumCharacteristic]

 
def ex_14_4_2_standardizedPoissonLaws
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) :
    ℕ → ProbabilityMeasure ℝ :=
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  thm_14_7_standardizedSumLaws S.P S.X 1 1 S.hX



def ex_14_4_2_resolvedSourceBridges
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  ex_14_4_2_poissonSourceLaw S ∧
    ex_14_4_2_poissonMomentBridge S ∧
      ex_14_4_2_poissonFiniteSumBridge S



theorem ex_14_4_2_resolvedSourceBridges_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ex_14_4_2_resolvedSourceBridges S := by
  exact
    ⟨hSource,
      ex_14_4_2_poissonMomentBridge_of_sourceLaw_final S hSource,
      ex_14_4_2_poissonFiniteSumBridge_of_sourceLaw S hSource⟩



def ex_14_4_2_sourceConclusion
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  Tendsto (ex_14_4_2_standardizedPoissonLaws S)
    atTop (𝓝 thm_14_7_standardNormalLaw)



def ex_14_4_2_sourceRoute
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω) : Prop :=
  ex_14_4_2_resolvedSourceBridges S ∧
    ex_14_4_2_sourceConclusion S



abbrev ex_14_4_2_TriangularArrayNotation :=
  chapter14_TriangularArrayNotation



theorem ex_14_4_2_normalApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ex_14_4_2_sourceConclusion S := by
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  have hSigma : (0 : ℝ) < 1 := by norm_num
  have momentBridge :
      ex_14_4_2_poissonMomentBridge S :=
    ex_14_4_2_poissonMomentBridge_of_sourceLaw_final S hSource
  rcases momentBridge with
    ⟨integrableOne, squareIntegrableOne, meanOne, varianceOne⟩
  have meanOne' : S.P[S.X 0] = (1 : ℝ) := by
    simpa [ex_14_4_2_poissonMean] using meanOne
  simpa [ex_14_4_2_sourceConclusion, ex_14_4_2_standardizedPoissonLaws] using
    thm_14_7 S.P S.X 1 1 S.hX S.hIndep S.hIdent integrableOne
      squareIntegrableOne meanOne' varianceOne hSigma

 
theorem ex_14_4_2_weakLimit_by_CLT
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    thm_14_1_weakLimit (ex_14_4_2_standardizedPoissonLaws S) := by
  refine ⟨thm_14_7_standardNormalLaw, ?_⟩
  exact ex_14_4_2_normalApproximation S hSource

theorem ex_14_4_2_sourceRoute_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    ex_14_4_2_sourceRoute S := by
  exact
    ⟨ex_14_4_2_resolvedSourceBridges_of_sourceLaw S hSource,
      ex_14_4_2_normalApproximation S hSource⟩



theorem ex_14_4_2
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_2_PoissonSourceSetup Ω)
    (hSource : ex_14_4_2_poissonSourceLaw S) :
    Tendsto (ex_14_4_2_standardizedPoissonLaws S)
      atTop (𝓝 thm_14_7_standardNormalLaw) :=
  ex_14_4_2_normalApproximation S hSource
