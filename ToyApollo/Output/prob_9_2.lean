/-
TASK ID: prob_9_2
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

noncomputable def poissonCharacteristicFunctionFormula (lam t : ℝ) : ℂ :=
  Complex.exp ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1))

noncomputable def poissonRealMeasure (lam : NNReal) : Measure ℝ :=
  (ProbabilityTheory.poissonMeasure lam).map (fun n : ℕ => (n : ℝ))

instance (lam : NNReal) : IsProbabilityMeasure (poissonRealMeasure lam) := by
  unfold poissonRealMeasure
  exact Measure.isProbabilityMeasure_map
    (AEStronglyMeasurable.of_discrete.aemeasurable)

private lemma poissonPMF_toReal (lam : NNReal) (n : ℕ) :
    ((ProbabilityTheory.poissonPMF lam) n).toReal =
      ProbabilityTheory.poissonPMFReal lam n := by
  rw [← ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF lam n]
  exact ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg

theorem poissonRealMeasure_charFun (lam : NNReal) (t : ℝ) :
    charFun (poissonRealMeasure lam) t =
      poissonCharacteristicFunctionFormula (lam : ℝ) t := by
  unfold poissonRealMeasure poissonCharacteristicFunctionFormula
  rw [charFun_apply_real]
  rw [integral_map]
  · unfold ProbabilityTheory.poissonMeasure
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
              rw [poissonPMF_toReal, ProbabilityTheory.poissonPMFReal, hexp_pow]
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

def HasPoissonLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (lam : NNReal) : Prop :=
  P.map X = poissonRealMeasure lam

def HasPoissonCharacteristicFunction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (lam : ℝ) : Prop :=
  ∀ t : ℝ, characteristicFunction P X t =
    poissonCharacteristicFunctionFormula lam t

theorem poissonCharacteristicFunctionFormula_mul
    (lam mu t : ℝ) :
    poissonCharacteristicFunctionFormula lam t *
        poissonCharacteristicFunctionFormula mu t =
      poissonCharacteristicFunctionFormula (lam + mu) t := by
  unfold poissonCharacteristicFunctionFormula
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_add]
  ring_nf

theorem independent_sum_has_poisson_characteristic_function
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} {lam mu : ℝ}
    (hXmeas : AEMeasurable X P) (hYmeas : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y)
    (hX : HasPoissonCharacteristicFunction P X lam)
    (hY : HasPoissonCharacteristicFunction P Y mu) :
    HasPoissonCharacteristicFunction P (fun ω => X ω + Y ω) (lam + mu) := by
  intro t
  rw [characteristicFunction_indep_add_eq_mul hXmeas hYmeas hXY t]
  rw [hX t, hY t]
  exact poissonCharacteristicFunctionFormula_mul lam mu t

theorem poisson_law_has_characteristic_function
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} {lam : NNReal}
    (hXmeas : AEMeasurable X P)
    (hXlaw : HasPoissonLaw P X lam) :
    HasPoissonCharacteristicFunction P X (lam : ℝ) := by
  intro t
  rw [characteristicFunction_law_eq_charFun hXmeas t, hXlaw,
    poissonRealMeasure_charFun]

theorem independent_sum_has_poisson_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} {lam mu : NNReal}
    (hXmeas : AEMeasurable X P) (hYmeas : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y)
    (hXlaw : HasPoissonLaw P X lam)
    (hYlaw : HasPoissonLaw P Y mu) :
    HasPoissonLaw P (fun ω => X ω + Y ω) (lam + mu) := by
  unfold HasPoissonLaw
  apply Measure.ext_of_charFun
  ext t
  calc
    charFun (P.map fun ω => X ω + Y ω) t
        = (charFun (P.map X) * charFun (P.map Y)) t := by
            rw [hXY.charFun_map_fun_add_eq_mul hXmeas hYmeas]
    _ = charFun (P.map X) t * charFun (P.map Y) t := rfl
    _ = charFun (poissonRealMeasure lam) t * charFun (poissonRealMeasure mu) t := by
            rw [hXlaw, hYlaw]
    _ = poissonCharacteristicFunctionFormula (lam : ℝ) t *
          poissonCharacteristicFunctionFormula (mu : ℝ) t := by
            rw [poissonRealMeasure_charFun, poissonRealMeasure_charFun]
    _ = poissonCharacteristicFunctionFormula ((lam + mu : NNReal) : ℝ) t := by
            simpa [NNReal.coe_add] using
              poissonCharacteristicFunctionFormula_mul (lam : ℝ) (mu : ℝ) t
    _ = charFun (poissonRealMeasure (lam + mu)) t := by
            rw [poissonRealMeasure_charFun]

noncomputable def poissonConvolutionPMFReal (lam mu : NNReal) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1),
    ProbabilityTheory.poissonPMFReal lam n *
      ProbabilityTheory.poissonPMFReal mu (k - n)

private lemma poisson_convolution_term_eq
    (lam mu : NNReal) {k n : ℕ} (hn : n ≤ k) :
    ((lam : ℝ) ^ n * Real.exp (-(lam : ℝ)) / n.factorial) *
        ((mu : ℝ) ^ (k - n) * Real.exp (-(mu : ℝ)) / (k - n).factorial) =
      Real.exp (-(lam : ℝ)) * Real.exp (-(mu : ℝ)) *
        ((lam : ℝ) ^ n * ((mu : ℝ) ^ (k - n) * (k.choose n : ℝ))) /
          k.factorial := by
  have hchoose_nat := Nat.choose_mul_factorial_mul_factorial hn
  have hchoose_real :
      (k.choose n : ℝ) * (n.factorial : ℝ) * ((k - n).factorial : ℝ) =
        (k.factorial : ℝ) := by
    exact_mod_cast hchoose_nat
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - n)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
  rw [← hchoose_real]
  ring

theorem poissonConvolutionPMFReal_eq_poissonPMFReal_add
    (lam mu : NNReal) (k : ℕ) :
    poissonConvolutionPMFReal lam mu k =
      ProbabilityTheory.poissonPMFReal (lam + mu) k := by
  unfold poissonConvolutionPMFReal
  calc
    ∑ n ∈ Finset.range (k + 1),
        ProbabilityTheory.poissonPMFReal lam n *
          ProbabilityTheory.poissonPMFReal mu (k - n)
        = ∑ n ∈ Finset.range (k + 1),
            Real.exp (-(lam : ℝ)) * Real.exp (-(mu : ℝ)) *
              ((lam : ℝ) ^ n * ((mu : ℝ) ^ (k - n) * (k.choose n : ℝ))) /
                k.factorial := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnle : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          simpa [ProbabilityTheory.poissonPMFReal, mul_assoc, mul_comm, mul_left_comm] using
            poisson_convolution_term_eq lam mu hnle
    _ = ProbabilityTheory.poissonPMFReal (lam + mu) k := by
          simp [ProbabilityTheory.poissonPMFReal, Real.exp_add, add_pow]
          rw [Finset.mul_sum]
          rw [← Finset.sum_div]
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          ring

theorem prob_9_2
    (lam mu : NNReal) :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
      {X Y : Ω → ℝ},
      AEMeasurable X P → AEMeasurable Y P → X ⟂ᵢ[P] Y →
      HasPoissonLaw P X lam → HasPoissonLaw P Y mu →
      HasPoissonLaw P (fun ω => X ω + Y ω) (lam + mu) := by
  intro Ω _ P _ X Y hXmeas hYmeas hXY hXlaw hYlaw
  exact independent_sum_has_poisson_law hXmeas hYmeas hXY hXlaw hYlaw
