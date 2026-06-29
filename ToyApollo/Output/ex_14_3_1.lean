/-
TASK ID: ex_14_3_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-prokhorov-sequential-compactness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_14_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

def ex_14_3_1_pn (lam : ℝ) (n : ℕ) : ℝ :=
  lam / (n + 1 : ℝ)

def ex_14_3_1_binomialCharacteristic
    (lam : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (1 + ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1)) /
      ((n : ℂ) + 1)) ^ (n + 1)

theorem ex_14_3_1_binomialCharacteristic_source_form
    (lam : ℝ) (n : ℕ) (t : ℝ) :
    ex_14_3_1_binomialCharacteristic lam n t =
      (1 - ((lam : ℂ) / ((n : ℂ) + 1)) *
          (1 - Complex.exp (Complex.I * (t : ℂ)))) ^ (n + 1) := by
  unfold ex_14_3_1_binomialCharacteristic
  congr 1
  ring

def ex_14_3_1_poissonCharacteristic (lam : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1))

theorem ex_14_3_1_binomialCharacteristic_tendsto
    (lam : ℝ) (t : ℝ) :
    Tendsto (fun n : ℕ => ex_14_3_1_binomialCharacteristic lam n t)
      atTop (𝓝 (ex_14_3_1_poissonCharacteristic lam t)) := by
  let z : ℂ := (lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1)
  have h :=
    (Complex.tendsto_one_add_div_pow_exp z).comp
      (tendsto_add_atTop_nat 1)
  change
    Tendsto (fun n : ℕ => (1 + z / ((n : ℂ) + 1)) ^ (n + 1))
      atTop (𝓝 (Complex.exp z))
  refine h.congr' ?_
  filter_upwards with n
  simp [Nat.cast_add, Nat.cast_one]

structure ex_14_3_1_BinomialPoissonSetup (lam : ℝ) where
  positive_lambda : 0 < lam
  binomialLaws : ℕ → ProbabilityMeasure ℝ
  poissonLaw : ProbabilityMeasure ℝ
  binomial_characteristic :
    ∀ n : ℕ, ∀ t : ℝ,
      thm_14_1_characteristicFunction (binomialLaws n) t =
        ex_14_3_1_binomialCharacteristic lam n t
  poisson_characteristic :
    ∀ t : ℝ,
      thm_14_1_characteristicFunction poissonLaw t =
        ex_14_3_1_poissonCharacteristic lam t

theorem ex_14_3_1_pointwiseCharacteristicConvergence
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    thm_14_1_pointwiseCharFunConvergence S.binomialLaws
      (fun t : ℝ => thm_14_1_characteristicFunction S.poissonLaw t) := by
  intro t
  have hlimit := ex_14_3_1_binomialCharacteristic_tendsto lam t
  have hleft :
      (fun n : ℕ =>
        thm_14_1_characteristicFunction (S.binomialLaws n) t) =
        fun n : ℕ => ex_14_3_1_binomialCharacteristic lam n t := by
    funext n
    simpa using S.binomial_characteristic n t
  have hright :
      ex_14_3_1_poissonCharacteristic lam t =
        thm_14_1_characteristicFunction S.poissonLaw t :=
    (S.poisson_characteristic t).symm
  simpa [hleft, hright] using hlimit

theorem ex_14_3_1_converges_to_poisson
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    Tendsto S.binomialLaws atTop (𝓝 S.poissonLaw) := by
  have hchar := ex_14_3_1_pointwiseCharacteristicConvergence S
  exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2 (fun t : ℝ => by
    simpa [thm_14_1_characteristicFunction] using hchar t)

theorem ex_14_3_1_weakLimit_by_Levy
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    thm_14_1_weakLimit S.binomialLaws := by
  have hchar := ex_14_3_1_pointwiseCharacteristicConvergence S
  exact (thm_14_1_weak_iff_characteristic hchar).2
    ⟨S.poissonLaw, fun _ => rfl⟩

theorem ex_14_3_1
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    Tendsto S.binomialLaws atTop (𝓝 S.poissonLaw) :=
  ex_14_3_1_converges_to_poisson S
