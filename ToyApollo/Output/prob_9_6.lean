/-
TASK ID: prob_9_6
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_6
import ToyApollo.Output.thm_9_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

noncomputable def cauchyCharFun (a γ t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (a : ℂ) * (t : ℂ) - ((γ * |t| : ℝ) : ℂ))

def HasCauchyDistribution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (a γ : ℝ) : Prop :=
  AEMeasurable X P ∧
    0 < γ ∧
    ∀ t : ℝ, characteristicFunction (P.map X) t = cauchyCharFun a γ t

noncomputable def cauchySampleAverage {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ((n : ℝ)⁻¹) * ∑ i : Fin n, X i ω

theorem cauchySampleAverage_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i : Fin n, AEMeasurable (X i) P) :
    AEMeasurable (cauchySampleAverage X) P := by
  unfold cauchySampleAverage
  fun_prop

theorem cauchyCharFun_average_scale
    {n : ℕ} (hn : 0 < n) (a γ t : ℝ) :
    (∏ _i : Fin n, cauchyCharFun a γ (((n : ℝ)⁻¹) * t)) =
      cauchyCharFun a γ t := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |(n : ℝ)⁻¹ * t| = |t| / (n : ℝ) := by
    rw [abs_mul, abs_inv, abs_of_pos hnRpos]
    field_simp [hnR]
  simp [cauchyCharFun, habs]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp [hnC]

theorem cauchySampleAverage_characteristicFunction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {a γ : ℝ}
    (hX : ∀ i : Fin n, HasCauchyDistribution P (X i) a γ)
    (hindep : iIndepFun X P) :
    ∀ t : ℝ,
      characteristicFunction (P.map (cauchySampleAverage X)) t =
        cauchyCharFun a γ t := by
  intro t
  have hAEM : ∀ i : Fin n, AEMeasurable (X i) P := fun i => (hX i).1
  have hsumAEM :
      AEMeasurable (fun ω => ∑ i : Fin n, X i ω) P := by
    fun_prop
  have havgAEM : AEMeasurable (cauchySampleAverage X) P :=
    cauchySampleAverage_aemeasurable hAEM
  calc
    characteristicFunction (P.map (cauchySampleAverage X)) t =
        charFun (P.map (cauchySampleAverage X)) t := by
          exact characteristicFunction_eq_charFun_map havgAEM t
    _ = charFun (P.map (fun ω => ∑ i : Fin n, X i ω)) (((n : ℝ)⁻¹) * t) := by
          change
            charFun (P.map (fun ω => ((n : ℝ)⁻¹) * ∑ i : Fin n, X i ω)) t =
              charFun (P.map (fun ω => ∑ i : Fin n, X i ω)) (((n : ℝ)⁻¹) * t)
          exact charFun_map_mul_comp
            (μ := P)
            (f := fun ω => ∑ i : Fin n, X i ω)
            hsumAEM ((n : ℝ)⁻¹) t
    _ = (∏ i : Fin n, charFun (P.map (X i)) (((n : ℝ)⁻¹) * t)) := by
          have hprod :=
            hindep.charFun_map_fun_sum_eq_prod hAEM
              (E := ℝ)
          simpa [Finset.prod_apply] using
            congrFun hprod (((n : ℝ)⁻¹) * t)
    _ = (∏ _i : Fin n, cauchyCharFun a γ (((n : ℝ)⁻¹) * t)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [← characteristicFunction_eq_charFun_map (P := P) (X := X i)
            (hX i).1 (((n : ℝ)⁻¹) * t)]
          exact (hX i).2.2 (((n : ℝ)⁻¹) * t)
    _ = cauchyCharFun a γ t :=
          cauchyCharFun_average_scale hn a γ t

theorem prob_9_6
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {a γ : ℝ}
    (hX : ∀ i : Fin n, HasCauchyDistribution P (X i) a γ)
    (hindep : iIndepFun X P) :
    SameDistribution P (cauchySampleAverage X) (X ⟨0, hn⟩) := by
  have havgAEM : AEMeasurable (cauchySampleAverage X) P :=
    cauchySampleAverage_aemeasurable (fun i => (hX i).1)
  exact thm_9_6 havgAEM (hX ⟨0, hn⟩).1
    (fun t => by
      rw [cauchySampleAverage_characteristicFunction hn hX hindep t]
      exact ((hX ⟨0, hn⟩).2.2 t).symm)
