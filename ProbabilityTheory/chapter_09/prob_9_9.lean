/-
TASK ID: prob_9_9
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3
import ProbabilityTheory.chapter_09.thm_9_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ComplexOrder ComplexConjugate

noncomputable def characteristicFunctionGramMatrix
    {n : Type*} (μ : Measure ℝ) (t : n → ℝ) : Matrix n n ℂ :=
  fun i j => charFun μ (t j - t i)

noncomputable def characteristicFunctionGramFeatureLp
    (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) : ℝ →₂[μ] ℂ :=
  (MemLp.of_bound (p := (2 : ENNReal))
    (f := fun x : ℝ => Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
    (by fun_prop)
    (1 : ℝ)
    (ae_of_all μ fun x => by
      rw [Complex.norm_exp_ofReal_mul_I])).toLp _

theorem characteristicFunctionGramFeatureLp_ae_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    (characteristicFunctionGramFeatureLp μ s : ℝ → ℂ) =ᵐ[μ]
      fun x : ℝ => Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
  unfold characteristicFunctionGramFeatureLp
  exact MemLp.coeFn_toLp _

theorem characteristicFunctionGramFeatureLp_inner
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    inner ℂ (characteristicFunctionGramFeatureLp μ a)
        (characteristicFunctionGramFeatureLp μ b) =
      charFun μ (b - a) := by
  rw [L2.inner_def, charFun_apply_real]
  apply integral_congr_ae
  filter_upwards
    [characteristicFunctionGramFeatureLp_ae_eq μ a,
      characteristicFunctionGramFeatureLp_ae_eq μ b] with x hxa hxb
  rw [hxa, hxb]
  rw [RCLike.inner_apply]
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  simp
  ring

theorem characteristicFunctionGramMatrix_eq_gram
    {n : Type*} [Fintype n] (μ : Measure ℝ) [IsFiniteMeasure μ] (t : n → ℝ) :
    characteristicFunctionGramMatrix μ t =
      Matrix.gram ℂ (fun i => characteristicFunctionGramFeatureLp μ (t i)) := by
  ext i j
  simp [characteristicFunctionGramMatrix, Matrix.gram,
    characteristicFunctionGramFeatureLp_inner]

theorem characteristicFunctionGramMatrix_isHermitian
    {n : Type*} [Fintype n] (μ : Measure ℝ) [IsFiniteMeasure μ] (t : n → ℝ) :
    (characteristicFunctionGramMatrix μ t).IsHermitian := by
  rw [characteristicFunctionGramMatrix_eq_gram μ t]
  exact Matrix.isHermitian_gram ℂ (fun i => characteristicFunctionGramFeatureLp μ (t i))

theorem characteristicFunctionGramMatrix_posSemidef
    {n : Type*} [Fintype n] (μ : Measure ℝ) [IsFiniteMeasure μ] (t : n → ℝ) :
    (characteristicFunctionGramMatrix μ t).PosSemidef := by
  rw [characteristicFunctionGramMatrix_eq_gram μ t]
  exact Matrix.posSemidef_gram ℂ
    (fun i => characteristicFunctionGramFeatureLp μ (t i))

theorem characteristicFunctionGramMatrix_quadraticForm_nonneg
    {n : Type*} [Fintype n] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t : n → ℝ) (v : n → ℂ) :
    0 ≤ (dotProduct (star v)
      (Matrix.mulVec (characteristicFunctionGramMatrix μ t) v)).re := by
  simpa [dotProduct, Matrix.mulVec] using
    (characteristicFunctionGramMatrix_posSemidef μ t).re_dotProduct_nonneg v

theorem prob_9_9
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (_hX : AEMeasurable X P)
    {n : Type*} [Fintype n] (t : n → ℝ) :
    (characteristicFunctionGramMatrix (P.map X) t).IsHermitian ∧
      (characteristicFunctionGramMatrix (P.map X) t).PosSemidef ∧
        ∀ v : n → ℂ,
          0 ≤ (dotProduct (star v)
            (Matrix.mulVec
              (characteristicFunctionGramMatrix (P.map X) t) v)).re := by
  have hpsd := characteristicFunctionGramMatrix_posSemidef (P.map X) t
  exact ⟨hpsd.isHermitian, hpsd,
    fun v => by
      simpa [dotProduct, Matrix.mulVec] using hpsd.re_dotProduct_nonneg v⟩
