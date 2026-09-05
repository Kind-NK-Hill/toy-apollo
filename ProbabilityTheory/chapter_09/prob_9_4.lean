/-
TASK ID: prob_9_4
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3
import ProbabilityTheory.chapter_09.thm_9_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem characteristicFunction_affine
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X P) (a b t : ℝ) :
    characteristicFunction (P.map (fun ω => a * X ω + b)) t =
      characteristicFunction (P.map X) (a * t) *
        Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) := by
  have hAffine : AEMeasurable (fun ω => a * X ω + b) P := by
    fun_prop
  rw [characteristicFunction_map_apply hAffine,
    characteristicFunction_map_apply hX]
  calc
    ∫ ω, Complex.exp (Complex.I * (↑(a * X ω + b) : ℂ) * (t : ℂ)) ∂P
        = ∫ ω,
            Complex.exp (Complex.I * (X ω : ℂ) * (↑(a * t) : ℂ)) *
              Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) ∂P := by
          congr with ω
          rw [← Complex.exp_add]
          congr 1
          norm_num [Complex.ofReal_add, Complex.ofReal_mul]
          ring
    _ = (∫ ω, Complex.exp (Complex.I * (X ω : ℂ) * (↑(a * t) : ℂ)) ∂P) *
          Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) := by
          exact integral_mul_const
            (μ := P)
            (r := Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)))
            (f := fun ω =>
              Complex.exp (Complex.I * (X ω : ℂ) * (↑(a * t) : ℂ)))

theorem prob_9_4
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X P) (a b t : ℝ) :
    characteristicFunction (P.map (fun ω => a * X ω + b)) t =
      characteristicFunction (P.map X) (a * t) *
        Complex.exp (Complex.I * (b : ℂ) * (t : ℂ)) :=
  characteristicFunction_affine P X hX a b t
