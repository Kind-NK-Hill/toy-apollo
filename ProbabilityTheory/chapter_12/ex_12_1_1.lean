/-
TASK ID: ex_12_1_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



abbrev ex_12_1_1_space := Fin 3

 
abbrev ex_12_1_1_a : ex_12_1_1_space := ⟨0, by decide⟩

 
abbrev ex_12_1_1_b : ex_12_1_1_space := ⟨1, by decide⟩

 
abbrev ex_12_1_1_c : ex_12_1_1_space := ⟨2, by decide⟩

 
def ex_12_1_1_weight (pa pb pc : NNReal) : ex_12_1_1_space → ENNReal
  | 0 => (pa : ENNReal)
  | 1 => (pb : ENNReal)
  | 2 => (pc : ENNReal)



noncomputable def ex_12_1_1_measure (pa pb pc : NNReal) :
    Measure ex_12_1_1_space :=
  Measure.sum fun i => ex_12_1_1_weight pa pb pc i • Measure.dirac i

 
theorem ex_12_1_1_measure_univ (pa pb pc : NNReal) :
    ex_12_1_1_measure pa pb pc Set.univ =
      (pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal) := by
  rw [ex_12_1_1_measure, Measure.sum_apply _ MeasurableSet.univ]
  simp [ex_12_1_1_weight, Fin.sum_univ_three,
    ENNReal.smul_def, add_assoc]

 
theorem ex_12_1_1_measure_univ_of_sum_one {pa pb pc : NNReal}
    (hsum : pa + pb + pc = 1) :
    ex_12_1_1_measure pa pb pc Set.univ = 1 := by
  have hsum' : ((pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal)) = 1 := by
    exact_mod_cast hsum
  simpa [ex_12_1_1_measure_univ] using hsum'



def ex_12_1_1_randomVariableOfVector (x : Fin 3 → ℝ) :
    ex_12_1_1_space → ℝ :=
  x



theorem ex_12_1_1_vector_correspondence (X : ex_12_1_1_space → ℝ) :
    ex_12_1_1_randomVariableOfVector (fun i => X i) = X :=
  rfl

 
theorem ex_12_1_1_inner_formula (pa pb pc : NNReal)
    (X Y : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X)
    (hY : L2Function (ex_12_1_1_measure pa pb pc) Y) :
    l2Inner (ex_12_1_1_measure pa pb pc) X Y hX hY =
      (pa : ℝ) * X ex_12_1_1_a * Y ex_12_1_1_a +
        (pb : ℝ) * X ex_12_1_1_b * Y ex_12_1_1_b +
          (pc : ℝ) * X ex_12_1_1_c * Y ex_12_1_1_c := by
  rw [l2Inner, ex_12_1_1_measure]
  have hfinite : ∀ i, ex_12_1_1_weight pa pb pc i ≠ ⊤ := by
    intro i
    fin_cases i <;> simp [ex_12_1_1_weight]
  rw [integral_sum_dirac (x := fun i : ex_12_1_1_space => i)
    (c := ex_12_1_1_weight pa pb pc) hfinite]
  simp [ex_12_1_1_weight, ex_12_1_1_a, ex_12_1_1_b, ex_12_1_1_c,
    Fin.sum_univ_three, mul_assoc, add_assoc]

 
theorem ex_12_1_1_second_moment_formula (pa pb pc : NNReal)
    (X : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X) :
    l2Inner (ex_12_1_1_measure pa pb pc) X X hX hX =
      (pa : ℝ) * (X ex_12_1_1_a) ^ 2 +
        (pb : ℝ) * (X ex_12_1_1_b) ^ 2 +
          (pc : ℝ) * (X ex_12_1_1_c) ^ 2 := by
  simpa [pow_two, mul_assoc] using
    ex_12_1_1_inner_formula pa pb pc X X hX hX



theorem ex_12_1_1 (pa pb pc : NNReal) (X Y : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X)
    (hY : L2Function (ex_12_1_1_measure pa pb pc) Y) :
    ex_12_1_1_measure pa pb pc Set.univ =
      (pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal) ∧
      l2Inner (ex_12_1_1_measure pa pb pc) X Y hX hY =
        (pa : ℝ) * X ex_12_1_1_a * Y ex_12_1_1_a +
          (pb : ℝ) * X ex_12_1_1_b * Y ex_12_1_1_b +
            (pc : ℝ) * X ex_12_1_1_c * Y ex_12_1_1_c ∧
        l2Inner (ex_12_1_1_measure pa pb pc) X X hX hX =
          (pa : ℝ) * (X ex_12_1_1_a) ^ 2 +
            (pb : ℝ) * (X ex_12_1_1_b) ^ 2 +
              (pc : ℝ) * (X ex_12_1_1_c) ^ 2 := by
  exact ⟨ex_12_1_1_measure_univ pa pb pc,
    ex_12_1_1_inner_formula pa pb pc X Y hX hY,
    ex_12_1_1_second_moment_formula pa pb pc X hX⟩
