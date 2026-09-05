/-
TASK ID: ex_12_1_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

open scoped ENNReal BigOperators

noncomputable section



abbrev ex_12_1_2_space := ℕ



def ex_12_1_2_weight (n : ex_12_1_2_space) : ENNReal :=
  (2⁻¹ : ENNReal) ^ (n + 1)

 
noncomputable def ex_12_1_2_realWeight (n : ex_12_1_2_space) : ℝ :=
  (ex_12_1_2_weight n).toReal

 
theorem ex_12_1_2_realWeight_eq (n : ex_12_1_2_space) :
    ex_12_1_2_realWeight n = (1 / (2 : ℝ) ^ (n + 1)) := by
  simp [ex_12_1_2_realWeight, ex_12_1_2_weight, one_div]



noncomputable def ex_12_1_2_measure : Measure ex_12_1_2_space :=
  Measure.sum fun n => ex_12_1_2_weight n • Measure.dirac n

theorem ex_12_1_2_weight_ne_top (n : ex_12_1_2_space) :
    ex_12_1_2_weight n ≠ ⊤ := by
  simp [ex_12_1_2_weight]



theorem ex_12_1_2_measure_univ :
    ex_12_1_2_measure Set.univ = 1 := by
  rw [ex_12_1_2_measure]
  simpa [ex_12_1_2_weight, Measure.sum_apply,
    ENNReal.tsum_geometric_add_one] using
    (ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
      (by simp : (2 : ENNReal) ≠ ⊤))



def ex_12_1_2_sequenceOfRandomVariable
    (X : ex_12_1_2_space → ℂ) : ℕ → ℂ :=
  X



def ex_12_1_2_randomVariableOfSequence
    (x : ℕ → ℂ) : ex_12_1_2_space → ℂ :=
  x

 
theorem ex_12_1_2_sequence_correspondence
    (X : ex_12_1_2_space → ℂ) :
    ex_12_1_2_randomVariableOfSequence
      (ex_12_1_2_sequenceOfRandomVariable X) = X :=
  rfl

 
def ex_12_1_2_L2Series (X : ex_12_1_2_space → ℂ) : Prop :=
  Summable fun n => ex_12_1_2_realWeight n * ‖X n‖ ^ 2



theorem ex_12_1_2_memLp_iff_series
    (X : ex_12_1_2_space → ℂ) :
    MemLp X (2 : ENNReal) ex_12_1_2_measure ↔
      ex_12_1_2_L2Series X := by
  have hX : AEStronglyMeasurable X ex_12_1_2_measure :=
    (measurable_of_countable X).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hX, ex_12_1_2_L2Series]
  have hfinite : ∀ n, ex_12_1_2_weight n ≠ ⊤ :=
    ex_12_1_2_weight_ne_top
  constructor
  · intro h
    have hs_abs : Summable fun n : ex_12_1_2_space =>
        (ex_12_1_2_weight n).toReal * |‖X n‖ ^ 2| := by
      exact (integrable_sum_dirac_iff
        (f := fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hfinite).mp
        (by simpa [ex_12_1_2_measure] using h)
    exact hs_abs.congr fun n => by
      simp [ex_12_1_2_realWeight, abs_of_nonneg (sq_nonneg (‖X n‖))]
  · intro h
    have hs_abs : Summable fun n : ex_12_1_2_space =>
        (ex_12_1_2_weight n).toReal * |‖X n‖ ^ 2| :=
      h.congr fun n => by
        simp [ex_12_1_2_realWeight, abs_of_nonneg (sq_nonneg (‖X n‖))]
    have hint : Integrable (fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (Measure.sum fun n => ex_12_1_2_weight n • Measure.dirac n) :=
      (integrable_sum_dirac_iff
        (f := fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hfinite).mpr hs_abs
    simpa [ex_12_1_2_measure] using hint

 
theorem ex_12_1_2_star_memLp
    {X : ex_12_1_2_space → ℂ}
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure) :
    MemLp (fun n => star (X n)) (2 : ENNReal) ex_12_1_2_measure := by
  refine hX.of_le_mul (c := 1)
    ((measurable_of_countable fun n : ex_12_1_2_space => star (X n)).aestronglyMeasurable)
    ?_
  filter_upwards with n
  simp [norm_star]



theorem ex_12_1_2_inner_integrable_of_memLp
    {X Y : ex_12_1_2_space → ℂ}
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    Integrable (fun n => star (X n) * Y n) ex_12_1_2_measure := by
  have hstar : MemLp (fun n => star (X n)) (2 : ENNReal)
      ex_12_1_2_measure :=
    ex_12_1_2_star_memLp hX
  change Integrable ((fun n => star (X n)) * Y) ex_12_1_2_measure
  exact hstar.integrable_mul hY



theorem ex_12_1_2_inner_formula
    (X Y : ex_12_1_2_space → ℂ)
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    complexL2Inner ex_12_1_2_measure X Y hX hY =
      ∑' n : ex_12_1_2_space,
        ex_12_1_2_realWeight n • (star (X n) * Y n) := by
  have hXY : Integrable (fun n => star (X n) * Y n) ex_12_1_2_measure :=
    ex_12_1_2_inner_integrable_of_memLp hX hY
  have hfinite : ∀ n, ex_12_1_2_weight n ≠ ⊤ :=
    ex_12_1_2_weight_ne_top
  have hs : Summable fun n : ex_12_1_2_space =>
      (ex_12_1_2_weight n).toReal *
        ‖star (X n) * Y n‖ := by
    simpa [ex_12_1_2_measure] using
      (Integrable.summable_of_dirac
        (f := fun n : ex_12_1_2_space => star (X n) * Y n)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hXY)
  rw [complexL2Inner, ex_12_1_2_measure]
  simpa [ex_12_1_2_realWeight] using
    (integral_sum_dirac_eq_tsum
      (f := fun n : ex_12_1_2_space => star (X n) * Y n)
      (x := fun n : ex_12_1_2_space => n)
      (c := ex_12_1_2_weight) hfinite hs)



theorem ex_12_1_2 (X Y : ex_12_1_2_space → ℂ)
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    ex_12_1_2_measure Set.univ = 1 ∧
      (MemLp X (2 : ENNReal) ex_12_1_2_measure ↔
        ex_12_1_2_L2Series X) ∧
      complexL2Inner ex_12_1_2_measure X Y hX hY =
        ∑' n : ex_12_1_2_space,
          ex_12_1_2_realWeight n • (star (X n) * Y n) := by
  exact ⟨ex_12_1_2_measure_univ,
    ex_12_1_2_memLp_iff_series X,
    ex_12_1_2_inner_formula X Y hX hY⟩
