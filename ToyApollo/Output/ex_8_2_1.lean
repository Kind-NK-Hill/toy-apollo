/-
TASK ID: ex_8_2_1
TYPE: Example_Proof
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_8_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Ex821Support

noncomputable def poissonMeasureOnReal (r : NNReal) : Measure ℝ :=
  (poissonMeasure r).map (fun n : ℕ => (n : ℝ))

instance instIsProbabilityMeasurePoissonMeasureOnReal (r : NNReal) :
    IsProbabilityMeasure (poissonMeasureOnReal r) := by
  unfold poissonMeasureOnReal
  exact Measure.isProbabilityMeasure_map Nat.cast_continuous.measurable.aemeasurable

def nonnegativeIntegerReals : Set ℝ :=
  Set.range (fun n : ℕ => (n : ℝ))

theorem measurableSet_nonnegativeIntegerReals :
    MeasurableSet nonnegativeIntegerReals := by
  exact (Set.countable_range (fun n : ℕ => (n : ℝ))).measurableSet

theorem poissonMeasureOnReal_singleton (r : NNReal) (n : ℕ) :
    poissonMeasureOnReal r ({(n : ℝ)} : Set ℝ) =
      ENNReal.ofReal
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) := by
  rw [poissonMeasureOnReal, Measure.map_apply Nat.cast_continuous.measurable
    (measurableSet_singleton (n : ℝ))]
  have hpreimage :
      (fun k : ℕ => (k : ℝ)) ⁻¹' ({(n : ℝ)} : Set ℝ) = ({n} : Set ℕ) := by
    ext k
    simp
  rw [hpreimage, poissonMeasure_singleton]

theorem poissonMeasureOnReal_concentrated (r : NNReal) :
    poissonMeasureOnReal r nonnegativeIntegerRealsᶜ = 0 := by
  rw [poissonMeasureOnReal, Measure.map_apply Nat.cast_continuous.measurable
    measurableSet_nonnegativeIntegerReals.compl]
  simp [nonnegativeIntegerReals]

theorem realProdMeasurableSpace_eq_borel :
    (inferInstance : MeasurableSpace (ℝ × ℝ)) = borel (ℝ × ℝ) :=
  BorelSpace.measurable_eq

noncomputable def poissonGaussianProductMeasure (r : NNReal) : Measure (ℝ × ℝ) :=
  (thm_8_2 (poissonMeasureOnReal r)
    (gaussianReal (0 : ℝ) (1 : NNReal))).choose

theorem poissonGaussianProductMeasure_rectangle
    (r : NNReal) (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    poissonGaussianProductMeasure r (s ×ˢ t) =
      poissonMeasureOnReal r s * gaussianReal (0 : ℝ) (1 : NNReal) t := by
  exact (thm_8_2 (poissonMeasureOnReal r)
    (gaussianReal (0 : ℝ) (1 : NNReal))).choose_spec.1 s t hs ht

theorem poissonGaussianProductMeasure_unique
    (r : NNReal) (R : Measure (ℝ × ℝ))
    (hR : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      R (s ×ˢ t) =
        poissonMeasureOnReal r s * gaussianReal (0 : ℝ) (1 : NNReal) t) :
    R = poissonGaussianProductMeasure r := by
  exact (thm_8_2 (poissonMeasureOnReal r)
    (gaussianReal (0 : ℝ) (1 : NNReal))).choose_spec.2 R hR

instance instIsProbabilityMeasurePoissonGaussianProductMeasure (r : NNReal) :
    IsProbabilityMeasure (poissonGaussianProductMeasure r) where
  measure_univ := by
    calc
      poissonGaussianProductMeasure r Set.univ =
          poissonGaussianProductMeasure r
            ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)) := by
        rw [Set.univ_prod_univ]
      _ = poissonMeasureOnReal r Set.univ *
          gaussianReal (0 : ℝ) (1 : NNReal) Set.univ :=
        poissonGaussianProductMeasure_rectangle r Set.univ Set.univ
          MeasurableSet.univ MeasurableSet.univ
      _ = 1 := by simp

theorem poissonGaussianProductMeasure_concentrated (r : NNReal) :
    poissonGaussianProductMeasure r
      (nonnegativeIntegerReals ×ˢ (Set.univ : Set ℝ))ᶜ = 0 := by
  have hstrip :
      poissonGaussianProductMeasure r
        (nonnegativeIntegerReals ×ˢ (Set.univ : Set ℝ)) = 1 := by
    rw [poissonGaussianProductMeasure_rectangle r nonnegativeIntegerReals Set.univ
      measurableSet_nonnegativeIntegerReals MeasurableSet.univ]
    rw [measure_of_measure_compl_eq_zero (poissonMeasureOnReal_concentrated r)]
    simp
  calc
    poissonGaussianProductMeasure r
          (nonnegativeIntegerReals ×ˢ (Set.univ : Set ℝ))ᶜ =
        poissonGaussianProductMeasure r Set.univ -
          poissonGaussianProductMeasure r
            (nonnegativeIntegerReals ×ˢ (Set.univ : Set ℝ)) :=
      measure_compl
        (measurableSet_nonnegativeIntegerReals.prod MeasurableSet.univ)
        (by rw [hstrip]; norm_num)
    _ = 0 := by simp [hstrip]

theorem poissonGaussianProductMeasure_Icc
    (r : NNReal) (n : ℕ) (a b : ℝ) :
    poissonGaussianProductMeasure r
        ({(n : ℝ)} ×ˢ Set.Icc a b) =
      ENNReal.ofReal
        ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) *
          ∫ x in Set.Icc a b,
            gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := by
  rw [poissonGaussianProductMeasure_rectangle r {(n : ℝ)} (Set.Icc a b)
    (measurableSet_singleton (n : ℝ)) measurableSet_Icc]
  rw [poissonMeasureOnReal_singleton]
  rw [gaussianReal_apply_eq_integral (0 : ℝ) (by norm_num) (Set.Icc a b)]
  rw [← ENNReal.ofReal_mul (by positivity)]

end Ex821Support

theorem ex_8_2_1 (r : NNReal) (n : ℕ) (a b : ℝ)
    (_hn : 0 < n) (_hab : a < b) :
    Ex821Support.poissonGaussianProductMeasure r
        ({(n : ℝ)} ×ˢ Set.Icc a b) =
      ENNReal.ofReal
        ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) *
          ∫ x in Set.Icc a b,
            gaussianPDFReal (0 : ℝ) (1 : NNReal) x) :=
  Ex821Support.poissonGaussianProductMeasure_Icc r n a b
