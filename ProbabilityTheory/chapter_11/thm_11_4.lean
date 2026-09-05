/-
TASK ID: thm_11_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-weak-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_07.def_7_3
import ProbabilityTheory.chapter_09.def_9_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

private theorem thm_11_4_sum_measurable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => ∑ i, X i ω) :=
  Finset.measurable_sum Finset.univ (fun i _hi => hX i)

private theorem thm_11_4_sum_memLp {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => ∑ i, X i ω) 2 P := by
  simpa using
    (memLp_finset_sum (Finset.univ : Finset ι) (fun i _hi => hX i))



theorem thm_11_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) 2 P)
    (huncorr : Pairwise fun i j => Uncorrelated P (X i) (X j)) :
    _root_.variance P (fun ω => ∑ i, X i ω)
        (FiniteAbsMoment.of_memLp
          (thm_11_4_sum_measurable X hXm) (thm_11_4_sum_memLp P X hX)) =
      ∑ i, _root_.variance P (X i) (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := by
  classical
  have hsum_mem : MemLp (fun ω => ∑ i, X i ω) 2 P :=
    thm_11_4_sum_memLp P X hX
  have hsum_variance :
      _root_.variance P (fun ω => ∑ i, X i ω)
          (FiniteAbsMoment.of_memLp
            (thm_11_4_sum_measurable X hXm) hsum_mem) =
        Var[fun ω => ∑ i, X i ω; P] := by
    rw [_root_.variance, rthCentralMoment]
    exact ProbabilityTheory.centralMoment_two_eq_variance
      (μ := P) (X := fun ω => ∑ i, X i ω) hsum_mem.aemeasurable
  have hdiag :
      ∀ i, cov[X i, X i; P] =
        _root_.variance P (X i) (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := by
    intro i
    calc
      cov[X i, X i; P] = Var[X i; P] := by
        exact ProbabilityTheory.covariance_self (μ := P) (X := X i) (hX i).aemeasurable
      _ = _root_.variance P (X i)
          (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := by
        symm
        rw [_root_.variance, rthCentralMoment]
        exact ProbabilityTheory.centralMoment_two_eq_variance
          (μ := P) (X := X i) (hX i).aemeasurable
  have hoffdiag : ∀ i j, i ≠ j → cov[X i, X j; P] = 0 := by
    intro i j hij
    have hcov :
        Covariance P (X i) (X j) = 0 :=
      (covariance_zero_iff_uncorrelated
        (μ := P) (X := X i) (Y := X j) (hX i) (hX j)).2 (huncorr hij)
    simpa [Covariance] using hcov
  have hrow :
      ∀ i, (∑ j, cov[X i, X j; P]) =
        _root_.variance P (X i) (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := by
    intro i
    calc
      (∑ j, cov[X i, X j; P]) = cov[X i, X i; P] := by
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _hj hji
          exact hoffdiag i j hji.symm
        · intro hi
          simp at hi
      _ = _root_.variance P (X i)
          (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := hdiag i
  calc
    _root_.variance P (fun ω => ∑ i, X i ω)
        (FiniteAbsMoment.of_memLp
          (thm_11_4_sum_measurable X hXm) (thm_11_4_sum_memLp P X hX))
        = Var[fun ω => ∑ i, X i ω; P] := hsum_variance
    _ = ∑ i, ∑ j, cov[X i, X j; P] := by
      exact ProbabilityTheory.variance_fun_sum (μ := P) (X := X) hX
    _ = ∑ i, _root_.variance P (X i)
        (FiniteAbsMoment.of_memLp (hXm i) (hX i)) := by
      exact Finset.sum_congr rfl fun i _hi => hrow i
