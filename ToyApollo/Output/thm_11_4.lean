import Mathlib
import ToyApollo.Output.def_7_3
import ToyApollo.Output.def_9_1

/-
TASK ID: thm_11_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-weak-law-large-numbers
TASK CONTENT:
\begin{thmbox}{11.4}
\end{thmbox}

IfX1,X 2,...,X n are pairwise uncorrelated, then

Va r(X1 + X2 +\cdot\cdot\cdot+ Xn) =

n\sum

i=1

Va r(Xi).

\textit{Proof} Without loss of generality, suppose the random variables X1,...,X n have

zero mean. (We can consider the centered random variable Yn = Xn - E[Xn]

otherwise.)

Using the definition of variance and the linearity of expectation, we have

Va r(X1 + X2 +\cdot\cdot\cdot+ Xn) = E

[

X2

1 + X2

2 +\cdot\cdot\cdot+ X2

n + 2

\sum

i<j

XiXj

]

=

n\sum

i=1

E[X2

i ].

The assumption of pairwise uncorrelatedness guarantees that the cross-terms

E[XiXj ] are zero for i /=j Therefore, we have

Va r(X1 + X2 +\cdot\cdot\cdot+ Xn) =

n\sum

i=1

E[X2

i ]=

n\sum

i=1

Va r(Xi).

\hfill $\square$

We will present two versions of weak law of large numbers. The first one

assumes that the random variables are pairwise uncorrelated with the same mean

and variance. Note that the random variables need not be identically distributed, and

they need not be independent.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

/--
Theorem 11.4: the variance of a finite sum of pairwise uncorrelated random
variables is the sum of their variances.

The textbook proof expands the square of the centered sum.  In Mathlib this
expansion is packaged as `variance_fun_sum`, which gives a double sum of
covariances; Definition 7.3 then turns pairwise uncorrelatedness into vanishing
off-diagonal covariance terms.
-/
theorem thm_11_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P)
    (huncorr : Pairwise fun i j => Uncorrelated P (X i) (X j)) :
    _root_.variance P (fun ω => ∑ i, X i ω) =
      ∑ i, _root_.variance P (X i) := by
  classical
  have hsum_mem : MemLp (fun ω => ∑ i, X i ω) 2 P := by
    simpa using
      (memLp_finset_sum (Finset.univ : Finset ι) (fun i _hi => hX i))
  have hsum_variance :
      _root_.variance P (fun ω => ∑ i, X i ω) =
        Var[fun ω => ∑ i, X i ω; P] := by
    rw [_root_.variance, rthCentralMoment]
    exact ProbabilityTheory.centralMoment_two_eq_variance
      (μ := P) (X := fun ω => ∑ i, X i ω) hsum_mem.aemeasurable
  have hdiag : ∀ i, cov[X i, X i; P] = _root_.variance P (X i) := by
    intro i
    calc
      cov[X i, X i; P] = Var[X i; P] := by
        exact ProbabilityTheory.covariance_self (μ := P) (X := X i) (hX i).aemeasurable
      _ = _root_.variance P (X i) := by
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
  have hrow : ∀ i, (∑ j, cov[X i, X j; P]) = _root_.variance P (X i) := by
    intro i
    calc
      (∑ j, cov[X i, X j; P]) = cov[X i, X i; P] := by
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _hj hji
          exact hoffdiag i j hji.symm
        · intro hi
          simp at hi
      _ = _root_.variance P (X i) := hdiag i
  calc
    _root_.variance P (fun ω => ∑ i, X i ω)
        = Var[fun ω => ∑ i, X i ω; P] := hsum_variance
    _ = ∑ i, ∑ j, cov[X i, X j; P] := by
      exact ProbabilityTheory.variance_fun_sum (μ := P) (X := X) hX
    _ = ∑ i, _root_.variance P (X i) := by
      exact Finset.sum_congr rfl fun i _hi => hrow i
