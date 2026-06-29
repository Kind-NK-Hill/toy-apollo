import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_10_2
import ToyApollo.Output.thm_11_5
import ToyApollo.Output.thm_2_2

/-
TASK ID: thm_11_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter11-weak-law-large-numbers
TASK CONTENT:
\begin{thmbox}{11.6 (Weak Law of Large Numbers (L1 Version))}
\end{thmbox}

Suppose .(Xi)\infty

i=1 is a sequence of iid. random variables with finite mean \mu.

ThenSn/n

P

-\to \mu .

Theorem 11.5, also known as Khinchin's weak law of large numbers, has a

detailed proof in [4, Theorem 2.2.14]In the following two sections, we will discuss

two applications of this theorem instead of going through the proof.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

/--
Theorem 11.6, the finite-mean iid weak law of large numbers.

The formal sample average reuses `thm_11_5_sampleMean`, so the L1 statement and
the preceding L2 theorem expose the same average interface.  The textbook cites
the detailed proof externally; here the proof lands through Mathlib's stronger
almost-sure strong law and the local Chapter 10 bridge from almost-sure
convergence to convergence in probability.
-/
theorem thm_11_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (m : ℝ)
    (hInt : Integrable (X 0) P)
    (hindep : def_5_10_randomVariables P X)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : P[X 0] = m) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
  have hindep' : iIndepFun X P := by
    simpa [def_5_10_randomVariables] using hindep
  have hpairwise : Pairwise fun i j => X i ⟂ᵢ[P] X j := by
    intro i j hij
    exact hindep'.indepFun hij
  have hInt_all : ∀ i, Integrable (X i) P := fun i =>
    (hident i).integrable_iff.2 hInt
  have hAvg_meas : ∀ n, AEStronglyMeasurable (thm_11_5_sampleMean X n) P := by
    intro n
    change AEStronglyMeasurable
      (fun ω => (1 / ((n : ℝ) + 1)) * (∑ i : Fin (n + 1), X i.1 ω)) P
    simpa using
      (MeasureTheory.AEStronglyMeasurable.const_mul
        (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin (n + 1)))
          (fun i _hi => (hInt_all i.1).aestronglyMeasurable))
        (1 / ((n : ℝ) + 1)))
  have hStrong :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
          atTop (nhds P[X 0]) :=
    ProbabilityTheory.strong_law_ae X hInt hpairwise hident
  have hAS_mean :
      ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => P[X 0]) := by
    filter_upwards [hStrong] with ω hω
    have hcomp :=
      hω.comp (Filter.tendsto_add_atTop_nat 1)
    convert hcomp using 1
    ext n
    have hsum :
        (∑ i : Fin (n + 1), X i.1 ω) =
          ∑ i ∈ Finset.range (n + 1), X i ω := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i => X i ω) (n + 1))
    simp [Function.comp_apply, thm_11_5_sampleMean, one_div, smul_eq_mul, hsum,
      Nat.cast_add, Nat.cast_one]
  have hAS :
      ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
    filter_upwards [hAS_mean] with ω hω
    simpa [hmean] using hω
  exact thm_10_2 P (fun n => thm_11_5_sampleMean X n) (fun _ => m) hAvg_meas hAS
