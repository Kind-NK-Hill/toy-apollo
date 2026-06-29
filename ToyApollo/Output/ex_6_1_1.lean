import Mathlib.MeasureTheory.Function.SimpleFunc

/-
TASK ID: ex_6_1_1
TYPE: Example_Proof
SOURCE PLAN: 19_chap6_simple_functions
TASK CONTENT:
\textbf{Example 6.1.1 (Lebesgue Integral for Finite Sample Space)} \\
When $\Omega$ is a finite set and $\mu$ is the counting measure, the Lebesgue integral reduces to a finite sum. If $\Omega$ is a finite set and $\mu$ is a general measure on $\Omega$, then the Lebesgue integral of a simple function is a finite weighted sum.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

/--
Example 6.1.1: on a finite sample space, a simple-function integral is a finite
weighted sum over the finitely many values in its range. The counting-measure
case is the corresponding unweighted finite-sum specialization.
-/
theorem ex_6_1_1 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    X.lintegral μ = Finset.sum X.range (fun x => x * μ (X ⁻¹' {x})) := by
  simpa using
    (MeasureTheory.SimpleFunc.map_lintegral (μ := μ) (g := fun x : ENNReal => x) X)
