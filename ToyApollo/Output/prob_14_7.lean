import Mathlib
import ToyApollo.Output.prob_10_10
import ToyApollo.Output.thm_14_1

/-
TASK ID: prob_14_7
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.7.} Let (Xn)\infty

n=1 and (Yn)\infty

n=1 be two sequences of random variables such that

Xn and Yn are independent random variables defined on the same probability space.

Show that if Xn

D

\to X and Yn

D

\to Y , then Xn +Yn converges to X+Y in distribution

(cf. Problem 10.10). (Hint: Apply Levy's continuity theorem.)
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- The law of a real-valued random variable as a probability measure. -/
def prob_14_7_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) :
    ProbabilityMeasure ℝ :=
  ⟨P.map X, Measure.isProbabilityMeasure_map hX⟩

/-- Weak convergence of random variables implies pointwise convergence of
their characteristic functions. -/
theorem prob_14_7_distribution_convergence_to_characteristic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (h : TendstoInDistribution Xn atTop X (fun _ : ℕ => P) P) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ =>
          thm_14_1_characteristicFunction
            (prob_14_7_law P (Xn n) (h.forall_aemeasurable n)) t)
        atTop
        (𝓝 (thm_14_1_characteristicFunction
          (prob_14_7_law P X h.aemeasurable_limit) t)) := by
  intro t
  have hchar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := fun n : ℕ =>
        prob_14_7_law P (Xn n) (h.forall_aemeasurable n))
      (μ₀ := prob_14_7_law P X h.aemeasurable_limit)).1 h.tendsto t
  simpa [thm_14_1_characteristicFunction, prob_14_7_law] using hchar

/-- Independence of two random variables identifies the characteristic function
of their sum with the product of their characteristic functions. -/
theorem prob_14_7_independent_sum_characteristic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y) (t : ℝ) :
    thm_14_1_characteristicFunction
        (prob_14_7_law P (fun ω => X ω + Y ω) (hX.add hY)) t =
      thm_14_1_characteristicFunction (prob_14_7_law P X hX) t *
        thm_14_1_characteristicFunction (prob_14_7_law P Y hY) t := by
  simpa [thm_14_1_characteristicFunction, prob_14_7_law] using
    congrFun (hXY.charFun_map_fun_add_eq_mul hX hY) t

/-- The characteristic functions of `X_n + Y_n` converge pointwise to the
characteristic function of `X + Y`. -/
theorem prob_14_7_sum_characteristic_convergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : TendstoInDistribution Xn atTop X (fun _ : ℕ => P) P)
    (hY : TendstoInDistribution Yn atTop Y (fun _ : ℕ => P) P)
    (hIndep : ∀ n : ℕ, Xn n ⟂ᵢ[P] Yn n) (hLimitIndep : X ⟂ᵢ[P] Y) :
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ =>
          thm_14_1_characteristicFunction
            (prob_14_7_law P (fun ω => Xn n ω + Yn n ω)
              ((hX.forall_aemeasurable n).add (hY.forall_aemeasurable n))) t)
        atTop
        (𝓝 (thm_14_1_characteristicFunction
          (prob_14_7_law P (fun ω => X ω + Y ω)
            (hX.aemeasurable_limit.add hY.aemeasurable_limit)) t)) := by
  intro t
  have hXchar := prob_14_7_distribution_convergence_to_characteristic P hX t
  have hYchar := prob_14_7_distribution_convergence_to_characteristic P hY t
  have hProd :
      Tendsto
        (fun n : ℕ =>
          thm_14_1_characteristicFunction
              (prob_14_7_law P (Xn n) (hX.forall_aemeasurable n)) t *
            thm_14_1_characteristicFunction
              (prob_14_7_law P (Yn n) (hY.forall_aemeasurable n)) t)
        atTop
        (𝓝 (thm_14_1_characteristicFunction
              (prob_14_7_law P X hX.aemeasurable_limit) t *
            thm_14_1_characteristicFunction
              (prob_14_7_law P Y hY.aemeasurable_limit) t)) :=
    hXchar.mul hYchar
  have hSeq :
      (fun n : ℕ =>
        thm_14_1_characteristicFunction
          (prob_14_7_law P (fun ω => Xn n ω + Yn n ω)
            ((hX.forall_aemeasurable n).add (hY.forall_aemeasurable n))) t) =
        (fun n : ℕ =>
          thm_14_1_characteristicFunction
              (prob_14_7_law P (Xn n) (hX.forall_aemeasurable n)) t *
            thm_14_1_characteristicFunction
              (prob_14_7_law P (Yn n) (hY.forall_aemeasurable n)) t) := by
    funext n
    exact prob_14_7_independent_sum_characteristic
      (hX.forall_aemeasurable n) (hY.forall_aemeasurable n) (hIndep n) t
  have hTarget :
      thm_14_1_characteristicFunction
          (prob_14_7_law P (fun ω => X ω + Y ω)
            (hX.aemeasurable_limit.add hY.aemeasurable_limit)) t =
        thm_14_1_characteristicFunction
            (prob_14_7_law P X hX.aemeasurable_limit) t *
          thm_14_1_characteristicFunction
            (prob_14_7_law P Y hY.aemeasurable_limit) t :=
    prob_14_7_independent_sum_characteristic
      hX.aemeasurable_limit hY.aemeasurable_limit hLimitIndep t
  simpa [hSeq, hTarget] using hProd

/-- The law-level convergence of the sums, obtained by Levy's continuity
criterion from the preceding characteristic-function convergence. -/
theorem prob_14_7_sum_laws_converge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : TendstoInDistribution Xn atTop X (fun _ : ℕ => P) P)
    (hY : TendstoInDistribution Yn atTop Y (fun _ : ℕ => P) P)
    (hIndep : ∀ n : ℕ, Xn n ⟂ᵢ[P] Yn n) (hLimitIndep : X ⟂ᵢ[P] Y) :
    Tendsto
      (fun n : ℕ =>
        prob_14_7_law P (fun ω => Xn n ω + Yn n ω)
          ((hX.forall_aemeasurable n).add (hY.forall_aemeasurable n)))
      atTop
      (𝓝 (prob_14_7_law P (fun ω => X ω + Y ω)
        (hX.aemeasurable_limit.add hY.aemeasurable_limit))) := by
  exact
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2
      (prob_14_7_sum_characteristic_convergence
        P Xn Yn X Y hX hY hIndep hLimitIndep)

/-- Problem 14.7: if `X_n` and `Y_n` converge in distribution, each pair
`X_n, Y_n` is independent, and the limiting variables are independent, then
`X_n + Y_n` converges in distribution to `X + Y`. -/
theorem prob_14_7
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : TendstoInDistribution Xn atTop X (fun _ : ℕ => P) P)
    (hY : TendstoInDistribution Yn atTop Y (fun _ : ℕ => P) P)
    (hIndep : ∀ n : ℕ, Xn n ⟂ᵢ[P] Yn n) (hLimitIndep : X ⟂ᵢ[P] Y) :
    TendstoInDistribution
      (fun n : ℕ => fun ω => Xn n ω + Yn n ω)
      atTop
      (fun ω => X ω + Y ω)
      (fun _ : ℕ => P)
      P := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (hX.forall_aemeasurable n).add (hY.forall_aemeasurable n)
  · exact hX.aemeasurable_limit.add hY.aemeasurable_limit
  · exact prob_14_7_sum_laws_converge P Xn Yn X Y hX hY hIndep hLimitIndep
