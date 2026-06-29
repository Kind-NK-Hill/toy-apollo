import Mathlib

/-
TASK ID: thm_14_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-weak-convergence
TASK CONTENT:
\begin{thmbox}{14.1 (Levy's Continuity Theorem)}
\end{thmbox}

Let .(Xn)\infty

n=1 be a sequence of real-valued random variables. Let Pn denote

the probability measure induced by Xn on R, and \phin(t) be the characteristic

function of Xn,f o r n\geq 1 Suppose the characteristic functions converge

pointwise to some function \phi(t).

Then the followings are equivalent:

1. Xn converges weakly to some random variable X as n tends to infinity.

2. \phi(t) is the characteristic function of a random variable.

3. \phi(t) is continuous at t= 0 .

4. The sequence of probability measures .(Pn)\infty

n=1 is tight.

In the first section in this chapter, we define the notion of weak convergence,

which is equivalent to convergence in distribution. We also prove that convergence

in total variation implies convergence in distribution. Then, we introduce the notion

of tightness of measures and Prokhorov theorem. In the last section, we use the

continuity theorem to prove a version of central limit theorem that assumes iid.

random variables with finite variance. In the last section, we will state a central

limit theorem for triangular array and illustrate it through an example.

Suppose we can only obtain information about a probability distribution P through

some measurements of the form .

\int

hdP , where h(x) is a "test function"If we

have a sequence of probability distributions Pn's, it would be desirable if, for each

test function h(x), the sequence of measurements .

\int

hdP n converges as n tends to

infinity. This motivates the concept of weak convergence, which allows us to study

the convergence of probability distributions based on their behavior with respect to

test functions.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- Characteristic function of a probability measure on `ℝ`, matching the
law-level version used by Mathlib's Lévy convergence theorem. -/
def thm_14_1_characteristicFunction
    (P : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (P : Measure ℝ) t

/-- The source hypothesis: characteristic functions of `P_n` converge
pointwise to the function `φ`. -/
def thm_14_1_pointwiseCharFunConvergence
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => thm_14_1_characteristicFunction (P n) t)
      atTop (𝓝 (φ t))

/-- Condition 1 of Theorem 14.1 in law-level form: the laws converge weakly to
some probability measure. -/
def thm_14_1_weakLimit
    (P : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∃ P₀ : ProbabilityMeasure ℝ, Tendsto P atTop (𝓝 P₀)

/-- Condition 2: the pointwise limit is the characteristic function of a
probability measure. -/
def thm_14_1_limitIsCharacteristic
    (φ : ℝ → ℂ) : Prop :=
  ∃ P₀ : ProbabilityMeasure ℝ,
    ∀ t : ℝ, φ t = thm_14_1_characteristicFunction P₀ t

/-- Condition 3: the limiting function is continuous at zero. -/
def thm_14_1_continuousAtZero (φ : ℝ → ℂ) : Prop :=
  ContinuousAt φ 0

/-- Condition 4: the sequence of probability measures is tight. -/
def thm_14_1_tight (P : ℕ → ProbabilityMeasure ℝ) : Prop :=
  IsTightMeasureSet (Set.range fun n : ℕ => ((P n : ProbabilityMeasure ℝ) : Measure ℝ))

/-- The four equivalent conditions stated in Lévy's continuity theorem. -/
def thm_14_1_fourConditionsEquivalent
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  (thm_14_1_weakLimit P ↔ thm_14_1_limitIsCharacteristic φ) ∧
    (thm_14_1_weakLimit P ↔ thm_14_1_continuousAtZero φ) ∧
      (thm_14_1_weakLimit P ↔ thm_14_1_tight P)

/-- Theorem 14.1, recorded as the full statement. -/
def thm_14_1_fullStatement
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  thm_14_1_pointwiseCharFunConvergence P φ →
    thm_14_1_fourConditionsEquivalent P φ

/-- Mathlib's law-level Lévy theorem gives the equivalence between weak
convergence of laws and pointwise convergence to a characteristic function. -/
theorem thm_14_1_weak_iff_characteristic
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    thm_14_1_weakLimit P ↔ thm_14_1_limitIsCharacteristic φ := by
  constructor
  · rintro ⟨P₀, hWeak⟩
    refine ⟨P₀, ?_⟩
    intro t
    have hChar :
        Tendsto (fun n : ℕ => thm_14_1_characteristicFunction (P n) t)
          atTop (𝓝 (thm_14_1_characteristicFunction P₀ t)) := by
      simpa [thm_14_1_characteristicFunction] using
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun
          (μ := P) (μ₀ := P₀)).1 hWeak t
    exact tendsto_nhds_unique (hφ t) hChar
  · rintro ⟨P₀, hCharEq⟩
    refine ⟨P₀, ?_⟩
    exact
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun
        (μ := P) (μ₀ := P₀)).2 (fun t => by
          simpa [thm_14_1_characteristicFunction, hCharEq t] using hφ t)

/-- Condition 2 implies condition 3: every characteristic function is continuous
at zero. -/
theorem thm_14_1_characteristic_continuousAtZero {φ : ℝ → ℂ}
    (hChar : thm_14_1_limitIsCharacteristic φ) :
    thm_14_1_continuousAtZero φ := by
  rcases hChar with ⟨P₀, hφ⟩
  have hEq :
      φ = fun t : ℝ => thm_14_1_characteristicFunction P₀ t := by
    funext t
    exact hφ t
  have hCont :
      ContinuousAt (fun t : ℝ => thm_14_1_characteristicFunction P₀ t) 0 := by
    simpa [thm_14_1_characteristicFunction] using
      (continuous_charFun (μ := (P₀ : Measure ℝ))).continuousAt
  simpa [thm_14_1_continuousAtZero, hEq] using hCont

/-- Condition 3 implies condition 4 under the pointwise characteristic-function
convergence hypothesis: this is the tightness direction of Lévy's theorem. -/
theorem thm_14_1_continuity_tight
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ)
    (hCont : thm_14_1_continuousAtZero φ) :
    thm_14_1_tight P := by
  have hTight :
      IsTightMeasureSet
        (Set.range fun n : ℕ => ((P n : ProbabilityMeasure ℝ) : Measure ℝ)) := by
    exact
      isTightMeasureSet_of_tendsto_charFun
        (μ := fun n : ℕ => ((P n : ProbabilityMeasure ℝ) : Measure ℝ))
        hCont
        (fun t => by
          simpa [thm_14_1_characteristicFunction] using hφ t)
  simpa [thm_14_1_tight] using hTight

/-- The portion of Theorem 14.1 already supplied directly by Mathlib and the
local interfaces above.  The remaining reverse directions are proved later in
the textbook development using weak convergence, tightness, and Prokhorov. -/
theorem thm_14_1_mathlib_spine
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    (thm_14_1_weakLimit P ↔ thm_14_1_limitIsCharacteristic φ) ∧
      (thm_14_1_limitIsCharacteristic φ →
        thm_14_1_continuousAtZero φ) ∧
        (thm_14_1_continuousAtZero φ → thm_14_1_tight P) := by
  exact ⟨thm_14_1_weak_iff_characteristic hφ,
    thm_14_1_characteristic_continuousAtZero,
    thm_14_1_continuity_tight hφ⟩

/-- Tightness plus pointwise characteristic-function convergence produces a
weak limit.  Prokhorov compactness gives a weakly convergent subsequence; the
subsequence characteristic functions identify the subsequential limit as the
law whose characteristic function is `φ`, and Mathlib's Lévy theorem then
upgrades this to weak convergence of the whole sequence. -/
theorem thm_14_1_tight_to_weak
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ)
    (hTight : thm_14_1_tight P) :
    thm_14_1_weakLimit P := by
  have hcompact : IsCompact (closure (Set.range P)) := by
    refine isCompact_closure_of_isTightMeasureSet (S := Set.range P) ?_
    have hset :
        {x | ∃ μ ∈ Set.range P, (μ : Measure ℝ) = x} =
          Set.range (fun n : ℕ => ((P n : ProbabilityMeasure ℝ) : Measure ℝ)) := by
      ext μ
      constructor
      · rintro ⟨P₀, hP₀, rfl⟩
        rcases hP₀ with ⟨n, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨P n, ⟨n, rfl⟩, rfl⟩
    simpa [thm_14_1_tight, hset] using hTight
  rcases hcompact.tendsto_subseq
      (x := P)
      (fun n : ℕ => subset_closure (Set.mem_range_self n)) with
    ⟨P₀, _hP₀, index, hindex, hSubWeak⟩
  have hLimitChar : thm_14_1_limitIsCharacteristic φ := by
    refine ⟨P₀, ?_⟩
    intro t
    have hSubPhi :
        Tendsto (fun k : ℕ => thm_14_1_characteristicFunction (P (index k)) t)
          atTop (𝓝 (φ t)) :=
      (hφ t).comp hindex.tendsto_atTop
    have hSubChar :
        Tendsto (fun k : ℕ => thm_14_1_characteristicFunction (P (index k)) t)
          atTop (𝓝 (thm_14_1_characteristicFunction P₀ t)) := by
      simpa [thm_14_1_characteristicFunction, Function.comp_def] using
        (ProbabilityMeasure.tendsto_iff_tendsto_charFun
          (μ := fun k : ℕ => P (index k)) (μ₀ := P₀)).1
          (by simpa [Function.comp_def] using hSubWeak) t
    exact tendsto_nhds_unique hSubPhi hSubChar
  exact (thm_14_1_weak_iff_characteristic hφ).2 hLimitChar

/-- Continuity at zero gives tightness by the characteristic-function estimate,
then tightness gives the weak limit. -/
theorem thm_14_1_continuity_to_weak
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ)
    (hCont : thm_14_1_continuousAtZero φ) :
    thm_14_1_weakLimit P :=
  thm_14_1_tight_to_weak hφ (thm_14_1_continuity_tight hφ hCont)

/-- Theorem 14.1 as a source-faithful theorem object. -/
theorem thm_14_1
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    thm_14_1_fourConditionsEquivalent P φ := by
  have hWeakChar := thm_14_1_weak_iff_characteristic hφ
  have hCharCont :
      thm_14_1_limitIsCharacteristic φ →
        thm_14_1_continuousAtZero φ :=
    fun h => thm_14_1_characteristic_continuousAtZero h
  have hContTight := thm_14_1_continuity_tight hφ
  refine ⟨hWeakChar, ?_, ?_⟩
  · constructor
    · intro hWeak
      exact hCharCont (hWeakChar.mp hWeak)
    · exact thm_14_1_continuity_to_weak hφ
  · constructor
    · intro hWeak
      exact hContTight (hCharCont (hWeakChar.mp hWeak))
    · exact thm_14_1_tight_to_weak hφ

/-- The Prop-valued full statement is discharged by the source-faithful theorem
above. -/
theorem thm_14_1_fullStatement_holds
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ} :
    thm_14_1_fullStatement P φ := by
  intro hφ
  exact thm_14_1 hφ
