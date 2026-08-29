/-
TASK ID: thm_14_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

def thm_14_1_characteristicFunction
    (P : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (P : Measure ℝ) t

def thm_14_1_pointwiseCharFunConvergence
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => thm_14_1_characteristicFunction (P n) t)
      atTop (𝓝 (φ t))

def thm_14_1_weakLimit
    (P : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∃ P₀ : ProbabilityMeasure ℝ, Tendsto P atTop (𝓝 P₀)

def thm_14_1_limitIsCharacteristic
    (φ : ℝ → ℂ) : Prop :=
  ∃ P₀ : ProbabilityMeasure ℝ,
    ∀ t : ℝ, φ t = thm_14_1_characteristicFunction P₀ t

def thm_14_1_continuousAtZero (φ : ℝ → ℂ) : Prop :=
  ContinuousAt φ 0

def thm_14_1_tight (P : ℕ → ProbabilityMeasure ℝ) : Prop :=
  IsTightMeasureSet (Set.range fun n : ℕ => ((P n : ProbabilityMeasure ℝ) : Measure ℝ))

def thm_14_1_fourConditionsEquivalent
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  (thm_14_1_weakLimit P ↔ thm_14_1_limitIsCharacteristic φ) ∧
    (thm_14_1_weakLimit P ↔ thm_14_1_continuousAtZero φ) ∧
      (thm_14_1_weakLimit P ↔ thm_14_1_tight P)

def thm_14_1_fullStatement
    (P : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  thm_14_1_pointwiseCharFunConvergence P φ →
    thm_14_1_fourConditionsEquivalent P φ

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
    rw [hset]
    simpa [thm_14_1_tight] using hTight
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

theorem thm_14_1_continuity_to_weak
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ)
    (hCont : thm_14_1_continuousAtZero φ) :
    thm_14_1_weakLimit P :=
  thm_14_1_tight_to_weak hφ (thm_14_1_continuity_tight hφ hCont)

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

theorem thm_14_1_fullStatement_holds
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ} :
    thm_14_1_fullStatement P φ := by
  intro hφ
  exact thm_14_1 hφ
