/-
TASK ID: ex_6_1_2
TYPE: Example_Proof
SOURCE PLAN: 19_chap6_simple_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_6_2

open MeasureTheory
open scoped BigOperators

-- WRITE FINAL LEAN CODE BELOW

theorem ex_6_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : Set Ω)
    (hB : MeasurableSet B) :
    Measurable
        (((SimpleFunc.const Ω (1 : EReal)).restrict B : SimpleFunc Ω EReal) : Ω → EReal) ∧
      ∀ {x : EReal},
        def_6_2 μ ((SimpleFunc.const Ω (1 : EReal)).restrict B) = some x →
        x = (μ B : EReal) := by
  classical
  let f : SimpleFunc Ω Bool := (SimpleFunc.const Ω true).restrict B
  let I : SimpleFunc Ω EReal := (SimpleFunc.const Ω (1 : EReal)).restrict B
  have hI :
      I = f.map (fun t : Bool => if t then (1 : EReal) else 0) := by
    ext ω
    by_cases hω : ω ∈ B
    · simp [I, f, SimpleFunc.restrict_apply, hB, hω]
    · simp [I, f, SimpleFunc.restrict_apply, hB, hω]
  have hf_true : (f : Ω → Bool) ⁻¹' {true} = B := by
    ext ω
    by_cases hω : ω ∈ B
    · simp [f, hB, hω]
    · simp [f, hB, hω]
  have hf_false : (f : Ω → Bool) ⁻¹' {false} = Bᶜ := by
    ext ω
    constructor
    · intro hω
      have hωB : ω ∉ B := by
        intro hmem
        have : f ω = true := by
          simp [f, hB, hmem]
        simpa [this] using hω
      simpa [Set.mem_compl] using hωB
    · intro hω
      have hωB : ω ∉ B := by
        simpa [Set.mem_compl] using hω
      change f ω = (0 : Bool)
      simp [f, hB, hωB]
  have hzero_outside :
      ∀ x ∈ (Finset.univ : Finset Bool), x ∉ f.range →
        (if x then (1 : EReal) else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal) = 0 := by
    intro x _ hx
    have hpre : (f : Ω → Bool) ⁻¹' {x} = ∅ := by
      ext ω
      constructor
      · intro hω
        exact hx (SimpleFunc.mem_range.2 ⟨ω, hω⟩)
      · intro hω
        cases hω
    rw [hpre]
    simp
  have hvalue :
      simpleFunctionIntegralValue μ I = (μ B : EReal) := by
    rw [hI, integralValue_map (μ := μ) (g := fun t : Bool => if t then (1 : EReal) else 0)
      (f := f)]
    have hrange :
        f.range ⊆ (Finset.univ : Finset Bool) := by
      intro x hx
      simp
    calc
      ∑ x ∈ f.range, (if x then (1 : EReal) else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal)
          = ∑ x ∈ (Finset.univ : Finset Bool),
              (if x then (1 : EReal) else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal) := by
                exact Finset.sum_subset hrange hzero_outside
      _ = (μ B : EReal) := by
            simp [hf_true, hf_false]
  refine ⟨?_, ?_⟩
  · simpa [I] using I.measurable
  · intro x hx
    rcases (def62_eq_some_iff (μ := μ) (f := I) (v := x)).1 hx with ⟨_, hxval⟩
    rw [← hxval, hvalue]

theorem indicatorConstIntegral_def_6_2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : EReal) (B : Set Ω) (hB : MeasurableSet B) :
    def_6_2 μ ((SimpleFunc.const Ω c).restrict B) = some (c * (μ B : EReal)) := by
  classical
  let f : SimpleFunc Ω Bool := (SimpleFunc.const Ω true).restrict B
  let I : SimpleFunc Ω EReal := (SimpleFunc.const Ω c).restrict B
  have hI :
      I = f.map (fun t : Bool => if t then c else 0) := by
    ext ω
    by_cases hω : ω ∈ B
    · simp [I, f, SimpleFunc.restrict_apply, hB, hω]
    · simp [I, f, SimpleFunc.restrict_apply, hB, hω]
  have hf_true : (f : Ω → Bool) ⁻¹' {true} = B := by
    ext ω
    by_cases hω : ω ∈ B
    · simp [f, hB, hω]
    · simp [f, hB, hω]
  have hf_false : (f : Ω → Bool) ⁻¹' {false} = Bᶜ := by
    ext ω
    constructor
    · intro hω
      have hωB : ω ∉ B := by
        intro hmem
        have : f ω = true := by
          simp [f, hB, hmem]
        simpa [this] using hω
      simpa [Set.mem_compl] using hωB
    · intro hω
      have hωB : ω ∉ B := by
        simpa [Set.mem_compl] using hω
      change f ω = (0 : Bool)
      simp [f, hB, hωB]
  have hzero_outside :
      ∀ x ∈ (Finset.univ : Finset Bool), x ∉ f.range →
        (if x then c else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal) = 0 := by
    intro x _ hx
    have hpre : (f : Ω → Bool) ⁻¹' {x} = ∅ := by
      ext ω
      constructor
      · intro hω
        exact hx (SimpleFunc.mem_range.2 ⟨ω, hω⟩)
      · intro hω
        cases hω
    rw [hpre]
    simp
  have hvalue :
      simpleFunctionIntegralValue μ I = c * (μ B : EReal) := by
    rw [hI, integralValue_map (μ := μ) (g := fun t : Bool => if t then c else 0)
      (f := f)]
    have hrange :
        f.range ⊆ (Finset.univ : Finset Bool) := by
      intro x hx
      simp
    calc
      ∑ x ∈ f.range, (if x then c else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal)
          = ∑ x ∈ (Finset.univ : Finset Bool),
              (if x then c else 0) * (μ ((f : Ω → Bool) ⁻¹' {x}) : EReal) := by
                exact Finset.sum_subset hrange hzero_outside
      _ = c * (μ B : EReal) := by
            simp [hf_true, hf_false]
  have hrange :
      ∀ x ∈ I.range, x = 0 ∨ x = c := by
    intro x hx
    rcases SimpleFunc.mem_range.1 hx with ⟨ω, rfl⟩
    by_cases hω : ω ∈ B
    · right
      simp [I, SimpleFunc.restrict_apply, hB, hω]
    · left
      simp [I, SimpleFunc.restrict_apply, hB, hω]
  have hdefined : simpleFunctionIntegralDefined μ I := by
    intro hbad
    rcases hbad with ⟨⟨x, hx, hxtop⟩, ⟨y, hy, hybot⟩⟩
    have hx_ne_zero : x ≠ 0 := by
      intro hx0
      subst hx0
      simp [simpleFunctionIntegralTerm] at hxtop
    have hy_ne_zero : y ≠ 0 := by
      intro hy0
      subst hy0
      simp [simpleFunctionIntegralTerm] at hybot
    have hx_eq_c : x = c := by
      rcases hrange x hx with hx0 | hxc
      · exact (hx_ne_zero hx0).elim
      · exact hxc
    have hy_eq_c : y = c := by
      rcases hrange y hy with hy0 | hyc
      · exact (hy_ne_zero hy0).elim
      · exact hyc
    subst x y
    have : (⊤ : EReal) = ⊥ := hxtop.symm.trans hybot
    cases this
  exact (def62_eq_some_iff (μ := μ) (f := I) (v := c * (μ B : EReal))).2 ⟨hdefined, hvalue⟩
