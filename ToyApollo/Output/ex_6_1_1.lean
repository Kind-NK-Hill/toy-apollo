/-
TASK ID: ex_6_1_1
TYPE: Example_Proof
SOURCE PLAN: 19_chap6_simple_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_6_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

theorem ex_6_1_1_ennreal_support
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    X.lintegral μ = Finset.sum X.range
      (fun x => x * μ (X ⁻¹' {x})) := by
  rfl

theorem ex_6_1_1
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (hNoConflict :
      ¬ ((∃ x ∈ X.range,
            simpleFunctionIntegralTerm μ X x = ⊤) ∧
         (∃ x ∈ X.range,
            simpleFunctionIntegralTerm μ X x = ⊥))) :
    def_6_2 μ X = some
      (Finset.sum X.range
        (fun x => simpleFunctionIntegralTerm μ X x)) := by
  have hDefined : simpleFunctionIntegralDefined μ X := by
    simpa [simpleFunctionIntegralDefined, simpleFunctionHasPosInf,
      simpleFunctionHasNegInf] using hNoConflict
  apply (def62_eq_some_iff μ X _).2
  refine ⟨hDefined, ?_⟩
  rfl

theorem ex_6_1_1_counting
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (X : SimpleFunc Ω EReal)
    (hNoConflict :
      ¬ ((∃ x ∈ X.range,
            simpleFunctionIntegralTerm (Measure.count : Measure Ω) X x = ⊤) ∧
         (∃ x ∈ X.range,
            simpleFunctionIntegralTerm (Measure.count : Measure Ω) X x = ⊥))) :
    def_6_2 (Measure.count : Measure Ω) X =
      some (Finset.sum Finset.univ fun ω => X ω) := by
  classical
  have hDefined : simpleFunctionIntegralDefined (Measure.count : Measure Ω) X := by
    simpa [simpleFunctionIntegralDefined, simpleFunctionHasPosInf,
      simpleFunctionHasNegInf] using hNoConflict
  apply (def62_eq_some_iff (Measure.count : Measure Ω) X _).2
  refine ⟨hDefined, ?_⟩
  unfold simpleFunctionIntegralValue
  simp only [simpleFunctionIntegralTerm]
  calc
    (∑ x ∈ X.range,
        x * (((Measure.count : Measure Ω) (X ⁻¹' {x}) : ENNReal) : EReal)) =
        ∑ x ∈ X.range,
          ∑ ω ∈ (Finset.univ : Finset Ω) with X ω = x, x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      let hFinite : (X ⁻¹' {x} : Set Ω).Finite := Set.toFinite _
      rw [Measure.count_apply_finite (X ⁻¹' {x}) hFinite]
      have hFiber :
          hFinite.toFinset = Finset.univ.filter (fun ω => X ω = x) := by
        ext ω
        simp
      rw [hFiber]
      have hCast :
          (((Finset.univ.filter (fun ω => X ω = x)).card : ENNReal) : EReal) =
            ((Finset.univ.filter (fun ω => X ω = x)).card : EReal) := by
        norm_cast
      rw [hCast]
      simp [Finset.sum_const, mul_comm]
    _ = ∑ ω ∈ (Finset.univ : Finset Ω), X ω := by
      exact Finset.sum_fiberwise_of_maps_to'
        (s := Finset.univ) (t := X.range) (g := fun ω => X ω)
        (fun ω _ => SimpleFunc.mem_range.2 ⟨ω, rfl⟩) (fun x => x)
    _ = ∑ ω : Ω, X ω := by
      simp
