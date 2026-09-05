/-
TASK ID: ex_6_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc
import ProbabilityTheory.chapter_06.def_6_2




open MeasureTheory
open scoped BigOperators






theorem ex_6_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : Set Ω)
    (hB : MeasurableSet B) :
    Measurable
        (((SimpleFunc.const Ω (1 : EReal)).restrict B : SimpleFunc Ω EReal) : Ω → EReal) ∧
      ∀ {x : EReal},
        def_6_2 μ ((SimpleFunc.const Ω (1 : EReal)).restrict B) = some x →
        x = (μ B : EReal) := by
  refine ⟨SimpleFunc.measurable ((SimpleFunc.const Ω 1).restrict B), ?_⟩
  · intro x hx
    have h_sum :
        (∑ y ∈ ((SimpleFunc.const Ω 1).restrict B).range,
            y * (μ (((SimpleFunc.const Ω 1).restrict B) ⁻¹' {y} : Set Ω) : EReal)) =
          (1 : EReal) * (μ B : EReal) := by
      simp  [SimpleFunc.restrict ];
      split_ifs ; simp_all [ SimpleFunc.range ];
      rw [ Finset.sum_eq_single 1 ] <;> simp +contextual [ Set.indicator ];
      · congr with x ; simp [ Set.indicator ];
      · intro h; simp [ Set.preimage, h ] ;
    convert h_sum using 1;
    · exact def62_eq_some_iff _ _ _ |>.1 hx |>.2.symm;
    · norm_num




theorem indicatorConstIntegral_def_6_2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : EReal) (B : Set Ω) (hB : MeasurableSet B) :
    def_6_2 μ ((SimpleFunc.const Ω c).restrict B) = some (c * (μ B : EReal)) := by
  by_cases hc : c = 0 <;> simp_all [ def62_eq_some_iff, SimpleFunc.restrict ];
  · simp +decide [ simpleFunctionIntegralValue, simpleFunctionIntegralTerm ];
    refine' ⟨ _, _ ⟩;
    · simp [ simpleFunctionIntegralDefined,
        simpleFunctionHasPosInf, simpleFunctionHasNegInf ];
      unfold simpleFunctionIntegralTerm;
      intro a a_1 a_2
      subst hc
      simp_all only [SimpleFunc.coe_zero, zero_mul, EReal.zero_ne_top];
    · rw [ Finset.sum_eq_zero ] ;
      intro x a
      subst hc
      simp_all only [SimpleFunc.mem_range,
        SimpleFunc.coe_zero, Set.mem_range, Pi.zero_apply, exists_const_iff]
      obtain ⟨left, right⟩ := a
      subst right
      simp_all only [zero_mul];
  · refine' ⟨ _, _ ⟩;
    · refine' fun h => _;
      obtain ⟨ ⟨ x, hx₁, hx₂ ⟩, ⟨ y, hy₁, hy₂ ⟩ ⟩ := h;
      simp_all [ SimpleFunc.range, simpleFunctionIntegralTerm ];
      rcases hx₁ with ⟨ x, rfl ⟩ ; rcases hy₁ with ⟨ y, rfl ⟩ ;
      by_cases hx : x ∈ B <;>
      by_cases hy : y ∈ B <;>
      simp_all [ Set.indicator ]
    · rw [ simpleFunctionIntegralValue ];
      rw [ Finset.sum_eq_single c ] <;>
      simp [ hc, simpleFunctionIntegralTerm ];
      · congr ; ext x ; by_cases hx : x ∈ B <;> simp  [hx];
        exact Ne.symm hc;
      · intro a ha;
        contrapose! ha;
        simp_all only [ne_eq, Set.indicator_of_mem, Function.const_apply];
      · intro h;
        rw [ show ( B.indicator ( Function.const Ω c ) ) ⁻¹' { c } = ∅ by ext x; specialize h x; aesop ] ;
        simp
