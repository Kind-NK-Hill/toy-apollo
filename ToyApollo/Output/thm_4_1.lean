import Mathlib
import ToyApollo.Output.def_4_2

/-
Theorem 4.1: The indicator function 1_A is (F, B(ℝ))-measurable if and only if A is F-measurable.
-/
theorem thm_4_1 {Ω : Type _} [MeasurableSpace Ω] (A : Set Ω) :
    Measurable (Set.indicator A (fun _ => (1 : ℝ))) ↔ MeasurableSet A := by
      constructor <;> intro h;
      · convert h ( MeasurableSingletonClass.measurableSet_singleton 1 ) using 1 ; aesop;
      · exact Measurable.indicator measurable_const h