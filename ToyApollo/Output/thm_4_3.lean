/-
TASK ID: thm_4_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic

variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

theorem measurable_composition {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  -- Suppose A is a set in H (i.e., A is a measurable set in Ω'')
  intro A hA
  -- Because g is measurable, the pre-image g⁻¹(A) is measurable in Ω'
  have h_pre_g : MeasurableSet (g ⁻¹' A) := hg hA
  -- Because f is measurable, f⁻¹(g⁻¹(A)) is measurable in Ω
  have h_pre_f : MeasurableSet (f ⁻¹' (g ⁻¹' A)) := hf h_pre_g
  -- h⁻¹(A) is equal to f⁻¹(g⁻¹(A)). In Lean, these are definitionally equal.
  exact h_pre_f

theorem measurable_composition_short {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) :=
  fun _ hA => hf (hg hA)
