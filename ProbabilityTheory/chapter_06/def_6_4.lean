/-
TASK ID: def_6_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic








open MeasureTheory



noncomputable def positivePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => max (X ω) 0



noncomputable def negativePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => -min (X ω) 0

 
noncomputable def def_6_4 {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : (Ω → ℝ) × (Ω → ℝ) :=
  (positivePart X, negativePart X)

section PositiveNegativeParts

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}



 
theorem measurable_positivePart (hX : Measurable X) : Measurable (positivePart X) := by
  unfold positivePart
  exact (continuous_id.max continuous_const).measurable.comp hX

 
theorem measurable_negativePart (hX : Measurable X) : Measurable (negativePart X) := by
  unfold negativePart
  exact ((continuous_id.min continuous_const).neg).measurable.comp hX

 
theorem positivePart_nonneg (ω : Ω) : 0 ≤ positivePart X ω := by
  exact le_max_right (X ω) 0

 
theorem negativePart_nonneg (ω : Ω) : 0 ≤ negativePart X ω := by
  simp [negativePart]

 
theorem negativePart_eq_max_neg (X : Ω → ℝ) :
    negativePart X = fun ω => max (-X ω) 0 := by
  funext ω
  simpa [negativePart] using (max_neg_neg (X ω) (0 : ℝ)).symm

 
theorem self_eq_positivePart_sub_negativePart (X : Ω → ℝ) :
    X = fun ω => positivePart X ω - negativePart X ω := by
  funext ω
  rw [negativePart_eq_max_neg]
  simp only [positivePart,
    max_zero_sub_max_neg_zero_eq_self]

 
theorem abs_eq_positivePart_add_negativePart (X : Ω → ℝ) :
    (fun ω => |X ω|) = fun ω => positivePart X ω + negativePart X ω := by
  funext ω
  by_cases hω : 0 ≤ X ω
  · have hneg : ¬ X ω < 0 := not_lt_of_ge hω
    have hmax : max (X ω) 0 = X ω := max_eq_left hω
    have hmin : min (X ω) 0 = 0 := min_eq_right hω
    have habs : |X ω| = X ω := abs_of_nonneg hω
    simp [positivePart, negativePart, hmax, hmin, habs]
  · have hlt : X ω < 0 := lt_of_not_ge hω
    have hmax : max (X ω) 0 = 0 := max_eq_right (le_of_lt hlt)
    have hmin : min (X ω) 0 = X ω := min_eq_left (le_of_lt hlt)
    have habs : |X ω| = -X ω := abs_of_neg hlt
    simp [positivePart, negativePart, hmax, hmin, habs]

end PositiveNegativeParts
