import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real

/-!
# Example 4.3.1: A Random Variable Whose Value May Be ∞

This module formalizes Example 4.3.1:
1. Let X, Y, Z be real-valued random variables on Ω.
2. The function V = √(X² + Y² + Z²) is measurable.
3. The function W = (X² + Y² + Z²)⁻¹/² is measurable as a function into ENNReal ([0, ∞]).
4. In ENNReal, 0⁻¹ is defined as ∞ (⊤), handling the case where X = Y = Z = 0.
-/

open ENNReal MeasureTheory

/-- Example 4.3.1: Let X, Y, Z be real-valued random variables on a measurable space Ω.
Then the composition √(X² + Y² + Z²) is measurable.
The function W = (X² + Y² + Z²)⁻¹/² (mapping to ENNReal) is also measurable,
correctly assigning ∞ when the denominator is zero. -/
theorem example_4_3_1 {Ω : Type _} [MeasurableSpace Ω]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    let V := fun ω => Real.sqrt (X ω ^ 2 + Y ω ^ 2 + Z ω ^ 2)
    let W := fun ω => (ENNReal.ofReal (V ω))⁻¹
    Measurable V ∧ Measurable W := by
  -- Let f be the sum of squares
  let f := fun ω => X ω ^ 2 + Y ω ^ 2 + Z ω ^ 2
  
  -- Step 1: Prove the sum of squares is measurable.
  -- Sums and powers of measurable functions are measurable.
  have hf : Measurable f := by
    apply Measurable.add
    · apply Measurable.add
      · exact hX.pow_const 2
      · exact hY.pow_const 2
    · exact hZ.pow_const 2

  -- Step 2: Prove V = √(f) is measurable.
  -- Real.sqrt is continuous, thus Borel-measurable.
  have hV : Measurable (fun ω => Real.sqrt (f ω)) :=
    Real.continuous_sqrt.measurable.comp hf

  constructor
  · exact hV
  · -- Step 3: Prove W is measurable as a function into ENNReal (ℝ≥0∞).
    -- ENNReal.ofReal is continuous and thus Borel-measurable.
    have hV_enn : Measurable (fun ω => ENNReal.ofReal (Real.sqrt (f ω))) := 
      ENNReal.continuous_ofReal.measurable.comp hV
    -- In ENNReal, the inversion operation is measurable.
    -- Crucially, in ENNReal, 0⁻¹ = ⊤ (infinity).
    exact Measurable.inv hV_enn

/-- Supplemental: Verify that the function indeed takes the value ∞ (top)
when the random variables X, Y, Z are all zero. -/
lemma inverse_sqrt_sum_sq_at_zero {Ω : Type _} [MeasurableSpace Ω]
    (X Y Z : Ω → ℝ) (ω : Ω) (hx : X ω = 0) (hy : Y ω = 0) (hz : Z ω = 0) :
    (ENNReal.ofReal (Real.sqrt (X ω ^ 2 + Y ω ^ 2 + Z ω ^ 2)))⁻¹ = ⊤ := by
  simp [hx, hy, hz]