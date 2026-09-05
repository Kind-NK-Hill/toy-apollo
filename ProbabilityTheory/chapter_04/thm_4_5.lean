/-
TASK ID: thm_4_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2




section Theorem_4_5

open MeasureTheory



theorem continuous_to_borel_measurable {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) : Measurable f :=
  -- In Mathlib, a continuous function between topological spaces is
  -- measurable with respect to their Borel σ-algebras.
  hf.measurable



theorem continuous_preimage_borel {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B) :=
  -- `hf.measurable` is of type `Measurable f`, which by definition
  -- means `∀ B, MeasurableSet B → MeasurableSet (f ⁻¹' B)`.
  hf.measurable hB



example {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Continuous f) : Measurable f :=
  hf.measurable


end Theorem_4_5
