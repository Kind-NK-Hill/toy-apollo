/-
TASK ID: thm_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import ProbabilityTheory.chapter_03.def_3_1
import ProbabilityTheory.chapter_03.def_3_2




open Set MeasureTheory ENNReal



theorem thm_3_1 {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    ∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀.carrier pm.toSetFunction μ := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom F₀.carrier
  let μ : Measure X :=
    pm.toAddContent.measure F₀.isSetRing.isSetSemiring le_rfl
      pm.toAddContent_isSigmaSubadditive
  refine ⟨μ, ?_⟩
  intro s hs
  calc
    μ s = pm.toAddContent s :=
      AddContent.measure_eq pm.toAddContent F₀.isSetRing.isSetSemiring rfl
        pm.toAddContent_isSigmaSubadditive hs
    _ = pm.toSetFunction s := rfl
