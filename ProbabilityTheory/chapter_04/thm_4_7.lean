/-
TASK ID: thm_4_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import ProbabilityTheory.chapter_04.def_4_3_sup_inf

open MeasureTheory



theorem measurable_seqSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqSup (fun i => f i ω)) := by
  simpa [seqSup] using (Measurable.iSup hf)




theorem measurable_seqInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqInf (fun i => f i ω)) := by
  simpa [seqInf] using (Measurable.iInf hf)



theorem thm_4_7 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  exact ⟨measurable_seqSupEReal f hf, measurable_seqInfEReal f hf⟩
