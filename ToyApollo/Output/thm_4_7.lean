import Mathlib
import ToyApollo.Output.def_4_3_sup_inf

open MeasureTheory

/-!
Theorem 4.7: measurability of pointwise supremum and infimum of a countable
family of measurable `EReal`-valued functions.
-/

theorem measurable_seqSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqSup (fun i => f i ω)) := by
  simpa [seqSup] using (Measurable.iSup hf)

theorem measurable_seqInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqInf (fun i => f i ω)) := by
  simpa [seqInf] using (Measurable.iInf hf)

/-- Textbook theorem 4.7 in bundled form. -/
theorem thm_4_7 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  exact ⟨measurable_seqSupEReal f hf, measurable_seqInfEReal f hf⟩
