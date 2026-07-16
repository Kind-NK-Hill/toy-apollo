/-
TASK ID: thm_4_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_3_sup_inf
import ToyApollo.Output.thm_4_4

open Set MeasureTheory

noncomputable section

def erealLowerRays : Set (Set EReal) :=
  Set.range (fun a : EReal => Iic a)

theorem erealLowerRays_generateFrom_eq_borel :
    MeasurableSpace.generateFrom erealLowerRays = borel EReal := by
  simpa [erealLowerRays] using (borel_eq_generateFrom_Iic EReal).symm

theorem measurable_of_erealLowerRays_preimage {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → EReal}
    (hF : ∀ A ∈ erealLowerRays, MeasurableSet (F ⁻¹' A)) :
    Measurable F := by
  have hgen :
      (inferInstance : MeasurableSpace EReal) =
        MeasurableSpace.generateFrom erealLowerRays := by
    calc
      (inferInstance : MeasurableSpace EReal) = borel EReal := BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom erealLowerRays :=
        erealLowerRays_generateFrom_eq_borel.symm
  have hsrc :
      @Measurable Ω EReal inferInstance
        (MeasurableSpace.generateFrom erealLowerRays) F :=
    (thm_4_4 F).2 hF
  convert hsrc using 1

theorem seqSup_levelSet_eq_iInter {Ω : Type*} (f : ℕ → Ω → EReal) (a : EReal) :
    {ω | seqSup (fun i => f i ω) ≤ a} = ⋂ i, {ω | f i ω ≤ a} := by
  ext ω
  simp [seqSup]

theorem seqSup_levelSet_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → EReal) (hf : ∀ i, Measurable (f i)) (a : EReal) :
    MeasurableSet {ω | seqSup (fun i => f i ω) ≤ a} := by
  rw [seqSup_levelSet_eq_iInter f a]
  exact MeasurableSet.iInter fun i => hf i measurableSet_Iic

theorem measurable_seqSupEReal {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → EReal) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) := by
  refine measurable_of_erealLowerRays_preimage ?_
  rintro A ⟨a, rfl⟩
  exact seqSup_levelSet_measurable f hf a

theorem seqInf_eq_neg_seqSup_neg (a : ℕ → EReal) :
    seqInf a = -(seqSup fun i => -a i) := by
  unfold seqInf seqSup
  apply le_antisymm
  · exact EReal.le_neg.mpr
      (iSup_le fun i => EReal.neg_le_neg_iff.mpr (iInf_le a i))
  · refine le_iInf ?_
    intro i
    exact EReal.neg_le.mpr (le_iSup (fun j : ℕ => -a j) i)

theorem measurable_seqInfEReal {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → EReal) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqInf (fun i => f i ω)) := by
  have hneg : ∀ i, Measurable (fun ω => -f i ω) := fun i => (hf i).neg
  have hsup :
      Measurable (fun ω => seqSup (fun i => -f i ω)) :=
    measurable_seqSupEReal (fun i ω => -f i ω) hneg
  have hfinal : Measurable (fun ω => -(seqSup (fun i => -f i ω))) := hsup.neg
  convert hfinal using 1
  ext ω
  exact seqInf_eq_neg_seqSup_neg (fun i => f i ω)

theorem thm_4_7 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  exact ⟨measurable_seqSupEReal f hf, measurable_seqInfEReal f hf⟩
