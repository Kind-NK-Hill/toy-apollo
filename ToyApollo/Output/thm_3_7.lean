/-
TASK ID: thm_3_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_10
import Mathlib.MeasureTheory.PiSystem

open MeasurableSpace

theorem PiSystem.toIsPiSystem {Ω : Type*} {P : Set (Set Ω)}
    (hP : PiSystem P) : IsPiSystem P := by
  intro A hA B hB _h_nonempty
  exact hP hA hB

def LambdaSystem.toDynkinSystem {Ω : Type*} {L : Set (Set Ω)}
    (hL : LambdaSystem L) : MeasurableSpace.DynkinSystem Ω where
  Has := fun s => s ∈ L
  has_empty := by
    have hcompl : (Set.univ : Set Ω)ᶜ ∈ L := hL.compl_mem hL.univ_mem
    simpa using hcompl
  has_compl := by
    intro s hs
    exact hL.compl_mem hs
  has_iUnion_nat := by
    intro f hdis hmem
    exact hL.iUnion_mem hdis hmem

@[simp] theorem LambdaSystem.toDynkinSystem_has
    {Ω : Type*} {L : Set (Set Ω)} (hL : LambdaSystem L) (s : Set Ω) :
    (hL.toDynkinSystem).Has s ↔ s ∈ L :=
  Iff.rfl

theorem thm_3_7 {α : Type*} {P : Set (Set α)} {L : DynkinSystem α}
    (hP : IsPiSystem P) (hPL : ∀ s ∈ P, L.Has s) :
    ∀ s, @MeasurableSet α (generateFrom P) s → L.Has s := by
  intro s hs
  have h := DynkinSystem.generateFrom_eq hP
  rw [h] at hs
  change (DynkinSystem.generate P).Has s at hs
  have key : DynkinSystem.generate P ≤ L := DynkinSystem.generate_le L hPL
  exact (DynkinSystem.le_def.mp key) s hs

theorem thm_3_7_textbook {Ω : Type*} {P L : Set (Set Ω)}
    (hP : PiSystem P) (hL : LambdaSystem L) (hPL : P ⊆ L) :
    ∀ s, @MeasurableSet Ω (MeasurableSpace.generateFrom P) s → s ∈ L := by
  have hP_mathlib : IsPiSystem P := PiSystem.toIsPiSystem hP
  have hPL_dynkin : ∀ s ∈ P, (hL.toDynkinSystem).Has s := by
    intro s hs
    exact (LambdaSystem.toDynkinSystem_has hL s).2 (hPL hs)
  intro s hs
  have hs_dynkin : (hL.toDynkinSystem).Has s :=
    thm_3_7 (P := P) (L := hL.toDynkinSystem)
      hP_mathlib hPL_dynkin s hs
  exact (LambdaSystem.toDynkinSystem_has hL s).1 hs_dynkin
