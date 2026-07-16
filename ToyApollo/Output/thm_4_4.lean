/-
TASK ID: thm_4_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import ToyApollo.Output.thm_4_2

open MeasureTheory Set

universe u v

variable {Ω : Type u} {Ω' : Type v}

def preimageMeasurableSpace [mF : MeasurableSpace Ω] (f : Ω → Ω') :
    MeasurableSpace Ω' where
  MeasurableSet' B := @MeasurableSet Ω mF (f ⁻¹' B)
  measurableSet_empty := by
    simpa using (@MeasurableSet.empty Ω mF)
  measurableSet_compl B hB := by
    rw [preimage_compl_distrib (f := f) (A := B)]
    exact hB.compl
  measurableSet_iUnion B hB := by
    rw [preimage_iUnion_distrib (f := f) (Ai := B)]
    exact MeasurableSet.iUnion hB

theorem measurableSet_preimageMeasurableSpace_iff [mF : MeasurableSpace Ω]
    (f : Ω → Ω') (B : Set Ω') :
    @MeasurableSet Ω' (preimageMeasurableSpace (Ω := Ω) f) B ↔
      @MeasurableSet Ω mF (f ⁻¹' B) :=
  Iff.rfl

theorem preimageMeasurableSpace_eq_map [mF : MeasurableSpace Ω] (f : Ω → Ω') :
    preimageMeasurableSpace f = MeasurableSpace.map f mF := by
  ext B
  rfl

theorem generators_le_preimageMeasurableSpace [mF : MeasurableSpace Ω]
    {C : Set (Set Ω')} {f : Ω → Ω'}
    (hC : ∀ A ∈ C, @MeasurableSet Ω mF (f ⁻¹' A)) :
    MeasurableSpace.generateFrom C ≤ preimageMeasurableSpace f := by
  exact MeasurableSpace.generateFrom_le (fun A hA => hC A hA)

theorem measurable_of_generators_preimage [mF : MeasurableSpace Ω]
    {C : Set (Set Ω')} {f : Ω → Ω'}
    (hC : ∀ A ∈ C, @MeasurableSet Ω mF (f ⁻¹' A)) :
    @Measurable Ω Ω' mF (MeasurableSpace.generateFrom C) f := by
  have hH :
      MeasurableSpace.generateFrom C ≤ preimageMeasurableSpace f :=
    generators_le_preimageMeasurableSpace (f := f) hC
  have hMap :
      MeasurableSpace.generateFrom C ≤ MeasurableSpace.map f mF := by
    simpa [preimageMeasurableSpace_eq_map (f := f)] using hH
  exact Measurable.of_le_map hMap

theorem measurable_iff_preimage_generating_set
    [mF : MeasurableSpace Ω]
    {C : Set (Set Ω')}
    (f : Ω → Ω') :
    @Measurable Ω Ω' mF (MeasurableSpace.generateFrom C) f ↔
    ∀ A ∈ C, MeasurableSet (f ⁻¹' A) := by
  constructor
  · -- Forward direction: preimages of all sigma(C)-measurable sets are measurable.
    intro hf A hA
    apply hf
    exact MeasurableSpace.measurableSet_generateFrom hA
  · -- Backward direction follows the textbook `H` construction and minimality of σ(C).
    intro hA
    exact measurable_of_generators_preimage (f := f) hA

theorem thm_4_4
    [mF : MeasurableSpace Ω]
    {C : Set (Set Ω')}
    (f : Ω → Ω') :
    @Measurable Ω Ω' mF (MeasurableSpace.generateFrom C) f ↔
    ∀ A ∈ C, MeasurableSet (f ⁻¹' A) :=
  measurable_iff_preimage_generating_set f

theorem measurable_iff_preimage_generating_set_of_eq_generateFrom
    [mF : MeasurableSpace Ω]
    [mG : MeasurableSpace Ω']
    {C : Set (Set Ω')}
    (hG : mG = MeasurableSpace.generateFrom C)
    (f : Ω → Ω') :
    Measurable f ↔ ∀ A ∈ C, MeasurableSet (f ⁻¹' A) := by
  rw [hG]
  exact measurable_iff_preimage_generating_set f
