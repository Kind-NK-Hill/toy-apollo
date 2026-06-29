/-
TASK ID: def_13_4
TYPE: Definition
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

@[reducible]
def def_13_4_sigma {Ω S : Type*} [MeasurableSpace S] (Y : Ω → S) :
    SigmaField Ω :=
  (inferInstance : MeasurableSpace S).comap Y

theorem def_13_4_sigma_subSigma_of_measurable {Ω S : Type*}
    [𝓕 : MeasurableSpace Ω] [MeasurableSpace S] {Y : Ω → S}
    (hY : Measurable Y) :
    IsSubSigmaField (def_13_4_sigma Y) 𝓕 := by
  intro A hA
  exact hY.comap_le A hA

def def_13_4 {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Y : Ω → S)
    (hσY : IsSubSigmaField (def_13_4_sigma Y) 𝓕)
    (X CE : Ω → ℝ) : Prop :=
  @def_13_3 Ω 𝓕 P (def_13_4_sigma Y) hσY X CE

@[reducible]
def def_13_4_pairSigma {Ω S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T] (Y : Ω → S) (Z : Ω → T) :
    SigmaField Ω :=
  (inferInstance : MeasurableSpace (S × T)).comap (fun ω => (Y ω, Z ω))

theorem def_13_4_pairSigma_subSigma_of_measurable {Ω S T : Type*}
    [𝓕 : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    {Y : Ω → S} {Z : Ω → T} (hY : Measurable Y) (hZ : Measurable Z) :
    IsSubSigmaField (def_13_4_pairSigma Y Z) 𝓕 := by
  intro A hA
  exact (hY.prodMk hZ).comap_le A hA

def def_13_4_pair {Ω S T : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] (P : Measure Ω)
    (Y : Ω → S) (Z : Ω → T)
    (hσYZ : IsSubSigmaField (def_13_4_pairSigma Y Z) 𝓕)
    (X CE : Ω → ℝ) : Prop :=
  @def_13_3 Ω 𝓕 P (def_13_4_pairSigma Y Z) hσYZ X CE

@[reducible]
def def_13_4_familySigma {Ω I : Type*} {S : I → Type*}
    [∀ i, MeasurableSpace (S i)] (Y : ∀ i, Ω → S i) : SigmaField Ω :=
  (inferInstance : MeasurableSpace ((i : I) → S i)).comap
    (fun ω i => Y i ω)

def def_13_4_family {Ω I : Type*} {S : I → Type*}
    [𝓕 : MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
    (P : Measure Ω) (Y : ∀ i, Ω → S i)
    (hσY : IsSubSigmaField (def_13_4_familySigma Y) 𝓕)
    (X CE : Ω → ℝ) : Prop :=
  @def_13_3 Ω 𝓕 P (def_13_4_familySigma Y) hσY X CE
