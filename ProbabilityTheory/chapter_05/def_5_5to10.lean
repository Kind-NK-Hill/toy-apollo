/-
TASK ID: def_5_5to10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic



def def_5_5 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ



def def_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) μ)




def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ



def def_5_8 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (X : Fin n → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ



def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ




def def_5_10 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : ℕ → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ



def def_5_10_randomVariables {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
