/-
TASK ID: def_10_6
TYPE: Definition
SOURCE PLAN: chapter10-random-vectors
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_10.thm_10_9




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory



def VectorConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
    ∀ ω ∈ E, Tendsto (fun n : ℕ => Vn n ω) atTop (nhds (V ω))



noncomputable def vectorEuclideanNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin d, (v i) ^ 2)



def vectorDeviationEvent {Ω : Type*} {d : ℕ} (Vn : ℕ → Ω → Fin d → ℝ)
    (V : Ω → Fin d → ℝ) (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω : Ω | vectorEuclideanNorm (Vn n ω - V ω) > ε}

 
def VectorConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => μ (vectorDeviationEvent Vn V n ε)) atTop (nhds 0)

 
def def_10_6 :=
  (@VectorConvergesAlmostSurely, @VectorConvergesInProbability)
