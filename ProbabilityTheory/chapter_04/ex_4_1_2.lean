/-
TASK ID: ex_4_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_04.def_4_1
import Mathlib

open MeasureTheory

inductive Omega : Type
  | a | b | c | d | e
  deriving Fintype, DecidableEq

instance : MeasurableSpace Omega := ⊤
instance : MeasurableSingletonClass Omega := ⟨fun _ => trivial⟩

 
noncomputable def exP : Measure Omega := (1 / 5 : ENNReal) • Measure.count

 
noncomputable def exX : Omega → ℝ
  | Omega.a => 1
  | Omega.b => 2
  | Omega.c => 3
  | Omega.d => 4
  | Omega.e => 5

 
noncomputable def exY : Omega → ℝ
  | Omega.a => 0
  | Omega.b => 3
  | Omega.c => 2
  | Omega.d => -1
  | Omega.e => 5

 
def lookupPair : Omega → ℝ × ℝ
  | Omega.a => (1, 0)
  | Omega.b => (2, 3)
  | Omega.c => (3, 2)
  | Omega.d => (4, -1)
  | Omega.e => (5, 5)



theorem ex_4_1_2 :
    IsRealMeasurable exX ∧
      IsRealMeasurable exY ∧
      ∀ ω : Omega, (exX ω, exY ω) = lookupPair ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    trivial
  · intro B hB
    trivial
  · intro ω
    cases ω <;> rfl
