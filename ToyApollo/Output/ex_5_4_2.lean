/-
TASK ID: ex_5_4_2
TYPE: Example_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Support.IIDWord

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

section MonkeyTyping

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]
variable {n : ℕ} [NeZero n]

theorem ex_5_4_2 (w : Fin n → α) :
    typingMeasure (α := α) (limsup (wordEvent (α := α) n w) atTop) = 1 := by
  exact typingMeasure_limsup_wordEvent_eq_one (α := α) (n := n) w

end MonkeyTyping
