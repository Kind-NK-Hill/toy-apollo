/-
TASK ID: def_2_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic









open Set



def SetSeqIncreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Monotone A



def SetSeqDecreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Antitone A





def def_2_6 {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  SetSeqIncreasing A
