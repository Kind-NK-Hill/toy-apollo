/-
TASK ID: def_4_2_inverse_image
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Set.Basic




universe u v

section InverseImageDefinition

variable {Ω : Type u} {Ω' : Type v}



def inverse_image (f : Ω → Ω') (A : Set Ω') : Set Ω :=
  {x : Ω | f x ∈ A}

-- custom notation for inverse image
notation f "⁻¹(" A ")" => inverse_image f A



example (f : Ω → Ω') (A : Set Ω') : Set Ω := f⁻¹( A )

-- Lean notation for preimage is `f ⁻¹' A`.
-- Proof that our definition matches Mathlib's built-in preimage notation
example (f : Ω → Ω') (A : Set Ω') : inverse_image f A = f ⁻¹' A :=
  rfl

end InverseImageDefinition
