import Mathlib.Data.Set.Basic

/-!
# 4.2 Composition of Measurable Functions

Given a function `f` mapping from domain `Ω` to `Ω'`, the inverse image
of a set `A` in `Ω'` is defined as the set of elements `x ∈ Ω` such that `f(x) ∈ A`, i.e.,
`f⁻¹(A) ≜ {x ∈ Ω : f(x) ∈ A}`.

We remark that the function `f` need not be an injective function. 
The mapping above is defined for any function `f`.
-/

universe u v

section InverseImageDefinition

variable {Ω : Type u} {Ω' : Type v}

/-- The definition of the inverse image of a set under a function. -/
def inverse_image (f : Ω → Ω') (A : Set Ω') : Set Ω :=
  {x : Ω | f x ∈ A}

-- Standard Lean notation for preimage is `f ⁻¹' A`.
-- We can define the specific LaTeX-style notation requested:
notation f "⁻¹(" A ")" => inverse_image f A

/-- 
Remark: The function `f` need not be an injective function. 
The mapping above is defined for any function `f`.
-/
example (f : Ω → Ω') (A : Set Ω') : Set Ω := f⁻¹(A)

-- Proof that our definition matches Mathlib's built-in preimage notation
example (f : Ω → Ω') (A : Set Ω') : inverse_image f A = f ⁻¹' A := 
  rfl

end InverseImageDefinition