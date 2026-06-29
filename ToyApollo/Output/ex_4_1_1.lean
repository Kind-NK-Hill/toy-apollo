import Mathlib.MeasureTheory.MeasurableSpace.Basic

universe u v

/-- 
Example 4.1.1 (Measurable Functions) - Part 1:
If ℱ is the trivial σ-field {∅, Ω}, and 𝒢 is a σ-field in which all singletons are 
𝒢-measurable, then an (ℱ, 𝒢)-measurable function is a constant function.
-/
theorem example_4_1_1_part1 {α : Type u} {β : Type v} [mG : MeasurableSpace β] 
    (hG : ∀ y : β, MeasurableSet {y}) (f : α → β) (hf : @Measurable α β ⊥ mG f) [Nonempty α] :
    ∃ c : β, ∀ x : α, f x = c := by
  -- Let x0 be an arbitrary element of α and c be its image f(x0).
  let x0 := Classical.arbitrary α
  let c := f x0
  use c
  intro x
  -- We set the local instance of MeasurableSpace α to be ⊥ (the trivial σ-algebra).
  letI mF : MeasurableSpace α := ⊥
  -- Because f is measurable from (α, ⊥) to (β, mG), the preimage of {c} 
  -- must be measurable in the trivial σ-algebra ⊥.
  have h_pre : MeasurableSet (f ⁻¹' {c}) := hf (hG c)
  
  -- In the trivial σ-algebra ⊥, the only measurable sets are ∅ and univ.
  rw [MeasurableSpace.measurableSet_bot_iff] at h_pre
  cases h_pre with
  | inl h_empty =>
    -- The preimage cannot be empty because it contains x0 by definition of c.
    have h_mem : x0 ∈ f ⁻¹' {c} := Set.mem_singleton (f x0)
    rw [h_empty] at h_mem
    -- x0 ∈ ∅ is False.
    contradiction
  | inr h_univ =>
    -- Since the preimage is the entire set α, every x must map to c.
    have h_mem : x ∈ f ⁻¹' {c} := by rw [h_univ]; exact Set.mem_univ x
    -- x ∈ f ⁻¹' {c} implies f x = c.
    exact Set.mem_singleton_iff.mp h_mem

/-- 
Example 4.1.1 (Measurable Functions) - Part 2:
If ℱ is the power set 𝒫(Ω), then no matter what 𝒢 is, all (ℱ, 𝒢) functions 
from Ω to Ω' are measurable.
-/
theorem example_4_1_1_part2 {α : Type u} {β : Type v} [mG : MeasurableSpace β] (f : α → β) :
    @Measurable α β ⊤ mG f := by
  -- We set the local instance of MeasurableSpace α to be ⊤ (the power set σ-algebra).
  letI mF : MeasurableSpace α := ⊤
  -- A function is measurable if the preimage of every measurable set is measurable.
  intro s _
  -- In the top σ-algebra ⊤, every subset is measurable by definition.
  exact MeasurableSpace.measurableSet_top