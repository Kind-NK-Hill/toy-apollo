/-
TASK ID: def_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent




open Set ENNReal Function MeasureTheory



structure FieldOfSets (Ω : Type*) where
  carrier : Set (Set Ω)
  empty_mem : ∅ ∈ carrier
  compl_mem : ∀ s ∈ carrier, sᶜ ∈ carrier
  union_mem : ∀ s t, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier





structure Premeasure {Ω : Type*} (F₀ : FieldOfSets Ω) where
   
  μ₀ : {s : Set Ω // s ∈ F₀.carrier} → ℝ≥0∞

   
  map_empty : μ₀ ⟨∅, F₀.empty_mem⟩ = 0

  

  sigma_additive :
    ∀ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier)
    (hU : (⋃ i, A i) ∈ F₀.carrier),
    Pairwise (Disjoint on A) →
    μ₀ ⟨⋃ i, A i, hU⟩ = ∑' i, μ₀ ⟨A i, hA i⟩

namespace FieldOfSets

 
lemma inter_mem {Ω : Type*} (F₀ : FieldOfSets Ω) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s ∩ t ∈ F₀.carrier := by
  rw [show s ∩ t = (sᶜ ∪ tᶜ)ᶜ by ext x; simp]
  exact F₀.compl_mem _ (F₀.union_mem _ _ (F₀.compl_mem _ hs) (F₀.compl_mem _ ht))

 
lemma sdiff_mem {Ω : Type*} (F₀ : FieldOfSets Ω) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s \ t ∈ F₀.carrier := by
  rw [show s \ t = s ∩ tᶜ by ext x; simp]
  exact F₀.inter_mem hs (F₀.compl_mem _ ht)

 
lemma isSetRing {Ω : Type*} (F₀ : FieldOfSets Ω) : IsSetRing F₀.carrier where
  empty_mem := F₀.empty_mem
  union_mem := by
    intro s t hs ht
    exact F₀.union_mem s t hs ht
  sdiff_mem := by
    intro s t hs ht
    exact F₀.sdiff_mem hs ht

end FieldOfSets

namespace Premeasure

variable {Ω : Type*} {F₀ : FieldOfSets Ω}



noncomputable def toSetFunction (pm : Premeasure F₀) (s : Set Ω) : ℝ≥0∞ :=
  by
    classical
    exact if hs : s ∈ F₀.carrier then pm.μ₀ ⟨s, hs⟩ else 0

@[simp]
lemma toSetFunction_of_mem (pm : Premeasure F₀) {s : Set Ω} (hs : s ∈ F₀.carrier) :
    pm.toSetFunction s = pm.μ₀ ⟨s, hs⟩ := by
  classical
  simp only [toSetFunction, dif_pos hs]

@[simp]
lemma toSetFunction_empty (pm : Premeasure F₀) : pm.toSetFunction ∅ = 0 := by
  rw [pm.toSetFunction_of_mem F₀.empty_mem]
  exact pm.map_empty

 
lemma additive (pm : Premeasure F₀) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) (hst : Disjoint s t)
    (hut : s ∪ t ∈ F₀.carrier) :
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
  let A : ℕ → Set Ω := fun i => if i = 0 then s else if i = 1 then t else ∅
  have hA : ∀ i, A i ∈ F₀.carrier := by
    intro i
    rcases i with (_ | _ | i) <;> simp [A, hs, ht, F₀.empty_mem]
  have hUset : (⋃ i, A i) = s ∪ t := by
    ext x
    simp only [mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases i with (_ | _ | i) <;> simp_all [A]
    · intro hx
      exact hx.elim (fun hxs => ⟨0, by simpa [A] using hxs⟩)
        (fun hxt => ⟨1, by simpa [A] using hxt⟩)
  have hU : (⋃ i, A i) ∈ F₀.carrier := hUset ▸ hut
  have hdisj : Pairwise (Disjoint on A) := by
    intro i j hij
    rcases i with (_ | _ | i) <;> rcases j with (_ | _ | j) <;>
      simp_all [A, Function.onFun, hst.symm]
  have hsigma := pm.sigma_additive A hA hU hdisj
  calc
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨⋃ i, A i, hU⟩ :=
      congrArg pm.μ₀ (Subtype.ext hUset.symm)
    _ = ∑' i, pm.μ₀ ⟨A i, hA i⟩ := hsigma
    _ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
      rw [tsum_eq_sum (s := Finset.range 2)]
      · simp [A, Finset.sum_range_succ]
      · intro j hj
        simp only [Finset.mem_range, not_lt] at hj
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        simpa [A, hj0, hj1] using pm.map_empty

 
noncomputable def toAddContent (pm : Premeasure F₀) : AddContent ℝ≥0∞ F₀.carrier :=
  F₀.isSetRing.addContent_of_union pm.toSetFunction pm.toSetFunction_empty <| by
    intro s t hs ht hst
    rw [pm.toSetFunction_of_mem (F₀.union_mem _ _ hs ht),
      pm.toSetFunction_of_mem hs, pm.toSetFunction_of_mem ht]
    exact pm.additive hs ht hst (F₀.union_mem _ _ hs ht)

@[simp]
lemma toAddContent_apply (pm : Premeasure F₀) (s : Set Ω) :
    pm.toAddContent s = pm.toSetFunction s := rfl

 
lemma toAddContent_isSigmaSubadditive (pm : Premeasure F₀) :
    pm.toAddContent.IsSigmaSubadditive := by
  apply isSigmaSubadditive_of_addContent_iUnion_eq_tsum F₀.isSetRing
  intro f hf hU hdisj
  change pm.toSetFunction (⋃ i, f i) = ∑' i, pm.toSetFunction (f i)
  rw [pm.toSetFunction_of_mem hU]
  simp_rw [pm.toSetFunction_of_mem (hf _)]
  exact pm.sigma_additive f hf hU hdisj

end Premeasure
