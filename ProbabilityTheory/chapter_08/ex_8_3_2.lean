/-
TASK ID: ex_8_3_2
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_03.ex_3_3_4




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

 
noncomputable def finiteAtomicMeasure {n : ℕ} (z : Fin n → ℝ) : Measure ℝ :=
  ∑ i : Fin n, Measure.dirac (z i)

 
noncomputable abbrev finiteMongeSourceMeasure {n : ℕ} (x : Fin n → ℝ) : Measure ℝ :=
  finiteAtomicMeasure x

 
noncomputable abbrev finiteMongeTargetMeasure {n : ℕ} (y : Fin n → ℝ) : Measure ℝ :=
  finiteAtomicMeasure y

 
def finiteMongeCost {n : ℕ} (x y : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, (x i - y (π i)) ^ 2



noncomputable def finitePermutationMongeMap {n : ℕ} (x y : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (z : ℝ) : ℝ :=
  ∑ i : Fin n, Set.indicator ({x i} : Set ℝ) (fun _ ↦ y (π i)) z

 
noncomputable def finiteMongeIntegralCost {n : ℕ} (x : Fin n → ℝ) (T : ℝ → ℝ) : ℝ :=
  ∫ z, (z - T z) ^ 2 ∂finiteMongeSourceMeasure x



def IsFiniteMongeMap {n : ℕ} (x y : Fin n → ℝ) (T : ℝ → ℝ) : Prop :=
  Measurable T ∧
    Measure.map T (finiteMongeSourceMeasure x) = finiteMongeTargetMeasure y

lemma measurable_finitePermutationMongeMap {n : ℕ} (x y : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : Measurable (finitePermutationMongeMap x y π) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator (measurableSet_singleton (x i))

lemma finitePermutationMongeMap_apply {n : ℕ} {x y : Fin n → ℝ}
    (hx : Function.Injective x) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    finitePermutationMongeMap x y π (x i) = y (π i) := by
  classical
  simp only [finitePermutationMongeMap]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp only [Set.indicator, Set.mem_singleton_iff]
    split_ifs with h
    · exact (hji (hx h.symm)).elim
    · rfl

lemma finitePermutationMongeMap_pushforward {n : ℕ} {x y : Fin n → ℝ}
    (hx : Function.Injective x) (π : Equiv.Perm (Fin n)) :
    Measure.map (finitePermutationMongeMap x y π) (finiteAtomicMeasure x) =
      finiteAtomicMeasure y := by
  classical
  rw [finiteAtomicMeasure, Measure.map_finset_sum'
    (measurable_finitePermutationMongeMap x y π).aemeasurable]
  simp_rw [Measure.map_dirac' (measurable_finitePermutationMongeMap x y π),
    finitePermutationMongeMap_apply hx]
  exact Fintype.sum_equiv π _ _ (fun _ ↦ rfl)

lemma finitePermutation_isFiniteMongeMap {n : ℕ} {x y : Fin n → ℝ}
    (hx : Function.Injective x) (π : Equiv.Perm (Fin n)) :
    IsFiniteMongeMap x y (finitePermutationMongeMap x y π) :=
  ⟨measurable_finitePermutationMongeMap x y π,
    finitePermutationMongeMap_pushforward hx π⟩



lemma finiteMongeMap_corresponds_toPermutation {n : ℕ} {x y : Fin n → ℝ}
    (hy : Function.Injective y) {T : ℝ → ℝ} (hT : IsFiniteMongeMap x y T)
    (τ : Fin n → Fin n) (hτ : ∀ i, T (x i) = y (τ i)) :
    ∃! π : Equiv.Perm (Fin n), ∀ i, T (x i) = y (π i) := by
  classical
  have hτ_surjective : Function.Surjective τ := by
    intro j
    by_contra hj
    have hτj : ∀ i, τ i ≠ j := by
      intro i hij
      exact hj ⟨i, hij⟩
    have hleft : Measure.map T (finiteAtomicMeasure x) ({y j} : Set ℝ) = 0 := by
      rw [Measure.map_apply hT.1 (measurableSet_singleton (y j))]
      simp [finiteAtomicMeasure, hτ, hy.eq_iff, hτj]
    have hright : finiteAtomicMeasure y ({y j} : Set ℝ) = 1 := by
      simp [finiteAtomicMeasure, Pi.single_apply, hy.eq_iff]
    have h := congrArg (fun μ : Measure ℝ ↦ μ ({y j} : Set ℝ)) hT.2
    rw [hleft, hright] at h
    exact zero_ne_one h
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective τ hτ_surjective.bijective_of_finite
  have hπ : ∀ i, T (x i) = y (π i) := by
    intro i
    exact hτ i
  refine ⟨π, hπ, ?_⟩
  intro σ hσ
  apply Equiv.ext
  intro i
  exact hy ((hσ i).symm.trans (hπ i))



lemma finiteMongeMap_hasUniquePermutation {n : ℕ} {x y : Fin n → ℝ}
    (hy : Function.Injective y) {T : ℝ → ℝ} (hT : IsFiniteMongeMap x y T) :
    ∃! π : Equiv.Perm (Fin n), ∀ i, T (x i) = y (π i) := by
  classical
  have hlands : ∀ i, ∃ j, T (x i) = y j := by
    intro i
    by_contra hi
    have hnot : ∀ j, T (x i) ≠ y j := by
      simpa only [not_exists] using hi
    have hmeasure : Measure.dirac (x i) ≤ finiteAtomicMeasure x := by
      rw [finiteAtomicMeasure]
      exact Finset.single_le_sum
        (fun j _ ↦ Measure.zero_le (Measure.dirac (x j))) (Finset.mem_univ i)
    let s : Set ℝ := {T (x i)}
    have hs : MeasurableSet s := measurableSet_singleton (T (x i))
    have hleft :
        (1 : ENNReal) ≤ Measure.map T (finiteAtomicMeasure x) s := by
      rw [Measure.map_apply hT.1 hs]
      calc
        (1 : ENNReal) = Measure.dirac (x i) (T ⁻¹' s) := by simp [s]
        _ ≤ finiteAtomicMeasure x (T ⁻¹' s) := hmeasure _
    have hright : finiteAtomicMeasure y s = 0 := by
      simp [finiteAtomicMeasure, hnot, s]
    have heq := congrArg (fun μ : Measure ℝ ↦ μ s) hT.2
    rw [hright] at heq
    rw [heq] at hleft
    exact (not_le_of_gt zero_lt_one) hleft
  let τ : Fin n → Fin n := fun i ↦ Classical.choose (hlands i)
  have hτ : ∀ i, T (x i) = y (τ i) := fun i ↦ Classical.choose_spec (hlands i)
  exact finiteMongeMap_corresponds_toPermutation hy hT τ hτ



lemma finiteMongeIntegralCost_eq_finiteMongeCost {n : ℕ} {x y : Fin n → ℝ}
    {T : ℝ → ℝ} (π : Equiv.Perm (Fin n)) (hT : ∀ i, T (x i) = y (π i)) :
    finiteMongeIntegralCost x T = finiteMongeCost x y π := by
  classical
  let f : ℝ → ℝ := fun z ↦ (z - T z) ^ 2
  have hf : ∀ i : Fin n, Integrable f (Measure.dirac (x i)) := by
    intro i
    exact integrable_dirac (by simp)
  rw [finiteMongeIntegralCost]
  change (∫ z, f z ∂finiteAtomicMeasure x) = finiteMongeCost x y π
  rw [finiteAtomicMeasure, integral_finsetSum_measure (fun i _ ↦ hf i)]
  simp only [integral_dirac, f, hT, finiteMongeCost]

lemma finitePermutationMongeCost_eq {n : ℕ} {x y : Fin n → ℝ}
    (hx : Function.Injective x) (π : Equiv.Perm (Fin n)) :
    finiteMongeIntegralCost x (finitePermutationMongeMap x y π) =
      finiteMongeCost x y π :=
  finiteMongeIntegralCost_eq_finiteMongeCost π
    (finitePermutationMongeMap_apply hx π)



lemma finiteMongeCost_exists_min {n : ℕ} [NeZero n] (x y : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ σ : Equiv.Perm (Fin n),
      finiteMongeCost x y π ≤ finiteMongeCost x y σ := by
  classical
  let cost : Equiv.Perm (Fin n) → ℝ := finiteMongeCost x y
  obtain ⟨π, hπ⟩ := Finite.exists_min cost
  exact ⟨π, hπ⟩



theorem ex_8_3_2 {n : ℕ} [NeZero n] (x y : Fin n → ℝ)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ (π : Equiv.Perm (Fin n)) (T : ℝ → ℝ),
      IsFiniteMongeMap x y T ∧
      (∀ i, T (x i) = y (π i)) ∧
      finiteMongeIntegralCost x T = finiteMongeCost x y π ∧
      (∀ σ : Equiv.Perm (Fin n), finiteMongeCost x y π ≤ finiteMongeCost x y σ) ∧
      ∀ S : ℝ → ℝ, IsFiniteMongeMap x y S →
        finiteMongeIntegralCost x T ≤ finiteMongeIntegralCost x S := by
  obtain ⟨π, hπ⟩ := finiteMongeCost_exists_min x y
  let T := finitePermutationMongeMap x y π
  have hT_atoms : ∀ i, T (x i) = y (π i) := finitePermutationMongeMap_apply hx π
  have hT_cost : finiteMongeIntegralCost x T = finiteMongeCost x y π :=
    finiteMongeIntegralCost_eq_finiteMongeCost π hT_atoms
  refine ⟨π, T, finitePermutation_isFiniteMongeMap hx π, hT_atoms, hT_cost, hπ, ?_⟩
  intro S hS
  obtain ⟨σ, hσ, -⟩ := finiteMongeMap_hasUniquePermutation hy hS
  calc
    finiteMongeIntegralCost x T = finiteMongeCost x y π := hT_cost
    _ ≤ finiteMongeCost x y σ := hπ σ
    _ = finiteMongeIntegralCost x S :=
      (finiteMongeIntegralCost_eq_finiteMongeCost σ hσ).symm
