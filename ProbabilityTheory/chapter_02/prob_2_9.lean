/-
TASK ID: prob_2_9
TYPE: Problem
SOURCE PLAN: 45_chap2_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open Set MeasureTheory Classical
open scoped MeasureTheory

noncomputable section

 
def atom {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (f : Fin n → Bool) : Set Ω :=
  ⋂ i : Fin n, if f i then A i else (A i)ᶜ

 
def atoms {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) : Finset (Set Ω) :=
  (Finset.univ.image (atom A)).filter (· ≠ ∅)

lemma atom_disjoint {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω)
    (f g : Fin n → Bool) (hfg : f ≠ g) : atom A f ∩ atom A g = ∅ := by
  simp +decide only [atom]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
  ext x
  simp +decide [hi]
  grind

lemma atom_union_univ {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    ⋃ f : Fin n → Bool, atom A f = Set.univ := by
  ext x
  simp [atom]
  exact ⟨fun i => if x ∈ A i then Bool.true else Bool.false,
    fun i => by by_cases hi : x ∈ A i <;> simp +decide [hi]⟩

lemma atom_measurable {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (f : Fin n → Bool) :
    @MeasurableSet Ω (MeasurableSpace.generateFrom (Set.range A)) (atom A f) := by
  unfold atom
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
  · exact (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)).compl

lemma set_eq_union_atoms {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (i : Fin n) :
    A i = ⋃ (f : Fin n → Bool) (_ : f i = true), atom A f := by
  ext x
  simp [atom]
  exact ⟨fun hx => ⟨fun j => if j = i then true else x ∈ A j, by aesop⟩,
    by rintro ⟨f, hf, hf'⟩; specialize hf' i; aesop⟩

lemma atoms_pairwise_disjoint {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    ∀ s ∈ atoms A, ∀ t ∈ atoms A, s ≠ t → s ∩ t = ∅ := by
  intros s hs t ht hst
  obtain ⟨f, hf⟩ : ∃ f : Fin n → Bool, s = atom A f := by
    unfold atoms at hs
    aesop
  obtain ⟨g, hg⟩ : ∃ g : Fin n → Bool, t = atom A g := by
    unfold atoms at ht
    aesop
  exact hf.symm ▸ hg.symm ▸ atom_disjoint A f g (by aesop)

lemma atoms_union_univ {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    ⋃ s ∈ atoms A, s = Set.univ := by
  simp +decide only [Set.ext_iff, mem_iUnion]
  simp +decide [atoms]
  exact fun x => by
    rcases Set.mem_iUnion.1 (atom_union_univ A ▸ Set.mem_univ x) with ⟨a, ha⟩
    exact ⟨a, Set.Nonempty.ne_empty ⟨x, ha⟩, ha⟩

lemma atoms_nonempty {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    ∀ s ∈ atoms A, s ≠ ∅ :=
  fun s hs => (Finset.mem_filter.mp hs).2

lemma atoms_card_le {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    (atoms A).card ≤ 2 ^ n := by
  exact le_trans (Finset.card_filter_le _ _)
    (Finset.card_image_le.trans_eq (Finset.card_univ.trans (by norm_num)))

lemma measurableSet_iff_union_atoms {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    let M := MeasurableSpace.generateFrom (Set.range A)
    ∀ s : Set Ω, @MeasurableSet Ω M s ↔
      ∃ I : Finset (Set Ω), I ⊆ atoms A ∧ s = ⋃ t ∈ I, t := by
  refine fun s => ⟨fun hs => ?_, ?_⟩
  · induction hs
    · rename_i s hs
      obtain ⟨i, hi⟩ : ∃ i : Fin n, s = A i := by
        simpa [eq_comm] using hs
      use Finset.filter (fun t => ∃ f : Fin n → Bool, f i = true ∧ t = atom A f)
        (atoms A)
      simp +decide [hi, set_eq_union_atoms]
      ext x
      simp [atoms]
      grind
    · exact ⟨∅, Finset.empty_subset _, by simp +decide⟩
    · obtain ⟨I, hI, rfl⟩ := ‹_›
      refine ⟨atoms A \ I, ?_, ?_⟩
      · grind
      · ext x
        simp +decide [Set.ext_iff]
        constructor
        · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp (atoms_union_univ A ▸ Set.mem_univ x)
          aesop
        · rintro ⟨t, ⟨ht₁, ht₂⟩, hx⟩ i hi
          have := atoms_pairwise_disjoint A t ht₁ i (hI hi)
          exact fun hx' =>
            Set.notMem_empty x (this (by rintro rfl; exact ht₂ hi) ▸ Set.mem_inter hx hx')
    · choose! I hI using ‹∀ n, ∃ I ⊆ atoms A, _›
      have h_finite_union : Set.Finite (⋃ n, I n : Set (Set Ω)) :=
        Set.Finite.subset (Finset.finite_toSet (atoms A)) (Set.iUnion_subset fun n => (hI n).1)
      refine ⟨h_finite_union.toFinset, ?_, ?_⟩ <;> aesop
  · simp +zetaDelta at *
    rintro x hx rfl
    exact MeasurableSet.biUnion ( Finset.countable_toSet x ) fun t ht => by simpa using atom_measurable A ( Classical.choose ( Finset.mem_image.mp ( hx ht |> fun h => Finset.mem_filter.mp h |>.1 ) ) ) |> fun h => by simpa only [ Classical.choose_spec ( Finset.mem_image.mp ( hx ht |> fun h => Finset.mem_filter.mp h |>.1 ) ) ] using h

lemma generated_measurable_sets_ncard_le {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) :
    {s : Set Ω | @MeasurableSet Ω (MeasurableSpace.generateFrom (Set.range A)) s}.ncard ≤
      2 ^ (2 ^ n) := by
  let U : Finset (Set Ω) := (atoms A).powerset.image fun I => ⋃ t ∈ I, t
  have hsubset :
      {s : Set Ω | @MeasurableSet Ω (MeasurableSpace.generateFrom (Set.range A)) s} ⊆
        (U : Set (Set Ω)) := by
    intro s hs
    change @MeasurableSet Ω (MeasurableSpace.generateFrom (Set.range A)) s at hs
    have hiff := (measurableSet_iff_union_atoms A) s
    rw [hiff] at hs
    rcases hs with ⟨I, hI, rfl⟩
    change (⋃ t ∈ I, t) ∈ U
    exact Finset.mem_image.mpr ⟨I, by simpa [Finset.mem_powerset] using hI, rfl⟩
  have h₁ :
      {s : Set Ω | @MeasurableSet Ω (MeasurableSpace.generateFrom (Set.range A)) s}.ncard
        ≤ U.card := by
    have h := Set.ncard_le_ncard hsubset (Finset.finite_toSet U)
    simpa using h
  have h₂ : U.card ≤ ((atoms A).powerset).card :=
    Finset.card_image_le
  have h₃ : ((atoms A).powerset).card = 2 ^ (atoms A).card :=
    Finset.card_powerset (atoms A)
  have h₄ : 2 ^ (atoms A).card ≤ 2 ^ (2 ^ n) :=
    Nat.pow_le_pow_right (by norm_num) (atoms_card_le A)
  exact le_trans h₁ (le_trans h₂ (by rw [h₃]; exact h₄))

theorem prob_2_9 (Ω : Type*) (n : ℕ) (A : Fin n → Set Ω) :
    let M : MeasurableSpace Ω := MeasurableSpace.generateFrom (Set.range A)
    ∃ 𝒜 : Finset (Set Ω),
      (∀ s ∈ 𝒜, s ≠ ∅) ∧
      (∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → s ∩ t = ∅) ∧
      (⋃ s ∈ 𝒜, s) = Set.univ ∧
      (∀ s : Set Ω, @MeasurableSet Ω M s ↔
        ∃ I : Finset (Set Ω), I ⊆ 𝒜 ∧ s = ⋃ t ∈ I, t) ∧
      𝒜.card ≤ 2 ^ n ∧
      {s : Set Ω | @MeasurableSet Ω M s}.ncard ≤ 2 ^ (2 ^ n) := by
  intro M
  exact ⟨atoms A,
    atoms_nonempty A,
    atoms_pairwise_disjoint A,
    atoms_union_univ A,
    measurableSet_iff_union_atoms A,
    atoms_card_le A,
    generated_measurable_sets_ncard_le A⟩
