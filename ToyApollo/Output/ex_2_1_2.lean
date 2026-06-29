/-
TASK ID: ex_2_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import Mathlib.Analysis.Real.Cardinality
import ToyApollo.Output.def_2_1

open Set
open scoped BigOperators

noncomputable section

def diagonalFlip (F : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun n => !(F n n)

theorem diagonalFlip_ne_row (F : ℕ → ℕ → Bool) (n : ℕ) :
    diagonalFlip F ≠ F n := by
  intro h
  have hcoord := congrArg (fun s : ℕ → Bool => s n) h
  simp [diagonalFlip] at hcoord

def binaryExpansionValue (s : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, if s n then (1 / 2 : ℝ) ^ (n + 1) else 0

def cantorIntervalValue (s : ℕ → Bool) : ℝ :=
  (1 / 2 : ℝ) * Cardinal.cantorFunction (1 / 3 : ℝ) s

theorem cantorFunction_one_third_false :
    Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => false) = 0 := by
  simp [Cardinal.cantorFunction, Cardinal.cantorFunctionAux]

theorem cantorFunction_one_third_true :
    Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => true) = (3 / 2 : ℝ) := by
  rw [Cardinal.cantorFunction]
  have hterm :
      (fun n : ℕ => Cardinal.cantorFunctionAux (1 / 3 : ℝ) (fun _ : ℕ => true) n) =
        fun n : ℕ => (1 / 3 : ℝ) ^ n := by
    ext n
    simp [Cardinal.cantorFunctionAux]
  rw [hterm, tsum_geometric_of_lt_one]
  · norm_num
  · norm_num
  · norm_num

theorem cantorFunction_one_third_nonneg (s : ℕ → Bool) :
    0 ≤ Cardinal.cantorFunction (1 / 3 : ℝ) s := by
  have hle := Cardinal.cantorFunction_le
    (c := (1 / 3 : ℝ)) (f := fun _ : ℕ => false) (g := s)
    (by norm_num) (by norm_num)
    (by intro n h; cases h)
  rw [cantorFunction_one_third_false] at hle
  exact hle

theorem cantorFunction_one_third_le_three_halves (s : ℕ → Bool) :
    Cardinal.cantorFunction (1 / 3 : ℝ) s ≤ (3 / 2 : ℝ) := by
  have hle := Cardinal.cantorFunction_le
    (c := (1 / 3 : ℝ)) (f := s) (g := fun _ : ℕ => true)
    (by norm_num) (by norm_num)
    (by intro n h; trivial)
  rwa [cantorFunction_one_third_true] at hle

def cantorIntervalEmbedding (s : ℕ → Bool) : Set.Icc (0 : ℝ) 1 :=
  ⟨cantorIntervalValue s, by
    constructor
    · have hnonneg := cantorFunction_one_third_nonneg s
      dsimp [cantorIntervalValue]
      nlinarith [hnonneg]
    · have hle := cantorFunction_one_third_le_three_halves s
      dsimp [cantorIntervalValue]
      nlinarith [hle]⟩

theorem cantorIntervalEmbedding_injective :
    Function.Injective cantorIntervalEmbedding := by
  intro s t hst
  have hval := congrArg Subtype.val hst
  have hcf :
      Cardinal.cantorFunction (1 / 3 : ℝ) s =
        Cardinal.cantorFunction (1 / 3 : ℝ) t := by
    dsimp [cantorIntervalEmbedding, cantorIntervalValue] at hval
    nlinarith
  exact Cardinal.cantorFunction_injective (c := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) hcf

theorem sameCardinality_to_nat_countable {α : Type*} {A : Set α}
    (hne : A.Nonempty) (h : SameCardinality A (Set.univ : Set ℕ)) :
    A.Countable := by
  rcases h with ⟨e⟩
  rw [Set.countable_iff_exists_surjective hne]
  refine ⟨fun n => e.symm ⟨n, by trivial⟩, ?_⟩
  intro a
  refine ⟨(e a).1, ?_⟩
  have hn : (⟨(e a).1, by trivial⟩ : (Set.univ : Set ℕ)) = e a := by
    ext
    rfl
  simpa [hn] using e.left_inv a

def ex_2_1_2 : Prop :=
  ¬ IsCountableSet (Set.Icc (0 : ℝ) 1)

theorem ex_2_1_2_binary_sequences_uncountable :
    ¬ IsCountableSet (Set.univ : Set (ℕ → Bool)) := by
  rintro ⟨e⟩
  let F : ℕ → ℕ → Bool := fun n => (e.symm ⟨n, by trivial⟩).1
  let sStar : ℕ → Bool := diagonalFlip F
  let nSub : (Set.univ : Set ℕ) := e ⟨sStar, by trivial⟩
  have hrow : F nSub.1 = sStar := by
    have hs : e.symm nSub = ⟨sStar, by trivial⟩ := by
      simp [nSub]
    simpa [F] using congrArg Subtype.val hs
  exact (diagonalFlip_ne_row F nSub.1) hrow.symm

theorem ex_2_1_2_binary_sequences_no_nat_injection :
    ¬ ∃ enc : (ℕ → Bool) → ℕ, Function.Injective enc := by
  rintro ⟨enc, henc⟩
  classical
  let F : ℕ → ℕ → Bool := fun n =>
    if h : ∃ s : ℕ → Bool, enc s = n then Classical.choose h else fun _ => false
  let sStar : ℕ → Bool := diagonalFlip F
  have hmem : ∃ s : ℕ → Bool, enc s = enc sStar := ⟨sStar, rfl⟩
  have hrow : F (enc sStar) = sStar := by
    dsimp [F]
    rw [dif_pos hmem]
    exact henc (Classical.choose_spec hmem)
  exact (diagonalFlip_ne_row F (enc sStar)) hrow.symm

theorem ex_2_1_2_unitInterval_uncountable :
    ¬ IsCountableSet (Set.Icc (0 : ℝ) 1) := by
  rintro ⟨e⟩
  exact ex_2_1_2_binary_sequences_no_nat_injection ⟨
    fun s => (e (cantorIntervalEmbedding s)).1,
    by
      intro s t hst
      apply cantorIntervalEmbedding_injective
      apply e.injective
      ext
      exact hst⟩

theorem ex_2_1_2_reals_uncountable :
    ¬ IsCountableSet (Set.univ : Set ℝ) := by
  rintro ⟨e⟩
  exact ex_2_1_2_binary_sequences_no_nat_injection ⟨
    fun s => (e ⟨cantorIntervalValue s, by trivial⟩).1,
    by
      intro s t hst
      have heq :
          e ⟨cantorIntervalValue s, by trivial⟩ =
            e ⟨cantorIntervalValue t, by trivial⟩ := by
        ext
        exact hst
      have hsub :
          (⟨cantorIntervalValue s, by trivial⟩ : (Set.univ : Set ℝ)) =
            ⟨cantorIntervalValue t, by trivial⟩ := e.injective heq
      have hval := congrArg Subtype.val hsub
      apply cantorIntervalEmbedding_injective
      exact Subtype.ext hval⟩

theorem ex_2_1_2_holds : ex_2_1_2 := by
  exact ex_2_1_2_unitInterval_uncountable
