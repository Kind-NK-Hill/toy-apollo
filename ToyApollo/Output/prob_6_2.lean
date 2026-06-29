import Mathlib

/-
TASK ID: prob_6_2
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
TASK CONTENT:
\textbf{6.2.} In the hat problem described in Example 6.5.1, find the variance of the number of people who can get back his/her own hat. (Hint: Compute $E[1_{A_i}1_{A_j}]$.)
-/

open MeasureTheory ProbabilityTheory Finset BigOperators

noncomputable section

/-- Number of permutations of `Fin n` that fix element `i`. -/
lemma card_perm_fixing_one (n : ℕ) (i : Fin n) :
    Fintype.card {σ : Equiv.Perm (Fin n) | σ i = i} = (n - 1).factorial := by
  rcases n with (_ | n) <;> simp_all +decide [Nat.factorial]
  · fin_cases i
  · rw [Fintype.card_subtype]
    have h_count :
        Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ i = i) Finset.univ) =
          Finset.card (Finset.image (fun σ : Equiv.Perm {x // x ≠ i} => Equiv.Perm.ofSubtype σ) Finset.univ) := by
      congr with σ
      simp +decide [Equiv.Perm.ofSubtype]
      constructor
      · intro hi
        use Equiv.Perm.subtypePerm σ (by
          exact fun x =>
            ⟨fun hx => by
                rintro rfl
                exact hx hi,
              fun hx => by
                rintro hx'
                exact hx <| σ.injective <| hx'.trans hi.symm⟩)
        ext x
        by_cases hx : x = i <;> simp_all +decide [Equiv.Perm.extendDomain]
      · rintro ⟨a, rfl⟩
        simp +decide [Equiv.Perm.extendDomain]
    rw [h_count, Finset.card_image_of_injective]
    · simp +decide [Finset.card_univ, Fintype.card_perm]
    · exact Equiv.Perm.ofSubtype_injective

/-- Number of permutations of `Fin n` that fix both `i` and `j`. -/
lemma card_perm_fixing_two (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Fintype.card {σ : Equiv.Perm (Fin n) | σ i = i ∧ σ j = j} = (n - 2).factorial := by
  let p : Fin n → Prop := fun x => x ≠ i ∧ x ≠ j
  have h_fix_equiv :
      {f : Equiv.Perm (Fin n) // ∀ a, ¬ p a → f a = a} ≃
        {σ : Equiv.Perm (Fin n) | σ i = i ∧ σ j = j} := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro σ
      exact ⟨σ.1, ⟨σ.2 i (by simp [p]), σ.2 j (by simp [p])⟩⟩
    · intro σ
      refine ⟨σ.1, ?_⟩
      intro a ha
      have ha' : a = i ∨ a = j := by
        by_cases hai : a = i
        · exact Or.inl hai
        · right
          by_contra haj
          exact ha ⟨hai, haj⟩
      cases ha' with
      | inl hai => simpa [hai] using σ.2.1
      | inr haj => simpa [haj] using σ.2.2
    · intro σ
      cases σ
      rfl
    · intro σ
      cases σ
      rfl
  have h_iso : {σ : Equiv.Perm (Fin n) | σ i = i ∧ σ j = j} ≃
      Equiv.Perm {x : Fin n | x ≠ i ∧ x ≠ j} := by
    simpa [p] using h_fix_equiv.symm.trans (Equiv.Perm.subtypeEquivSubtypePerm p).symm
  convert Fintype.card_congr h_iso using 1
  rw [Fintype.card_perm]
  have h_card :
      Fintype.card {x : Fin n // x ≠ i ∧ x ≠ j} = n - 2 := by
    have h_not_i : Fintype.card {x : Fin n // x ≠ i} = n - 1 := by
      simpa [Fintype.card_fin] using
        (Fintype.card_subtype_compl (fun x : Fin n => x = i)).trans (by
          rw [Fintype.card_subtype_eq i])
    have h_not_j_in_not_i :
        Fintype.card {x : {x : Fin n // x ≠ i} // x.1 ≠ j} = n - 2 := by
      let y : {x : Fin n // x ≠ i} := ⟨j, by simpa using hij.symm⟩
      have h_eq_j : Fintype.card {x : {x : Fin n // x ≠ i} // x.1 = j} = 1 := by
        have h_congr :
            {x : {x : Fin n // x ≠ i} // x.1 = j} ≃
              {x : {x : Fin n // x ≠ i} // x = y} :=
          Equiv.subtypeEquivRight (fun x => by
            constructor
            · intro hx
              apply Subtype.ext
              simpa [y] using hx
            · intro hx
              simpa [y] using congrArg Subtype.val hx)
        rw [Fintype.card_congr h_congr, Fintype.card_subtype_eq y]
      rw [Fintype.card_subtype_compl, h_eq_j, h_not_i]
      omega
    rw [← Fintype.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : Fin n => x ≠ i) (fun x : Fin n => x ≠ j))]
    exact h_not_j_in_not_i
  exact congrArg Nat.factorial h_card.symm

/-- Sum of indicators `∑_σ 1_{σ(i)=i}` over all permutations equals `(n-1)!`. -/
lemma sum_indicator_fix (n : ℕ) (i : Fin n) :
    (∑ σ : Equiv.Perm (Fin n), if σ i = i then (1 : ℝ) else 0) = ((n - 1).factorial : ℝ) := by
  convert card_perm_fixing_one n i using 1
  rw [Fintype.card_subtype]
  aesop

/-- Sum of product indicators `∑_σ 1_{σ(i)=i}1_{σ(j)=j}` for `i ≠ j`. -/
lemma sum_indicator_fix_two (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∑ σ : Equiv.Perm (Fin n),
      (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0) =
    ((n - 2).factorial : ℝ) := by
  norm_num [Finset.sum_ite]
  convert card_perm_fixing_two n i j hij using 1
  rw [Fintype.card_of_subtype]
  aesop

/-- Sum of fixed point counts over all permutations equals `n!`. -/
lemma sum_fixedPointCount (n : ℕ) (hn : 1 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      (∑ i : Fin n, if σ i = i then (1 : ℝ) else 0) = (n.factorial : ℝ) := by
  have h_swap :
      (∑ σ : Equiv.Perm (Fin n), (∑ i : Fin n, (if σ i = i then (1 : ℝ) else 0))) =
        (∑ i : Fin n, (∑ σ : Equiv.Perm (Fin n), (if σ i = i then (1 : ℝ) else 0))) := by
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop)
  have := sum_indicator_fix n
  cases n <;> simp_all +decide [Nat.factorial]

/-- Sum of squares of fixed point counts over all permutations equals `2 * n!`. -/
lemma sum_sq_fixedPointCount (n : ℕ) (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      (∑ i : Fin n, if σ i = i then (1 : ℝ) else 0) ^ 2 = 2 * (n.factorial : ℝ) := by
  have h_expand :
      ∑ σ : Equiv.Perm (Fin n), (∑ i : Fin n, if σ i = i then (1 : ℝ) else 0) ^ 2 =
        ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, (if σ i = i then (1 : ℝ) else 0) +
          ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ.erase i,
            (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0) := by
    simp +decide [← Finset.sum_add_distrib, sq]
    simp +decide [Finset.sum_ite, Finset.filter_congr, Finset.filter_true_of_mem]
  have h_eval :
      ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, (if σ i = i then (1 : ℝ) else 0) =
          (n.factorial : ℝ) ∧
        ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ.erase i,
            (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0) =
          (n * (n - 1) * (n - 2).factorial : ℝ) := by
    constructor
    · convert sum_fixedPointCount n (by linarith) using 1
    · have h_off_diag :
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ σ : Equiv.Perm (Fin n),
              (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0) =
            n * (n - 1) * (n - 2).factorial := by
        have h_off_diag :
            ∀ i j : Fin n, i ≠ j →
              ∑ σ : Equiv.Perm (Fin n),
                (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0) =
                  (n - 2).factorial := by
          exact fun i j h => sum_indicator_fix_two n i j h
        rw [Finset.sum_congr rfl fun i hi =>
          Finset.sum_congr rfl fun j hj => h_off_diag i j <| by aesop]
        norm_num [mul_assoc, mul_comm, mul_left_comm, hn.trans_lt']
      convert h_off_diag using 1
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  rcases n with (_ | _ | n) <;> simp_all +decide [Nat.factorial]
  linarith

theorem prob_6_2 (n : ℕ) (hn : 2 ≤ n) :
    letI _mΩ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
    let P := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let N : Equiv.Perm (Fin n) → ℝ := fun ω => ∑ i : Fin n, if ω i = i then (1 : ℝ) else 0
    variance N P = 1 := by
  refine' Eq.trans _ (sub_eq_of_eq_add _)
  rw [ProbabilityTheory.variance_eq_sub]
  · simp +decide [PMF.uniformOfFintype]
  · erw [MeasureTheory.integral_fintype]
    · erw [MeasureTheory.integral_fintype]
      · simp +decide [PMF.uniformOfFintype_apply, MeasureTheory.measureReal_def]
        simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul, Fintype.card_perm]
        field_simp
        have := sum_sq_fixedPointCount n hn
        have := sum_fixedPointCount n (by linarith)
        norm_cast at *
        simp_all +decide [Finset.sum_ite]
        ring
      · simp +zetaDelta at *
    · exact Integrable.of_finite

end
