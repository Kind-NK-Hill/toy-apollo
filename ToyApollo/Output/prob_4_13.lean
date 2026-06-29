import Mathlib

/-
TASK ID: prob_4_13
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.13.} Let $A$ be the set $\{1, 2, 3, 4\}$ and $B$ be $\{a, b, c\}$:
\begin{enumerate}[label=(\alph*)]
    \item How many distinct functions can be defined from $A$ to $B$?
    \item Suppose we impose an algebra $\mathcal{F} = \{\emptyset, A, \{1, 2\}, \{3, 4\}\}$ on $A$, and an algebra $\mathcal{G} = \{\emptyset, B, \{a, b\}, \{c\}\}$ on $B$. Count the number of $(\mathcal{F}, \mathcal{G})$-measurable functions from $A$ to $B$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

private abbrev prob_4_13_A := Fin 4
private abbrev prob_4_13_B := Fin 3

private def prob_4_13_left : Finset prob_4_13_A :=
  ({0, 1} : Finset prob_4_13_A)

private def prob_4_13_right : Finset prob_4_13_A :=
  ({2, 3} : Finset prob_4_13_A)

private def prob_4_13_ab : Finset prob_4_13_B :=
  ({0, 1} : Finset prob_4_13_B)

private def prob_4_13_c : Finset prob_4_13_B :=
  ({2} : Finset prob_4_13_B)

private def prob_4_13_F : Finset (Finset prob_4_13_A) :=
  {∅, Finset.univ, prob_4_13_left, prob_4_13_right}

private def prob_4_13_G : Finset (Finset prob_4_13_B) :=
  {∅, Finset.univ, prob_4_13_ab, prob_4_13_c}

private def prob_4_13_preimage (f : prob_4_13_A → prob_4_13_B)
    (S : Finset prob_4_13_B) : Finset prob_4_13_A :=
  Finset.univ.filter (fun a => f a ∈ S)

private def prob_4_13_isMeasurable (f : prob_4_13_A → prob_4_13_B) : Prop :=
  ∀ S ∈ prob_4_13_G, prob_4_13_preimage f S ∈ prob_4_13_F

@[simp] private lemma prob_4_13_mem_preimage
    (f : prob_4_13_A → prob_4_13_B) (S : Finset prob_4_13_B)
    (a : prob_4_13_A) :
    a ∈ prob_4_13_preimage f S ↔ f a ∈ S := by
  simp [prob_4_13_preimage]

@[simp] private lemma prob_4_13_mem_c_iff_not_mem_ab (x : prob_4_13_B) :
    x ∈ prob_4_13_c ↔ x ∉ prob_4_13_ab := by
  fin_cases x <;> simp [prob_4_13_ab, prob_4_13_c]

private lemma prob_4_13_status_of_measurable
    (f : prob_4_13_A → prob_4_13_B) (hf : prob_4_13_isMeasurable f) :
    (f 0 ∈ prob_4_13_ab ↔ f 1 ∈ prob_4_13_ab) ∧
      (f 2 ∈ prob_4_13_ab ↔ f 3 ∈ prob_4_13_ab) := by
  have hpre : prob_4_13_preimage f prob_4_13_ab ∈ prob_4_13_F := by
    exact hf prob_4_13_ab (by simp [prob_4_13_G])
  have hcases :
      prob_4_13_preimage f prob_4_13_ab = ∅ ∨
        prob_4_13_preimage f prob_4_13_ab = Finset.univ ∨
        prob_4_13_preimage f prob_4_13_ab = prob_4_13_left ∨
        prob_4_13_preimage f prob_4_13_ab = prob_4_13_right := by
    simpa [prob_4_13_F] using hpre
  constructor
  · rcases hcases with h | h | h | h <;>
      rw [← prob_4_13_mem_preimage f prob_4_13_ab (0 : prob_4_13_A),
        ← prob_4_13_mem_preimage f prob_4_13_ab (1 : prob_4_13_A), h] <;>
      simp [prob_4_13_left, prob_4_13_right]
  · rcases hcases with h | h | h | h <;>
      rw [← prob_4_13_mem_preimage f prob_4_13_ab (2 : prob_4_13_A),
        ← prob_4_13_mem_preimage f prob_4_13_ab (3 : prob_4_13_A), h] <;>
      simp [prob_4_13_left, prob_4_13_right]

private lemma prob_4_13_preimage_ab_mem_F_of_status
    (f : prob_4_13_A → prob_4_13_B)
    (h01 : f 0 ∈ prob_4_13_ab ↔ f 1 ∈ prob_4_13_ab)
    (h23 : f 2 ∈ prob_4_13_ab ↔ f 3 ∈ prob_4_13_ab) :
    prob_4_13_preimage f prob_4_13_ab ∈ prob_4_13_F := by
  by_cases h0 : f 0 ∈ prob_4_13_ab <;> by_cases h2 : f 2 ∈ prob_4_13_ab
  · have h1 : f 1 ∈ prob_4_13_ab := h01.mp h0
    have h3 : f 3 ∈ prob_4_13_ab := h23.mp h2
    have hpre : prob_4_13_preimage f prob_4_13_ab = Finset.univ := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∈ prob_4_13_ab := h01.mp h0
    have h3 : f 3 ∉ prob_4_13_ab := by
      intro h
      exact h2 (h23.mpr h)
    have hpre : prob_4_13_preimage f prob_4_13_ab = prob_4_13_left := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, prob_4_13_left, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∉ prob_4_13_ab := by
      intro h
      exact h0 (h01.mpr h)
    have h3 : f 3 ∈ prob_4_13_ab := h23.mp h2
    have hpre : prob_4_13_preimage f prob_4_13_ab = prob_4_13_right := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, prob_4_13_right, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∉ prob_4_13_ab := by
      intro h
      exact h0 (h01.mpr h)
    have h3 : f 3 ∉ prob_4_13_ab := by
      intro h
      exact h2 (h23.mpr h)
    have hpre : prob_4_13_preimage f prob_4_13_ab = ∅ := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]

private lemma prob_4_13_preimage_c_mem_F_of_status
    (f : prob_4_13_A → prob_4_13_B)
    (h01 : f 0 ∈ prob_4_13_ab ↔ f 1 ∈ prob_4_13_ab)
    (h23 : f 2 ∈ prob_4_13_ab ↔ f 3 ∈ prob_4_13_ab) :
    prob_4_13_preimage f prob_4_13_c ∈ prob_4_13_F := by
  by_cases h0 : f 0 ∈ prob_4_13_ab <;> by_cases h2 : f 2 ∈ prob_4_13_ab
  · have h1 : f 1 ∈ prob_4_13_ab := h01.mp h0
    have h3 : f 3 ∈ prob_4_13_ab := h23.mp h2
    have hpre : prob_4_13_preimage f prob_4_13_c = ∅ := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∈ prob_4_13_ab := h01.mp h0
    have h3 : f 3 ∉ prob_4_13_ab := by
      intro h
      exact h2 (h23.mpr h)
    have hpre : prob_4_13_preimage f prob_4_13_c = prob_4_13_right := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, prob_4_13_right, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∉ prob_4_13_ab := by
      intro h
      exact h0 (h01.mpr h)
    have h3 : f 3 ∈ prob_4_13_ab := h23.mp h2
    have hpre : prob_4_13_preimage f prob_4_13_c = prob_4_13_left := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, prob_4_13_left, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]
  · have h1 : f 1 ∉ prob_4_13_ab := by
      intro h
      exact h0 (h01.mpr h)
    have h3 : f 3 ∉ prob_4_13_ab := by
      intro h
      exact h2 (h23.mpr h)
    have hpre : prob_4_13_preimage f prob_4_13_c = Finset.univ := by
      ext x
      fin_cases x <;> simp [prob_4_13_preimage, h0, h1, h2, h3]
    rw [hpre]
    simp [prob_4_13_F]

private lemma prob_4_13_measurable_of_status
    (f : prob_4_13_A → prob_4_13_B)
    (h01 : f 0 ∈ prob_4_13_ab ↔ f 1 ∈ prob_4_13_ab)
    (h23 : f 2 ∈ prob_4_13_ab ↔ f 3 ∈ prob_4_13_ab) :
    prob_4_13_isMeasurable f := by
  intro S hS
  have hScases :
      S = ∅ ∨ S = Finset.univ ∨ S = prob_4_13_ab ∨ S = prob_4_13_c := by
    simpa [prob_4_13_G] using hS
  rcases hScases with rfl | rfl | rfl | rfl
  · simp [prob_4_13_preimage, prob_4_13_F]
  · simp [prob_4_13_preimage, prob_4_13_F]
  · exact prob_4_13_preimage_ab_mem_F_of_status f h01 h23
  · exact prob_4_13_preimage_c_mem_F_of_status f h01 h23

private abbrev prob_4_13_BlockChoice := Unit ⊕ (Fin 2 × Fin 2)

private def prob_4_13_embedAB (x : Fin 2) : prob_4_13_B :=
  ⟨x.1, by omega⟩

private def prob_4_13_toAB (x : prob_4_13_B) (hx : x ∈ prob_4_13_ab) : Fin 2 :=
  ⟨x.1, by
    fin_cases x <;> simp [prob_4_13_ab] at hx ⊢⟩

@[simp] private lemma prob_4_13_embedAB_mem (x : Fin 2) :
    prob_4_13_embedAB x ∈ prob_4_13_ab := by
  fin_cases x <;> simp [prob_4_13_embedAB, prob_4_13_ab]

@[simp] private lemma prob_4_13_embedAB_not_mem_c (x : Fin 2) :
    prob_4_13_embedAB x ∉ prob_4_13_c := by
  fin_cases x <;> simp [prob_4_13_embedAB, prob_4_13_c]

@[simp] private lemma prob_4_13_two_not_mem_ab :
    (2 : prob_4_13_B) ∉ prob_4_13_ab := by
  simp [prob_4_13_ab]

@[simp] private lemma prob_4_13_two_mem_c :
    (2 : prob_4_13_B) ∈ prob_4_13_c := by
  simp [prob_4_13_c]

@[simp] private lemma prob_4_13_embed_toAB
    (x : prob_4_13_B) (hx : x ∈ prob_4_13_ab) :
    prob_4_13_embedAB (prob_4_13_toAB x hx) = x := by
  fin_cases x <;> simp [prob_4_13_toAB, prob_4_13_embedAB, prob_4_13_ab] at hx ⊢

@[simp] private lemma prob_4_13_toAB_embed
    (x : Fin 2) (hx : prob_4_13_embedAB x ∈ prob_4_13_ab) :
    prob_4_13_toAB (prob_4_13_embedAB x) hx = x := by
  fin_cases x <;> simp [prob_4_13_toAB, prob_4_13_embedAB, prob_4_13_ab]

private lemma prob_4_13_not_mem_ab_eq_two
    (x : prob_4_13_B) (hx : x ∉ prob_4_13_ab) : x = 2 := by
  fin_cases x <;> simp [prob_4_13_ab] at hx ⊢

private def prob_4_13_decodeBlock :
    prob_4_13_BlockChoice → Fin 2 → prob_4_13_B
  | Sum.inl (), _ => 2
  | Sum.inr xy, i => if i = 0 then prob_4_13_embedAB xy.1 else prob_4_13_embedAB xy.2

private def prob_4_13_encodeBlock (x y : prob_4_13_B)
    (hxy : x ∈ prob_4_13_ab ↔ y ∈ prob_4_13_ab) : prob_4_13_BlockChoice :=
  if hx : x ∈ prob_4_13_ab then
    Sum.inr (prob_4_13_toAB x hx, prob_4_13_toAB y (hxy.mp hx))
  else
    Sum.inl ()

private lemma prob_4_13_decode_encodeBlock_zero
    (x y : prob_4_13_B) (hxy : x ∈ prob_4_13_ab ↔ y ∈ prob_4_13_ab) :
    prob_4_13_decodeBlock (prob_4_13_encodeBlock x y hxy) 0 = x := by
  unfold prob_4_13_encodeBlock prob_4_13_decodeBlock
  by_cases hx : x ∈ prob_4_13_ab
  · simp [hx]
  · have hx2 : x = 2 := prob_4_13_not_mem_ab_eq_two x hx
    simp [hx, hx2]

private lemma prob_4_13_decode_encodeBlock_one
    (x y : prob_4_13_B) (hxy : x ∈ prob_4_13_ab ↔ y ∈ prob_4_13_ab) :
    prob_4_13_decodeBlock (prob_4_13_encodeBlock x y hxy) 1 = y := by
  unfold prob_4_13_encodeBlock prob_4_13_decodeBlock
  by_cases hx : x ∈ prob_4_13_ab
  · simp [hx]
  · have hy_not : y ∉ prob_4_13_ab := by
      intro hy
      exact hx (hxy.mpr hy)
    have hy2 : y = 2 := prob_4_13_not_mem_ab_eq_two y hy_not
    simp [hx, hy2]

private lemma prob_4_13_decodeBlock_sameStatus (b : prob_4_13_BlockChoice) :
    prob_4_13_decodeBlock b 0 ∈ prob_4_13_ab ↔
      prob_4_13_decodeBlock b 1 ∈ prob_4_13_ab := by
  rcases b with _ | ⟨x, y⟩ <;>
    simp [prob_4_13_decodeBlock]

private lemma prob_4_13_encode_decodeBlock
    (b : prob_4_13_BlockChoice)
    (h : prob_4_13_decodeBlock b 0 ∈ prob_4_13_ab ↔
      prob_4_13_decodeBlock b 1 ∈ prob_4_13_ab) :
    prob_4_13_encodeBlock (prob_4_13_decodeBlock b 0)
      (prob_4_13_decodeBlock b 1) h = b := by
  rcases b with _ | ⟨x, y⟩ <;>
    simp [prob_4_13_encodeBlock, prob_4_13_decodeBlock]

private def prob_4_13_codeToFun
    (code : prob_4_13_BlockChoice × prob_4_13_BlockChoice) :
    prob_4_13_A → prob_4_13_B :=
  ![
    prob_4_13_decodeBlock code.1 0,
    prob_4_13_decodeBlock code.1 1,
    prob_4_13_decodeBlock code.2 0,
    prob_4_13_decodeBlock code.2 1
  ]

private lemma prob_4_13_codeToFun_measurable
    (code : prob_4_13_BlockChoice × prob_4_13_BlockChoice) :
    prob_4_13_isMeasurable (prob_4_13_codeToFun code) := by
  apply prob_4_13_measurable_of_status
  · simpa [prob_4_13_codeToFun] using prob_4_13_decodeBlock_sameStatus code.1
  · simpa [prob_4_13_codeToFun] using prob_4_13_decodeBlock_sameStatus code.2

private def prob_4_13_measurableEquivCode :
    {f : prob_4_13_A → prob_4_13_B // prob_4_13_isMeasurable f} ≃
      prob_4_13_BlockChoice × prob_4_13_BlockChoice where
  toFun f :=
    let h := prob_4_13_status_of_measurable f.1 f.2
    (prob_4_13_encodeBlock (f.1 0) (f.1 1) h.1,
      prob_4_13_encodeBlock (f.1 2) (f.1 3) h.2)
  invFun code := ⟨prob_4_13_codeToFun code, prob_4_13_codeToFun_measurable code⟩
  left_inv f := by
    ext i
    fin_cases i <;>
      simp [prob_4_13_codeToFun, prob_4_13_decode_encodeBlock_zero,
        prob_4_13_decode_encodeBlock_one]
  right_inv code := by
    rcases code with ⟨l, r⟩
    simp [prob_4_13_codeToFun, prob_4_13_encode_decodeBlock,
      prob_4_13_decodeBlock_sameStatus]

private lemma prob_4_13_blockChoice_card :
    Fintype.card prob_4_13_BlockChoice = 5 := by
  rw [Fintype.card_sum, Fintype.card_prod]
  simp

private lemma prob_4_13_measurable_count :
    Fintype.card {f : prob_4_13_A → prob_4_13_B //
      prob_4_13_isMeasurable f} = 25 := by
  rw [Fintype.card_congr prob_4_13_measurableEquivCode]
  rw [Fintype.card_prod, prob_4_13_blockChoice_card]

theorem prob_4_13 :
  let A := Fin 4
  let B := Fin 3
  let F : Finset (Finset A) := {∅, Finset.univ, ({0,1} : Finset A), ({2,3} : Finset A)}
  let G : Finset (Finset B) := {∅, Finset.univ, ({0,1} : Finset B), ({2} : Finset B)}
  let is_measurable (f : A → B) : Prop := ∀ S ∈ G, (Finset.filter (fun a => f a ∈ S) Finset.univ) ∈ F
  Fintype.card (A → B) = 81 ∧ Fintype.card {f : A → B // is_measurable f} = 25 := by
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    norm_num
  · simpa [prob_4_13_A, prob_4_13_B, prob_4_13_F, prob_4_13_G,
      prob_4_13_left, prob_4_13_right, prob_4_13_ab, prob_4_13_c,
      prob_4_13_isMeasurable, prob_4_13_preimage] using prob_4_13_measurable_count
