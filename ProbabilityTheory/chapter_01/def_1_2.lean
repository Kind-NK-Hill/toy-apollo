/-
TASK ID: def_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic

--import Mathlib.Topology.MetricSpace.Basic
-- ℝ as a metric space: `dist`, `Real.dist_eq`, `eq_of_forall_dist_le`
--import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- ℝ ordered field, `sSup`/`sInf`, `exists_nat_gt`
--import Mathlib.Data.Fintype.Basic
-- `Fintype (Fin n)`, `Finset.univ`, `Finset.mem_univ`
--import Mathlib.Data.Finset.Lattice.Fold
-- `Finset.sup'`, `Finset.sup'_eq_of_forall`
--import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- `∑` (`Finset.sum`) notation

open scoped BigOperators Pointwise

noncomputable section






def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧
  BddAbove (f '' Set.Icc a b) ∧
  BddBelow (f '' Set.Icc a b) ∧
  MonotoneOn alpha (Set.Icc a b)




structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  pts_start : pts 0 = a
  pts_end : pts (Fin.last n) = b
  strict_mono : StrictMono pts




def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin P.n))
    ⟨⟨0, P.hn⟩, Finset.mem_univ _⟩
    fun i => P.pts i.succ - P.pts i.castSucc



def Partition.subinterval {a b : ℝ} (P : Partition a b) (i : Fin P.n)
  : Set ℝ :=
  Set.Icc (P.pts i.castSucc) (P.pts i.succ)



def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sSup (f '' Partition.subinterval P i)



def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sInf (f '' Partition.subinterval P i)




def taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    f (tags i) * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

 
def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.n, tags i ∈ Partition.subinterval P i



example {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) :
  tagsInPartition P tags ↔ ∀ i : Fin P.n, tags i ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ)
  := by rfl




def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    upperStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))



def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    lowerStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))




def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps



def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L




def TaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : Fin P.n → ℝ,
      tagsInPartition P tags →
      P.mesh < delta →
      |taggedSum P tags f alpha - L| < eps


 
def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  UpperLowerCommonLimit a b f alpha L

 
def rsTaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  TaggedCommonLimit a b f alpha L








structure RSIntegralWitness (f alpha : ℝ → ℝ) (a b : ℝ) where
  value : ℝ
  source_limit : rsUpperLowerCommonLimit a b f alpha value
  tagged_limit : rsTaggedCommonLimit a b f alpha value




def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  Nonempty (RSIntegralWitness f alpha a b)



noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  (Classical.choice h).value

 
theorem rsIntegral_source_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).source_limit

 
theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).tagged_limit

 
theorem rsIntegral_source_and_tagged_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) ∧
      rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  ⟨rsIntegral_source_spec h, rsIntegral_spec h⟩












def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b




def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}




section RS_integral_uniqueness






theorem leftTagsInPartition {a b : ℝ} (P : Partition a b) :
    tagsInPartition P (fun i => P.pts i.castSucc) := by
  intro i
  constructor
  · exact le_rfl
  · simp only
    apply le_of_lt
    exact P.strict_mono (Fin.castSucc_lt_succ)




def uniformPartition (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  hn := hn
  pts := fun i => a + ((i : ℝ) / (n : ℝ)) * (b - a)
  pts_start := by simp
  pts_end := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    -- Explicitly change the Fin coercion to expose its integer value
    change a + ((Fin.last n).val : ℝ) / (n : ℝ) * (b - a) = b
    rw [Fin.val_last]
    field_simp [hn0]
    ring
  strict_mono := by
    -- StrictMono means ∀ i j, i < j → pts i < pts j
    intro i j hij
    dsimp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hba : 0 < b - a := sub_pos.mpr hab
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij

    -- Step 1: i < j  ==>  i / n < j / n
    have h1 : (i : ℝ) / (n : ℝ) < (j : ℝ) / (n : ℝ) := by
      exact mul_lt_mul_of_pos_right hijR (inv_pos.mpr hnR)

    -- Step 2: i / n * (b - a) < j / n * (b - a)
    have h2 : ((i : ℝ) / (n : ℝ)) * (b - a) < ((j : ℝ) / (n : ℝ)) * (b - a) :=
      mul_lt_mul_of_pos_right h1 hba

    -- Step 3: a + ... < a + ...
    linarith [h2]




theorem uniformPartition_mesh_eq (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring




theorem exists_partition_mesh_lt {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq]
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hltN : (b - a) / δ < (N : ℝ) := by
    have hnle : (n : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hnle
  have hmul : b - a < (N : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ] at hltN
  rw [div_lt_iff₀ hNposR]
  nlinarith



theorem taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨_hs₂, hlim₂⟩
  rcases hs₁ with ⟨hab, _⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  rcases exists_partition_mesh_lt hab (lt_min hδ₁ hδ₂) with ⟨P, hPmesh⟩

  -- Define `tags` to precisely match the size `Fin P.n`
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- `leftTagsInPartition P` provides exactly this proof.
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hPmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hPmesh (min_le_right δ₁ δ₂)

  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hdecomp :
      L₁ - L₂ = -(taggedSum P tags f alpha - L₁) +
        (taggedSum P tags f alpha - L₂) := by
    ring
  have hlt : |L₁ - L₂| < eps := by
    calc
      |L₁ - L₂| =
          |-(taggedSum P tags f alpha - L₁) +
            (taggedSum P tags f alpha - L₂)| := by rw [hdecomp]
      _ ≤ |-(taggedSum P tags f alpha - L₁)| +
            |taggedSum P tags f alpha - L₂| := abs_add_le _ _
      _ = |taggedSum P tags f alpha - L₁| +
            |taggedSum P tags f alpha - L₂| := by rw [abs_neg]
      _ < eps := by
        have hsum :
            |taggedSum P tags f alpha - L₁| +
                |taggedSum P tags f alpha - L₂| < eps / 2 + eps / 2 :=
          add_lt_add hP₁ hP₂
        simpa using hsum
  have hdist : dist L₁ L₂ < eps := by
    simpa [Real.dist_eq, abs_sub_comm] using hlt
  exact le_of_lt hdist

end RS_integral_uniqueness
