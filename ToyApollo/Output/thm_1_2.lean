/-
TASK ID: thm_1_2
TYPE: Theorem_Statement
SOURCE PLAN: 38_chap1_riemann_stieltjes
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2

-- WRITE FINAL LEAN CODE BELOW

open Set

noncomputable section

namespace Thm12Item4

open DarbouxRS

private def leftNodeIndex {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k ≤ P.n) (i : Fin (k + 1)) : Fin (P.n + 1) :=
  Fin.castLE (Nat.succ_le_succ hkn) i

private def leftCellIndex {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k ≤ P.n) (i : Fin k) : Fin P.n :=
  Fin.castLE hkn i

private def rightNodeIndex {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k ≤ P.n) (j : Fin (P.n - k + 1)) : Fin (P.n + 1) :=
  ⟨k + j.val, by omega⟩

private def rightCellIndex {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k ≤ P.n) (j : Fin (P.n - k)) : Fin P.n :=
  ⟨k + j.val, by omega⟩

private def pointAtNat {a b : ℝ} (P : Partition a b) (i : ℕ) : ℝ :=
  if hi : i ≤ P.n then P.pts ⟨i, Nat.lt_succ_iff.mpr hi⟩ else b

private def subintervalAtNat {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  if hi : i < P.n then Icc (pointAtNat P i) (pointAtNat P (i + 1)) else ∅

private def upperStepAtNat {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < P.n then sSup (f '' subintervalAtNat P i) else 0

private def lowerStepAtNat {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < P.n then sInf (f '' subintervalAtNat P i) else 0

private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i ≤ P.n) :
    pointAtNat P i = P.pts ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  simp [pointAtNat, hi]

private lemma subintervalAtNat_eq {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i < P.n) :
    subintervalAtNat P i = subinterval P ⟨i, hi⟩ := by
  rw [subintervalAtNat, dif_pos hi, subinterval, Partition.subinterval,
    pointAtNat_eq P (Nat.le_of_lt hi), pointAtNat_eq P (Nat.succ_le_of_lt hi)]
  rfl

private lemma upperStepAtNat_eq {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    upperStepAtNat P f i = upperStep P f ⟨i, hi⟩ := by
  rw [upperStepAtNat, dif_pos hi, upperStep, subintervalAtNat_eq P hi]

private lemma lowerStepAtNat_eq {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) {i : ℕ} (hi : i < P.n) :
    lowerStepAtNat P f i = lowerStep P f ⟨i, hi⟩ := by
  rw [lowerStepAtNat, dif_pos hi, lowerStep, subintervalAtNat_eq P hi]

private def splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k ≤ P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr hkn⟩ = c) : Partition a c where
  n := k
  hn := hk0
  pts := fun i => P.pts (leftNodeIndex P k hkn i)
  pts_start := by simpa [leftNodeIndex] using P.pts_start
  pts_end := by
    rw [show leftNodeIndex P k hkn (Fin.last k) =
        (⟨k, Nat.lt_succ_iff.mpr hkn⟩ : Fin (P.n + 1)) by
      apply Fin.ext
      simp [leftNodeIndex]]
    exact hc
  strict_mono := by
    intro i j hij
    exact P.strict_mono ((Fin.castLE_lt_castLE_iff _).2 hij)

private def splitRight {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) :
    Partition c b where
  n := P.n - k
  hn := Nat.sub_pos_of_lt hkn
  pts := fun j => P.pts (rightNodeIndex P k (le_of_lt hkn) j)
  pts_start := by simpa [rightNodeIndex] using hc
  pts_end := by
    rw [show rightNodeIndex P k (le_of_lt hkn) (Fin.last (P.n - k)) =
        Fin.last P.n by
      apply Fin.ext
      simp [rightNodeIndex, Nat.add_sub_of_le (le_of_lt hkn)]]
    exact P.pts_end
  strict_mono := by
    intro i j hij
    apply P.strict_mono
    change k + i.val < k + j.val
    omega

private lemma upperStep_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hk0 : 0 < k) (hkn : k ≤ P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr hkn⟩ = c) (f : ℝ → ℝ) (i : Fin k) :
    upperStep (splitLeft P k hk0 hkn c hc) f i =
      upperStep P f (leftCellIndex P k hkn i) := by
  rfl

private lemma lowerStep_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hk0 : 0 < k) (hkn : k ≤ P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr hkn⟩ = c) (f : ℝ → ℝ) (i : Fin k) :
    lowerStep (splitLeft P k hk0 hkn c hc) f i =
      lowerStep P f (leftCellIndex P k hkn i) := by
  rfl

private lemma upperStep_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f : ℝ → ℝ)
    (j : Fin (P.n - k)) :
    upperStep (splitRight P k hkn c hc) f j =
      upperStep P f (rightCellIndex P k (le_of_lt hkn) j) := by
  rfl

private lemma lowerStep_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f : ℝ → ℝ)
    (j : Fin (P.n - k)) :
    lowerStep (splitRight P k hkn c hc) f j =
      lowerStep P f (rightCellIndex P k (le_of_lt hkn) j) := by
  rfl

private def upperTermAtNat {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  upperStepAtNat P f i * (α (pointAtNat P (i + 1)) - α (pointAtNat P i))

private def lowerTermAtNat {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  lowerStepAtNat P f i * (α (pointAtNat P (i + 1)) - α (pointAtNat P i))

private def taggedTermAtNat {a b : ℝ} (P : Partition a b)
    (tags : Fin P.n → ℝ) (f α : ℝ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < P.n then
    let iFin : Fin P.n := ⟨i, hi⟩
    f (tags iFin) * (α (pointAtNat P (i + 1)) - α (pointAtNat P i))
  else 0

private lemma upperSum_eq_range {a b : ℝ} (P : Partition a b) (f α : ℝ → ℝ) :
    upperSum P f α = ∑ i ∈ Finset.range P.n, upperTermAtNat P f α i := by
  unfold upperSum
  calc
    (∑ i : Fin P.n,
        upperStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, upperTermAtNat P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [upperTermAtNat, upperStepAtNat_eq P f i.isLt,
            pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
            pointAtNat_eq P (Nat.le_of_lt i.isLt)]
          rfl
    _ = _ := Fin.sum_univ_eq_sum_range (upperTermAtNat P f α) P.n

private lemma lowerSum_eq_range {a b : ℝ} (P : Partition a b) (f α : ℝ → ℝ) :
    lowerSum P f α = ∑ i ∈ Finset.range P.n, lowerTermAtNat P f α i := by
  unfold lowerSum
  calc
    (∑ i : Fin P.n,
        lowerStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, lowerTermAtNat P f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [lowerTermAtNat, lowerStepAtNat_eq P f i.isLt,
            pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
            pointAtNat_eq P (Nat.le_of_lt i.isLt)]
          rfl
    _ = _ := Fin.sum_univ_eq_sum_range (lowerTermAtNat P f α) P.n

private lemma taggedSum_eq_range {a b : ℝ} (P : Partition a b)
    (tags : Fin P.n → ℝ) (f α : ℝ → ℝ) :
    taggedSum P tags f α =
      ∑ i ∈ Finset.range P.n, taggedTermAtNat P tags f α i := by
  unfold taggedSum
  calc
    (∑ i : Fin P.n,
        f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n, taggedTermAtNat P tags f α i.val := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [taggedTermAtNat, dif_pos i.isLt,
            pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
            pointAtNat_eq P (Nat.le_of_lt i.isLt)]
          rfl
    _ = _ := Fin.sum_univ_eq_sum_range (taggedTermAtNat P tags f α) P.n

private lemma upperTermAtNat_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ)
    {i : ℕ} (hi : i < k) :
    upperTermAtNat (splitLeft P k hk0 (le_of_lt hkn) c hc) f α i =
      upperTermAtNat P f α i := by
  rw [upperTermAtNat, upperTermAtNat,
    upperStepAtNat_eq _ f hi, upperStepAtNat_eq P f (lt_trans hi hkn),
    pointAtNat_eq _ (Nat.succ_le_of_lt hi), pointAtNat_eq _ (Nat.le_of_lt hi),
    pointAtNat_eq P (Nat.succ_le_of_lt (lt_trans hi hkn)),
    pointAtNat_eq P (Nat.le_of_lt (lt_trans hi hkn))]
  change upperStep (splitLeft P k hk0 (le_of_lt hkn) c hc) f ⟨i, hi⟩ * _ =
    upperStep P f ⟨i, lt_trans hi hkn⟩ * _
  rw [upperStep_splitLeft]
  rfl

private lemma lowerTermAtNat_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ)
    {i : ℕ} (hi : i < k) :
    lowerTermAtNat (splitLeft P k hk0 (le_of_lt hkn) c hc) f α i =
      lowerTermAtNat P f α i := by
  rw [lowerTermAtNat, lowerTermAtNat,
    lowerStepAtNat_eq _ f hi, lowerStepAtNat_eq P f (lt_trans hi hkn),
    pointAtNat_eq _ (Nat.succ_le_of_lt hi), pointAtNat_eq _ (Nat.le_of_lt hi),
    pointAtNat_eq P (Nat.succ_le_of_lt (lt_trans hi hkn)),
    pointAtNat_eq P (Nat.le_of_lt (lt_trans hi hkn))]
  change lowerStep (splitLeft P k hk0 (le_of_lt hkn) c hc) f ⟨i, hi⟩ * _ =
    lowerStep P f ⟨i, lt_trans hi hkn⟩ * _
  rw [lowerStep_splitLeft]
  rfl

private lemma upperTermAtNat_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ)
    {j : ℕ} (hj : j < P.n - k) :
    upperTermAtNat (splitRight P k hkn c hc) f α j =
      upperTermAtNat P f α (k + j) := by
  have hkj : k + j < P.n := by omega
  rw [upperTermAtNat, upperTermAtNat,
    upperStepAtNat_eq _ f hj, upperStepAtNat_eq P f hkj,
    pointAtNat_eq _ (Nat.succ_le_of_lt hj), pointAtNat_eq _ (Nat.le_of_lt hj),
    pointAtNat_eq P (Nat.succ_le_of_lt hkj), pointAtNat_eq P (Nat.le_of_lt hkj)]
  change upperStep (splitRight P k hkn c hc) f ⟨j, hj⟩ * _ =
    upperStep P f ⟨k + j, hkj⟩ * _
  rw [upperStep_splitRight]
  congr 2 <;> apply congrArg α <;> apply congrArg P.pts <;> apply Fin.ext <;> simp

private lemma lowerTermAtNat_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ)
    {j : ℕ} (hj : j < P.n - k) :
    lowerTermAtNat (splitRight P k hkn c hc) f α j =
      lowerTermAtNat P f α (k + j) := by
  have hkj : k + j < P.n := by omega
  rw [lowerTermAtNat, lowerTermAtNat,
    lowerStepAtNat_eq _ f hj, lowerStepAtNat_eq P f hkj,
    pointAtNat_eq _ (Nat.succ_le_of_lt hj), pointAtNat_eq _ (Nat.le_of_lt hj),
    pointAtNat_eq P (Nat.succ_le_of_lt hkj), pointAtNat_eq P (Nat.le_of_lt hkj)]
  change lowerStep (splitRight P k hkn c hc) f ⟨j, hj⟩ * _ =
    lowerStep P f ⟨k + j, hkj⟩ * _
  rw [lowerStep_splitRight]
  congr 2 <;> apply congrArg α <;> apply congrArg P.pts <;> apply Fin.ext <;> simp

private lemma upperSum_split {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ) :
    upperSum P f α =
      upperSum (splitLeft P k hk0 (le_of_lt hkn) c hc) f α +
        upperSum (splitRight P k hkn c hc) f α := by
  rw [upperSum_eq_range, upperSum_eq_range, upperSum_eq_range]
  have hsplit : k + (P.n - k) = P.n := by omega
  have hPsplit :
      (∑ i ∈ Finset.range P.n, upperTermAtNat P f α i) =
        (∑ i ∈ Finset.range k, upperTermAtNat P f α i) +
          ∑ j ∈ Finset.range (P.n - k), upperTermAtNat P f α (k + j) := by
    rw [← Finset.sum_range_add, hsplit]
  rw [hPsplit]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    exact (upperTermAtNat_splitLeft P k hk0 hkn c hc f α
      (Finset.mem_range.mp hi)).symm
  · refine Finset.sum_congr rfl ?_
    intro j hj
    exact (upperTermAtNat_splitRight P k hkn c hc f α
      (Finset.mem_range.mp hj)).symm

private lemma lowerSum_split {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) (f α : ℝ → ℝ) :
    lowerSum P f α =
      lowerSum (splitLeft P k hk0 (le_of_lt hkn) c hc) f α +
        lowerSum (splitRight P k hkn c hc) f α := by
  rw [lowerSum_eq_range, lowerSum_eq_range, lowerSum_eq_range]
  have hsplit : k + (P.n - k) = P.n := by omega
  have hPsplit :
      (∑ i ∈ Finset.range P.n, lowerTermAtNat P f α i) =
        (∑ i ∈ Finset.range k, lowerTermAtNat P f α i) +
          ∑ j ∈ Finset.range (P.n - k), lowerTermAtNat P f α (k + j) := by
    rw [← Finset.sum_range_add, hsplit]
  rw [hPsplit]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    exact (lowerTermAtNat_splitLeft P k hk0 hkn c hc f α
      (Finset.mem_range.mp hi)).symm
  · refine Finset.sum_congr rfl ?_
    intro j hj
    exact (lowerTermAtNat_splitRight P k hkn c hc f α
      (Finset.mem_range.mp hj)).symm

private lemma partition_length_le_mesh {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup' (s := (Finset.univ : Finset (Fin P.n)))
    (f := fun j => P.pts j.succ - P.pts j.castSucc) (Finset.mem_univ i)

private lemma mesh_splitLeft_le {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) :
    (splitLeft P k hk0 (le_of_lt hkn) c hc).mesh ≤ P.mesh := by
  change (Finset.univ.sup' ⟨(⟨0, hk0⟩ : Fin k), Finset.mem_univ _⟩
      (fun i : Fin k =>
        (splitLeft P k hk0 (le_of_lt hkn) c hc).pts i.succ -
          (splitLeft P k hk0 (le_of_lt hkn) c hc).pts i.castSucc)) ≤ P.mesh
  apply Finset.sup'_le
  intro i _
  simpa [splitLeft, leftNodeIndex, leftCellIndex] using
    partition_length_le_mesh P (leftCellIndex P k (le_of_lt hkn) i)

private lemma mesh_splitRight_le {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c) :
    (splitRight P k hkn c hc).mesh ≤ P.mesh := by
  change (Finset.univ.sup'
      ⟨(⟨0, Nat.sub_pos_of_lt hkn⟩ : Fin (P.n - k)), Finset.mem_univ _⟩
      (fun j : Fin (P.n - k) =>
        (splitRight P k hkn c hc).pts j.succ -
          (splitRight P k hkn c hc).pts j.castSucc)) ≤ P.mesh
  apply Finset.sup'_le
  intro j _
  have hlen := partition_length_le_mesh P (rightCellIndex P k (le_of_lt hkn) j)
  change P.pts (rightNodeIndex P k (le_of_lt hkn) j.succ) -
      P.pts (rightNodeIndex P k (le_of_lt hkn) j.castSucc) ≤ P.mesh
  rw [show rightNodeIndex P k (le_of_lt hkn) j.succ =
      (rightCellIndex P k (le_of_lt hkn) j).succ by
    apply Fin.ext
    simp [rightNodeIndex, rightCellIndex, Nat.add_assoc],
    show rightNodeIndex P k (le_of_lt hkn) j.castSucc =
      (rightCellIndex P k (le_of_lt hkn) j).castSucc by
    apply Fin.ext
    simp [rightNodeIndex, rightCellIndex]]
  exact hlen

private def insTags {n : ℕ} (tags : Fin n → ℝ) (k : Fin n) (d : ℝ) : Fin (n + 1) → ℝ :=
  fun j =>
    if hj : j.val < k.val then tags ⟨j.val, by omega⟩
    else if hj' : j.val ≤ k.val + 1 then d
    else tags ⟨j.val - 1, by omega⟩

private lemma insTags_lt {n : ℕ} (tags : Fin n → ℝ) (k : Fin n) (d : ℝ)
    {j : Fin (n + 1)} (hj : j.val < k.val) :
    insTags tags k d j = tags ⟨j.val, by omega⟩ := by
  simp [insTags, hj]

private lemma insTags_seamL {n : ℕ} (tags : Fin n → ℝ) (k : Fin n) (d : ℝ) :
    insTags tags k d k.castSucc = d := by
  simp [insTags]

private lemma insTags_seamR {n : ℕ} (tags : Fin n → ℝ) (k : Fin n) (d : ℝ) :
    insTags tags k d k.succ = d := by
  simp [insTags]

private lemma insTags_gt {n : ℕ} (tags : Fin n → ℝ) (k : Fin n) (d : ℝ)
    {j : Fin (n + 1)} (hj : k.val + 1 < j.val) :
    insTags tags k d j = tags ⟨j.val - 1, by omega⟩ := by
  simp [insTags, show ¬j.val < k.val by omega,
    show ¬j.val ≤ k.val + 1 by omega]

private lemma tagsInPartition_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c)
    (tags : Fin P.n → ℝ) (htags : tagsInPartition P tags) :
    tagsInPartition (splitLeft P k hk0 (le_of_lt hkn) c hc)
      (fun i => tags (leftCellIndex P k (le_of_lt hkn) i)) := by
  intro i
  change tags (leftCellIndex P k (le_of_lt hkn) i) ∈
    subinterval P (leftCellIndex P k (le_of_lt hkn) i)
  exact htags (leftCellIndex P k (le_of_lt hkn) i)

private lemma tagsInPartition_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = c)
    (tags : Fin P.n → ℝ) (htags : tagsInPartition P tags) :
    tagsInPartition (splitRight P k hkn c hc)
      (fun j => tags (rightCellIndex P k (le_of_lt hkn) j)) := by
  intro j
  change tags (rightCellIndex P k (le_of_lt hkn) j) ∈
    subinterval P (rightCellIndex P k (le_of_lt hkn) j)
  exact htags (rightCellIndex P k (le_of_lt hkn) j)

private def insPts {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) : Fin (P.n + 2) → ℝ :=
  fun j =>
    if hj : j.val ≤ k then P.pts ⟨j.val, by omega⟩
    else if hj' : j.val = k + 1 then c
    else P.pts ⟨j.val - 1, by omega⟩

private lemma insPts_le {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) {j : Fin (P.n + 2)} (hj : j.val ≤ k) :
    insPts P k hkn c j = P.pts ⟨j.val, by omega⟩ := by
  simp [insPts, hj]

private lemma insPts_seam {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) :
    insPts P k hkn c ⟨k + 1, by omega⟩ = c := by
  simp [insPts]

private lemma insPts_gt {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) {j : Fin (P.n + 2)} (hj : k + 1 < j.val) :
    insPts P k hkn c j = P.pts ⟨j.val - 1, by omega⟩ := by
  have h1 : ¬ j.val ≤ k := by omega
  have h2 : j.val ≠ k + 1 := by omega
  simp [insPts, h1, h2]

private def insertPoint {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc1 : pointAtNat P k < c)
    (hc2 : c < pointAtNat P (k + 1)) : Partition a b where
  n := P.n + 1
  hn := by omega
  pts := insPts P k hkn c
  pts_start := by
    rw [insPts_le P k hkn c (Nat.zero_le k)]
    simpa using P.pts_start
  pts_end := by
    rw [insPts_gt P k hkn c (by simp; omega)]
    rw [show (⟨(Fin.last (P.n + 1)).val - 1, by omega⟩ : Fin (P.n + 1)) =
        Fin.last P.n by
      apply Fin.ext
      simp]
    exact P.pts_end
  strict_mono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    by_cases hjk : j.val < k
    · rw [insPts_le P k hkn c (le_of_lt hjk),
        insPts_le P k hkn c (by simp; omega)]
      exact P.strict_mono Fin.castSucc_lt_succ
    · by_cases hjkeq : j.val = k
      · simpa [insPts, hjkeq, pointAtNat, Nat.le_of_lt hkn] using hc1
      · by_cases hjk1eq : j.val = k + 1
        · simpa [insPts, hjk1eq, pointAtNat, Nat.succ_le_of_lt hkn] using hc2
        · have hjgt : k + 1 < j.val := by omega
          rw [insPts_gt P k hkn c hjgt,
            insPts_gt P k hkn c (by simp; omega)]
          apply P.strict_mono
          change j.val - 1 < (j.val + 1) - 1
          omega

private lemma insertPoint_pts_eq {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc1 : pointAtNat P k < c) (hc2 : c < pointAtNat P (k + 1)) :
    (insertPoint P k hkn c hc1 hc2).pts = insPts P k hkn c := rfl

private lemma insertPoint_pts_seam {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ)
    (hc1 : pointAtNat P k < c) (hc2 : c < pointAtNat P (k + 1)) :
    (insertPoint P k hkn c hc1 hc2).pts
      (Fin.cast (by simp [insertPoint]) (⟨k + 1, by omega⟩ : Fin (P.n + 2))) = c := by
  change insPts P k hkn c ⟨k + 1, by omega⟩ = c
  exact insPts_seam P k hkn c

private lemma pointAtNat_insert_le {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ) (hc1 : pointAtNat P k < c)
    (hc2 : c < pointAtNat P (k + 1)) {i : ℕ} (hi : i ≤ k) :
    pointAtNat (insertPoint P k hkn c hc1 hc2) i = pointAtNat P i := by
  rw [pointAtNat_eq _ (by simp [insertPoint]; omega), pointAtNat_eq P (by omega)]
  simp only [insertPoint_pts_eq]
  rw [insPts_le P k hkn c hi]

private lemma pointAtNat_insert_seam {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ) (hc1 : pointAtNat P k < c)
    (hc2 : c < pointAtNat P (k + 1)) :
    pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) = c := by
  rw [pointAtNat_eq _ (by simp [insertPoint]; omega)]
  simpa using insertPoint_pts_seam P k hkn c hc1 hc2

private lemma pointAtNat_insert_shift {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ) (hc1 : pointAtNat P k < c)
    (hc2 : c < pointAtNat P (k + 1)) (j : ℕ) (hj : k + (j + 1) ≤ P.n) :
    pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1)) =
      pointAtNat P (k + (j + 1)) := by
  rw [pointAtNat_eq _ (by simp [insertPoint]; omega), pointAtNat_eq P hj]
  simp only [insertPoint_pts_eq]
  rw [insPts_gt P k hkn c (by simp)]
  congr 1
  apply Fin.ext
  simp
  omega

lemma sum_insert_diff (n k : ℕ) (hk : k < n)
    (u u' : ℕ → ℝ) (uL uR : ℝ)
    (hlt : ∀ i, i < k → u' i = u i)
    (hkL : u' k = uL)
    (hkR : u' (k + 1) = uR)
    (hgt : ∀ j, u' (k + 1 + (j + 1)) = u (k + (j + 1))) :
    ∑ i ∈ Finset.range n, u i =
      (∑ i ∈ Finset.range (n + 1), u' i) - (uL + uR) + u k := by
  -- Split range n at k: [0,k) ++ {k+j : j < n-k}
  have hsplitn : k + (n - k) = n := by omega
  have hnk : n - k = (n - k - 1) + 1 := by omega
  -- LHS
  have hLHS : ∑ i ∈ Finset.range n, u i
      = (∑ i ∈ Finset.range k, u i)
        + ∑ j ∈ Finset.range (n - k), u (k + j) := by
    conv_lhs => rw [← hsplitn, Finset.sum_range_add]
  -- RHS sum over range (n+1): split at k+1 into [0,k+1) ++ shifted
  have hsplitn1 : (k + 1) + (n - k) = n + 1 := by omega
  have hRHS : ∑ i ∈ Finset.range (n + 1), u' i
      = (∑ i ∈ Finset.range (k + 1), u' i)
        + ∑ j ∈ Finset.range (n - k), u' (k + 1 + j) := by
    conv_lhs => rw [← hsplitn1, Finset.sum_range_add]
  -- Decompose the u-tail: peel index 0.
  have hUtail : ∑ j ∈ Finset.range (n - k), u (k + j)
      = (∑ j ∈ Finset.range (n - k - 1), u (k + (j + 1))) + u k := by
    rw [hnk, Finset.sum_range_succ']
    simp
  -- Decompose the u'-left block range (k+1): peel last index k.
  have hU'left : ∑ i ∈ Finset.range (k + 1), u' i
      = (∑ i ∈ Finset.range k, u' i) + u' k :=
    Finset.sum_range_succ (fun i => u' i) k
  -- Decompose the u'-tail: peel index 0.
  have hU'tail : ∑ j ∈ Finset.range (n - k), u' (k + 1 + j)
      = (∑ j ∈ Finset.range (n - k - 1), u' (k + 1 + (j + 1))) + u' (k + 1) := by
    rw [hnk, Finset.sum_range_succ']
    simp
  -- Termwise equalities.
  have hleft : ∑ i ∈ Finset.range k, u' i = ∑ i ∈ Finset.range k, u i :=
    Finset.sum_congr rfl (fun i hi => hlt i (Finset.mem_range.mp hi))
  have htail : ∑ j ∈ Finset.range (n - k - 1), u' (k + 1 + (j + 1))
      = ∑ j ∈ Finset.range (n - k - 1), u (k + (j + 1)) :=
    Finset.sum_congr rfl (fun j _ => hgt j)
  rw [hLHS, hRHS, hUtail, hU'left, hU'tail, hleft, htail, hkL, hkR]
  ring

variable {a b : ℝ}

section InsertCells
variable (P : Partition a b) (k : ℕ) (hkn : k < P.n)
  (c : ℝ) (hc1 : pointAtNat P k < c) (hc2 : c < pointAtNat P (k + 1))

private lemma insert_subinterval_lt {i : ℕ} (hi : i < k) :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) i =
      subintervalAtNat P i := by
  unfold subintervalAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos (lt_trans hi hkn)]
  rw [pointAtNat_insert_le P k hkn c hc1 hc2 (le_of_lt hi),
    pointAtNat_insert_le P k hkn c hc1 hc2 (by omega)]

private lemma insert_subinterval_seamL :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) k =
      Icc (pointAtNat P k) c := by
  unfold subintervalAtNat
  rw [dif_pos (by simp [insertPoint]; omega)]
  rw [pointAtNat_insert_le P k hkn c hc1 hc2 le_rfl,
    pointAtNat_insert_seam P k hkn c hc1 hc2]

private lemma insert_subinterval_seamR :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) =
      Icc c (pointAtNat P (k + 1)) := by
  unfold subintervalAtNat
  rw [dif_pos (by simp [insertPoint]; omega)]
  rw [pointAtNat_insert_seam P k hkn c hc1 hc2]
  have hshift := pointAtNat_insert_shift P k hkn c hc1 hc2 0
    (Nat.succ_le_of_lt hkn)
  exact congrArg (fun x => Icc c x) (by simpa using hshift)

private lemma insert_subinterval_gt (j : ℕ) (hj : k + (j + 1) < P.n) :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1)) =
      subintervalAtNat P (k + (j + 1)) := by
  unfold subintervalAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos hj]
  rw [pointAtNat_insert_shift P k hkn c hc1 hc2 j (Nat.le_of_lt hj)]
  have hshift := pointAtNat_insert_shift P k hkn c hc1 hc2 (j + 1) (by omega)
  exact congrArg (fun x => Icc (pointAtNat P (k + (j + 1))) x)
    (by simpa only [Nat.add_assoc] using hshift)

private lemma insert_upperStep_lt (f : ℝ → ℝ) {i : ℕ} (hi : i < k) :
    upperStepAtNat (insertPoint P k hkn c hc1 hc2) f i =
      upperStepAtNat P f i := by
  unfold upperStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos (lt_trans hi hkn)]
  rw [insert_subinterval_lt P k hkn c hc1 hc2 hi]

private lemma insert_lowerStep_lt (f : ℝ → ℝ) {i : ℕ} (hi : i < k) :
    lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f i =
      lowerStepAtNat P f i := by
  unfold lowerStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos (lt_trans hi hkn)]
  rw [insert_subinterval_lt P k hkn c hc1 hc2 hi]

private lemma insert_upperStep_gt (f : ℝ → ℝ) (j : ℕ)
    (hj : k + (j + 1) < P.n) :
    upperStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1 + (j + 1)) =
      upperStepAtNat P f (k + (j + 1)) := by
  unfold upperStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos hj]
  rw [insert_subinterval_gt P k hkn c hc1 hc2 j hj]

private lemma insert_lowerStep_gt (f : ℝ → ℝ) (j : ℕ)
    (hj : k + (j + 1) < P.n) :
    lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1 + (j + 1)) =
      lowerStepAtNat P f (k + (j + 1)) := by
  unfold lowerStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos hj]
  rw [insert_subinterval_gt P k hkn c hc1 hc2 j hj]

private lemma insert_pts_lt {i : ℕ} (hi : i ≤ k) :
    pointAtNat (insertPoint P k hkn c hc1 hc2) i = pointAtNat P i := by
  exact pointAtNat_insert_le P k hkn c hc1 hc2 hi

private lemma insert_pts_ge (j : ℕ) (hj : k + (j + 1) ≤ P.n) :
    pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1)) =
      pointAtNat P (k + (j + 1)) := by
  exact pointAtNat_insert_shift P k hkn c hc1 hc2 j hj

private lemma insert_pts_seam :
    pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) = c := by
  exact pointAtNat_insert_seam P k hkn c hc1 hc2

private lemma upperSum_insert_eq (f α : ℝ → ℝ) :
    upperSum P f α =
      upperSum (insertPoint P k hkn c hc1 hc2) f α
        - (upperStepAtNat (insertPoint P k hkn c hc1 hc2) f k *
              (α c - α (pointAtNat P k))
            + upperStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) *
              (α (pointAtNat P (k + 1)) - α c))
        + upperStepAtNat P f k *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) := by
  let P' := insertPoint P k hkn c hc1 hc2
  have key := sum_insert_diff P.n k hkn
    (upperTermAtNat P f α) (upperTermAtNat P' f α)
    (upperStepAtNat P' f k * (α c - α (pointAtNat P k)))
    (upperStepAtNat P' f (k + 1) * (α (pointAtNat P (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · rw [upperSum_eq_range P, upperSum_eq_range P']
    exact key
  case hlt =>
    intro i hi
    unfold upperTermAtNat
    rw [insert_upperStep_lt P k hkn c hc1 hc2 f hi,
      insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
      insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    unfold upperTermAtNat
    rw [insert_pts_lt P k hkn c hc1 hc2 le_rfl,
      insert_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    unfold upperTermAtNat
    rw [insert_pts_seam P k hkn c hc1 hc2,
      insert_pts_ge P k hkn c hc1 hc2 0 (by omega)]
  case hgt =>
    intro j
    dsimp [P']
    by_cases hj : k + (j + 1) < P.n
    · have hshiftNext :
          pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1) + 1) =
            pointAtNat P (k + (j + 1) + 1) := by
        simpa only [Nat.add_assoc] using
          pointAtNat_insert_shift P k hkn c hc1 hc2 (j + 1) (by omega)
      unfold upperTermAtNat
      rw [insert_upperStep_gt P k hkn c hc1 hc2 f j hj,
        insert_pts_ge P k hkn c hc1 hc2 j (Nat.le_of_lt hj),
        hshiftNext]
    · have hnew : ¬ k + 1 + (j + 1) <
          (insertPoint P k hkn c hc1 hc2).n := by simp [insertPoint]; omega
      simp [upperTermAtNat, upperStepAtNat, hj, hnew]

private lemma lowerSum_insert_eq (f α : ℝ → ℝ) :
    lowerSum P f α =
      lowerSum (insertPoint P k hkn c hc1 hc2) f α
        - (lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f k *
              (α c - α (pointAtNat P k))
            + lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) *
              (α (pointAtNat P (k + 1)) - α c))
        + lowerStepAtNat P f k *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) := by
  let P' := insertPoint P k hkn c hc1 hc2
  have key := sum_insert_diff P.n k hkn
    (lowerTermAtNat P f α) (lowerTermAtNat P' f α)
    (lowerStepAtNat P' f k * (α c - α (pointAtNat P k)))
    (lowerStepAtNat P' f (k + 1) * (α (pointAtNat P (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · rw [lowerSum_eq_range P, lowerSum_eq_range P']
    exact key
  case hlt =>
    intro i hi
    unfold lowerTermAtNat
    rw [insert_lowerStep_lt P k hkn c hc1 hc2 f hi,
      insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
      insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    unfold lowerTermAtNat
    rw [insert_pts_lt P k hkn c hc1 hc2 le_rfl,
      insert_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    unfold lowerTermAtNat
    rw [insert_pts_seam P k hkn c hc1 hc2,
      insert_pts_ge P k hkn c hc1 hc2 0 (by omega)]
  case hgt =>
    intro j
    dsimp [P']
    by_cases hj : k + (j + 1) < P.n
    · have hshiftNext :
          pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1) + 1) =
            pointAtNat P (k + (j + 1) + 1) := by
        simpa only [Nat.add_assoc] using
          pointAtNat_insert_shift P k hkn c hc1 hc2 (j + 1) (by omega)
      unfold lowerTermAtNat
      rw [insert_lowerStep_gt P k hkn c hc1 hc2 f j hj,
        insert_pts_ge P k hkn c hc1 hc2 j (Nat.le_of_lt hj),
        hshiftNext]
    · have hnew : ¬ k + 1 + (j + 1) <
          (insertPoint P k hkn c hc1 hc2).n := by simp [insertPoint]; omega
      simp [lowerTermAtNat, lowerStepAtNat, hj, hnew]

private lemma insert_seamL_subset :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) k ⊆
      subintervalAtNat P k := by
  rw [insert_subinterval_seamL P k hkn c hc1 hc2]
  rw [subintervalAtNat_eq P hkn]
  unfold subinterval Partition.subinterval
  intro x hx
  have hc2' : c < P.pts (⟨k, hkn⟩ : Fin P.n).succ := by
    simpa [pointAtNat, Nat.succ_le_of_lt hkn] using hc2
  have hx1 : P.pts (⟨k, hkn⟩ : Fin P.n).castSucc ≤ x := by
    simpa [pointAtNat, Nat.le_of_lt hkn] using hx.1
  exact ⟨hx1, le_trans hx.2 (le_of_lt hc2')⟩

private lemma insert_seamR_subset :
    subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) ⊆
      subintervalAtNat P k := by
  rw [insert_subinterval_seamR P k hkn c hc1 hc2]
  rw [subintervalAtNat_eq P hkn]
  unfold subinterval Partition.subinterval
  intro x hx
  have hc1' : P.pts (⟨k, hkn⟩ : Fin P.n).castSucc < c := by
    simpa [pointAtNat, Nat.le_of_lt hkn] using hc1
  have hx2 : x ≤ P.pts (⟨k, hkn⟩ : Fin P.n).succ := by
    simpa [pointAtNat, Nat.succ_le_of_lt hkn] using hx.2
  exact ⟨le_trans (le_of_lt hc1') hx.1, hx2⟩

include hkn in
private lemma cell_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subintervalAtNat P k) := by
  rw [subintervalAtNat_eq P hkn]
  exact BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

include hkn in
private lemma cell_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subintervalAtNat P k) := by
  rw [subintervalAtNat_eq P hkn]
  exact BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

private lemma seam_upperStep_le_L (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    upperStepAtNat (insertPoint P k hkn c hc1 hc2) f k ≤
      upperStepAtNat P f k := by
  unfold upperStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos hkn]
  refine csSup_le_csSup (cell_bddAbove P k hkn f hAbove) ?_
    (Set.image_mono (insert_seamL_subset P k hkn c hc1 hc2))
  refine ⟨f (pointAtNat P k), pointAtNat P k, ?_, rfl⟩
  rw [insert_subinterval_seamL P k hkn c hc1 hc2]
  exact ⟨le_rfl, le_of_lt hc1⟩

private lemma seam_upperStep_le_R (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    upperStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤
      upperStepAtNat P f k := by
  unfold upperStepAtNat
  rw [dif_pos (by simp [insertPoint]; omega), dif_pos hkn]
  refine csSup_le_csSup (cell_bddAbove P k hkn f hAbove) ?_
    (Set.image_mono (insert_seamR_subset P k hkn c hc1 hc2))
  refine ⟨f c, c, ?_, rfl⟩
  rw [insert_subinterval_seamR P k hkn c hc1 hc2]
  exact ⟨le_rfl, le_of_lt hc2⟩

private lemma seamL_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) k) := by
  apply BddAbove.mono (Set.image_mono ?_) hAbove
  intro x hx
  have hxP := insert_seamL_subset P k hkn c hc1 hc2 hx
  rw [subintervalAtNat_eq P hkn] at hxP
  exact subinterval_subset_Icc_core P hxP

private lemma seamR_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1)) := by
  apply BddAbove.mono (Set.image_mono ?_) hAbove
  intro x hx
  have hxP := insert_seamR_subset P k hkn c hc1 hc2 hx
  rw [subintervalAtNat_eq P hkn] at hxP
  exact subinterval_subset_Icc_core P hxP

private lemma seam_lowerStep_le_upperStep_L (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat P f k ≤ upperStepAtNat (insertPoint P k hkn c hc1 hc2) f k := by
  -- pick x = P.pts k in the left seam sub-cell
  have hxmem : pointAtNat P k ∈
      subintervalAtNat (insertPoint P k hkn c hc1 hc2) k := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc1⟩
  have hxcell : pointAtNat P k ∈ subintervalAtNat P k :=
    insert_seamL_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStepAtNat P f k ≤ f (pointAtNat P k) := by
    unfold lowerStepAtNat
    rw [dif_pos hkn]
    exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨pointAtNat P k, hxcell, rfl⟩
  have h2 : f (pointAtNat P k) ≤
      upperStepAtNat (insertPoint P k hkn c hc1 hc2) f k := by
    unfold upperStepAtNat
    rw [dif_pos (by simp [insertPoint]; omega)]
    exact le_csSup (seamL_bddAbove P k hkn c hc1 hc2 f hAbove)
      ⟨pointAtNat P k, hxmem, rfl⟩
  exact le_trans h1 h2

private lemma seam_lowerStep_le_upperStep_R (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat P f k ≤
      upperStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) := by
  have hxmem : c ∈ subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc2⟩
  have hxcell : c ∈ subintervalAtNat P k :=
    insert_seamR_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStepAtNat P f k ≤ f c := by
    unfold lowerStepAtNat
    rw [dif_pos hkn]
    exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨c, hxcell, rfl⟩
  have h2 : f c ≤ upperStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) := by
    unfold upperStepAtNat
    rw [dif_pos (by simp [insertPoint]; omega)]
    exact le_csSup (seamR_bddAbove P k hkn c hc1 hc2 f hAbove) ⟨c, hxmem, rfl⟩
  exact le_trans h1 h2

private lemma seamL_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) k) := by
  apply BddBelow.mono (Set.image_mono ?_) hBelow
  intro x hx
  have hxP := insert_seamL_subset P k hkn c hc1 hc2 hx
  rw [subintervalAtNat_eq P hkn] at hxP
  exact subinterval_subset_Icc_core P hxP

private lemma seamR_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1)) := by
  apply BddBelow.mono (Set.image_mono ?_) hBelow
  intro x hx
  have hxP := insert_seamR_subset P k hkn c hc1 hc2 hx
  rw [subintervalAtNat_eq P hkn] at hxP
  exact subinterval_subset_Icc_core P hxP

private lemma seam_lowerStep_ge_L (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat P f k ≤
      lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f k := by
  have hne : (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) k).Nonempty := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]
    exact ⟨f (pointAtNat P k), pointAtNat P k, ⟨le_rfl, le_of_lt hc1⟩, rfl⟩
  unfold lowerStepAtNat
  rw [dif_pos hkn, dif_pos (by simp [insertPoint]; omega)]
  refine le_csInf hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hxcell : x ∈ subintervalAtNat P k := insert_seamL_subset P k hkn c hc1 hc2 hx
  exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨x, hxcell, rfl⟩

private lemma seam_lowerStep_ge_R (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat P f k ≤
      lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) := by
  have hne : (f '' subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1)).Nonempty := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]
    exact ⟨f c, c, ⟨le_rfl, le_of_lt hc2⟩, rfl⟩
  unfold lowerStepAtNat
  rw [dif_pos hkn, dif_pos (by simp [insertPoint]; omega)]
  refine le_csInf hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hxcell : x ∈ subintervalAtNat P k := insert_seamR_subset P k hkn c hc1 hc2 hx
  exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨x, hxcell, rfl⟩

private lemma seam_lowerStep_le_upper_L (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f k ≤
      upperStepAtNat P f k := by
  have hxmem : pointAtNat P k ∈
      subintervalAtNat (insertPoint P k hkn c hc1 hc2) k := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc1⟩
  have hxcell : pointAtNat P k ∈ subintervalAtNat P k :=
    insert_seamL_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f k ≤
      f (pointAtNat P k) := by
    unfold lowerStepAtNat
    rw [dif_pos (by simp [insertPoint]; omega)]
    exact csInf_le (seamL_bddBelow P k hkn c hc1 hc2 f hBelow)
      ⟨pointAtNat P k, hxmem, rfl⟩
  have h2 : f (pointAtNat P k) ≤ upperStepAtNat P f k := by
    unfold upperStepAtNat
    rw [dif_pos hkn]
    exact le_csSup (cell_bddAbove P k hkn f hAbove) ⟨pointAtNat P k, hxcell, rfl⟩
  exact le_trans h1 h2

private lemma seam_lowerStep_le_upper_R (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤
      upperStepAtNat P f k := by
  have hxmem : c ∈ subintervalAtNat (insertPoint P k hkn c hc1 hc2) (k + 1) := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc2⟩
  have hxcell : c ∈ subintervalAtNat P k :=
    insert_seamR_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStepAtNat (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤ f c := by
    unfold lowerStepAtNat
    rw [dif_pos (by simp [insertPoint]; omega)]
    exact csInf_le (seamR_bddBelow P k hkn c hc1 hc2 f hBelow) ⟨c, hxmem, rfl⟩
  have h2 : f c ≤ upperStepAtNat P f k := by
    unfold upperStepAtNat
    rw [dif_pos hkn]
    exact le_csSup (cell_bddAbove P k hkn f hAbove) ⟨c, hxcell, rfl⟩
  exact le_trans h1 h2

include hkn in
private lemma cptk_mem : pointAtNat P k ∈ Icc a b := by
  rw [pointAtNat_eq P (Nat.le_of_lt hkn)]
  exact partition_pts_mem_Icc_core P

include hkn in
private lemma cptk1_mem : pointAtNat P (k + 1) ∈ Icc a b := by
  rw [pointAtNat_eq P (Nat.succ_le_of_lt hkn)]
  exact partition_pts_mem_Icc_core P

include hkn hc1 hc2 in
private lemma c_mem : c ∈ Icc a b := by
  have h1 := cptk_mem P k hkn
  have h2 := cptk1_mem P k hkn
  exact ⟨le_trans h1.1 (le_of_lt hc1), le_trans (le_of_lt hc2) h2.2⟩

private lemma abs_upperSum_insert_le (f α : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    (hmono : MonotoneOn α (Icc a b)) :
    |upperSum P f α - upperSum (insertPoint P k hkn c hc1 hc2) f α|
      ≤ (upperStepAtNat P f k - lowerStepAtNat P f k)
          * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) := by
  set P' := insertPoint P k hkn c hc1 hc2 with hP'
  -- increments
  have hkmem := cptk_mem P k hkn
  have hk1mem := cptk1_mem P k hkn
  have hcmem := c_mem P k hkn c hc1 hc2
  have hdL : 0 ≤ α c - α (pointAtNat P k) :=
    sub_nonneg.mpr (hmono hkmem hcmem (le_of_lt hc1))
  have hdR : 0 ≤ α (pointAtNat P (k + 1)) - α c :=
    sub_nonneg.mpr (hmono hcmem hk1mem (le_of_lt hc2))
  -- sub-cell step bounds
  have hML_le : upperStepAtNat P' f k ≤ upperStepAtNat P f k :=
    seam_upperStep_le_L P k hkn c hc1 hc2 f hAbove
  have hMR_le : upperStepAtNat P' f (k + 1) ≤ upperStepAtNat P f k :=
    seam_upperStep_le_R P k hkn c hc1 hc2 f hAbove
  have hm_le_L : lowerStepAtNat P f k ≤ upperStepAtNat P' f k :=
    seam_lowerStep_le_upperStep_L P k hkn c hc1 hc2 f hAbove hBelow
  have hm_le_R : lowerStepAtNat P f k ≤ upperStepAtNat P' f (k + 1) :=
    seam_lowerStep_le_upperStep_R P k hkn c hc1 hc2 f hAbove hBelow
  -- the difference identity
  have hid := upperSum_insert_eq P k hkn c hc1 hc2 f α
  -- abbreviations
  set M := upperStepAtNat P f k
  set m := lowerStepAtNat P f k
  set ML := upperStepAtNat P' f k
  set MR := upperStepAtNat P' f (k + 1)
  set dL := α c - α (pointAtNat P k)
  set dR := α (pointAtNat P (k + 1)) - α c
  -- Δα_k = dL + dR
  have hsum : α (pointAtNat P (k + 1)) - α (pointAtNat P k) = dL + dR := by
    simp only [dL, dR]; ring
  rw [hsum]
  -- from identity: upperSum P - upperSum P' = M*(dL+dR) - (ML*dL + MR*dR)
  have hdiff : upperSum P f α - upperSum P' f α
      = M * (dL + dR) - (ML * dL + MR * dR) := by
    rw [hid]; ring
  rw [hdiff]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hm_le_L hdL,
      mul_le_mul_of_nonneg_right hm_le_R hdR]
  · nlinarith [mul_le_mul_of_nonneg_right hML_le hdL,
      mul_le_mul_of_nonneg_right hMR_le hdR]

private lemma abs_lowerSum_insert_le (f α : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    (hmono : MonotoneOn α (Icc a b)) :
    |lowerSum P f α - lowerSum (insertPoint P k hkn c hc1 hc2) f α|
      ≤ (upperStepAtNat P f k - lowerStepAtNat P f k)
          * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) := by
  set P' := insertPoint P k hkn c hc1 hc2 with hP'
  have hkmem := cptk_mem P k hkn
  have hk1mem := cptk1_mem P k hkn
  have hcmem := c_mem P k hkn c hc1 hc2
  have hdL : 0 ≤ α c - α (pointAtNat P k) :=
    sub_nonneg.mpr (hmono hkmem hcmem (le_of_lt hc1))
  have hdR : 0 ≤ α (pointAtNat P (k + 1)) - α c :=
    sub_nonneg.mpr (hmono hcmem hk1mem (le_of_lt hc2))
  have hmL_ge : lowerStepAtNat P f k ≤ lowerStepAtNat P' f k :=
    seam_lowerStep_ge_L P k hkn c hc1 hc2 f hBelow
  have hmR_ge : lowerStepAtNat P f k ≤ lowerStepAtNat P' f (k + 1) :=
    seam_lowerStep_ge_R P k hkn c hc1 hc2 f hBelow
  have hmL_le : lowerStepAtNat P' f k ≤ upperStepAtNat P f k :=
    seam_lowerStep_le_upper_L P k hkn c hc1 hc2 f hAbove hBelow
  have hmR_le : lowerStepAtNat P' f (k + 1) ≤ upperStepAtNat P f k :=
    seam_lowerStep_le_upper_R P k hkn c hc1 hc2 f hAbove hBelow
  have hid := lowerSum_insert_eq P k hkn c hc1 hc2 f α
  set M := upperStepAtNat P f k
  set m := lowerStepAtNat P f k
  set mL := lowerStepAtNat P' f k
  set mR := lowerStepAtNat P' f (k + 1)
  set dL := α c - α (pointAtNat P k)
  set dR := α (pointAtNat P (k + 1)) - α c
  have hsum : α (pointAtNat P (k + 1)) - α (pointAtNat P k) = dL + dR := by
    simp only [dL, dR]; ring
  rw [hsum]
  have hdiff : lowerSum P f α - lowerSum P' f α
      = m * (dL + dR) - (mL * dL + mR * dR) := by
    rw [hid]; ring
  rw [hdiff, abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hmL_le hdL,
      mul_le_mul_of_nonneg_right hmR_le hdR]
  · nlinarith [mul_le_mul_of_nonneg_right hmL_ge hdL,
      mul_le_mul_of_nonneg_right hmR_ge hdR]

include hkn hc1 hc2 in
lemma insert_gap_le_mesh (i : Fin (insertPoint P k hkn c hc1 hc2).n) :
    (insertPoint P k hkn c hc1 hc2).pts i.succ -
        (insertPoint P k hkn c hc1 hc2).pts i.castSucc ≤ P.mesh := by
  let P' := insertPoint P k hkn c hc1 hc2
  have hnext : pointAtNat P' (i.val + 1) = P'.pts i.succ := by
    rw [pointAtNat_eq P' (Nat.succ_le_of_lt i.isLt)]
    congr 1
  have hcur : pointAtNat P' i.val = P'.pts i.castSucc := by
    rw [pointAtNat_eq P' (Nat.le_of_lt i.isLt)]
    congr 1
  change P'.pts i.succ - P'.pts i.castSucc ≤ P.mesh
  rw [← hnext, ← hcur]
  have gapAtNat (j : ℕ) (hj : j < P.n) :
      pointAtNat P (j + 1) - pointAtNat P j ≤ P.mesh := by
    rw [pointAtNat_eq P (Nat.succ_le_of_lt hj),
      pointAtNat_eq P (Nat.le_of_lt hj)]
    simpa using partition_length_le_mesh P (⟨j, hj⟩ : Fin P.n)
  have hgapk := gapAtNat k hkn
  rcases lt_trichotomy i.val k with hlt | heq | hgt
  · -- i < k
    dsimp [P']
    rw [insert_pts_lt P k hkn c hc1 hc2 (by omega : i.val + 1 ≤ k),
      insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hlt)]
    exact gapAtNat i.val (lt_trans hlt hkn)
  · -- i = k : gap = c - P.pts k
    dsimp [P']
    rw [heq, insert_pts_seam P k hkn c hc1 hc2,
      insert_pts_lt P k hkn c hc1 hc2 le_rfl]
    linarith [le_of_lt hc2]
  · -- i > k
    rcases Nat.lt_or_ge i.val (k + 1) with h | h
    · omega
    · rcases Nat.eq_or_lt_of_le h with heq1 | hgt1
      · -- i = k + 1 : gap = P.pts (k+1) - c
        dsimp [P']
        rw [← heq1, insert_pts_seam P k hkn c hc1 hc2]
        have hshift := insert_pts_ge P k hkn c hc1 hc2 0
          (Nat.succ_le_of_lt hkn)
        rw [show pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + 1) =
            pointAtNat P (k + 1) by simpa using hshift]
        linarith [le_of_lt hc1]
      · -- i ≥ k + 2 : shifted P gap
        obtain ⟨j, hjval⟩ : ∃ j, i.val = k + 1 + (j + 1) :=
          ⟨i.val - k - 2, by omega⟩
        have hlt2 : k + (j + 1) < P.n := by
          have hi := i.isLt
          simp [P', insertPoint] at hi
          omega
        dsimp [P']
        rw [hjval, insert_pts_ge P k hkn c hc1 hc2 j (Nat.le_of_lt hlt2)]
        have hshiftNext := pointAtNat_insert_shift P k hkn c hc1 hc2 (j + 1) (by omega)
        rw [show pointAtNat (insertPoint P k hkn c hc1 hc2)
              (k + 1 + (j + 1) + 1) = pointAtNat P (k + (j + 1) + 1) by
          simpa only [Nat.add_assoc] using hshiftNext]
        exact gapAtNat (k + (j + 1)) hlt2

include hkn hc1 hc2 in
lemma mesh_insert_le :
    (insertPoint P k hkn c hc1 hc2).mesh ≤ P.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i hi
  exact insert_gap_le_mesh P k hkn c hc1 hc2 i

include hkn hc1 hc2 in
lemma insTags_valid (tags : Fin P.n → ℝ) (htags : tagsInPartition P tags) :
    tagsInPartition (insertPoint P k hkn c hc1 hc2)
      (insTags tags (⟨k, hkn⟩ : Fin P.n) c) := by
  let P' := insertPoint P k hkn c hc1 hc2
  let kFin : Fin P.n := ⟨k, hkn⟩
  intro i
  change insTags tags kFin c i ∈ subinterval P' i
  rw [← subintervalAtNat_eq P' i.isLt]
  rcases lt_trichotomy i.val k with hlt | heq | hgt
  · -- i < k
    have htag : insTags tags kFin c i =
        tags (⟨i.val, lt_trans hlt hkn⟩ : Fin P.n) := by
      simpa [kFin] using insTags_lt tags kFin c hlt
    rw [htag, insert_subinterval_lt P k hkn c hc1 hc2 hlt,
      subintervalAtNat_eq P (lt_trans hlt hkn)]
    exact htags ⟨i.val, lt_trans hlt hkn⟩
  · -- i = k : tag d in [pts k, c]
    have htag : insTags tags kFin c i = c := by
      simp [insTags, kFin, heq]
    rw [heq, htag, insert_subinterval_seamL P k hkn c hc1 hc2]
    exact ⟨le_of_lt hc1, le_rfl⟩
  · rcases Nat.lt_or_ge i.val (k + 1) with h | h
    · omega
    · rcases Nat.eq_or_lt_of_le h with heq1 | hgt1
      · -- i = k + 1 : tag d in [c, pts (k+1)]
        have htag : insTags tags kFin c i = c := by
          simp [insTags, kFin, ← heq1]
        rw [← heq1, htag, insert_subinterval_seamR P k hkn c hc1 hc2]
        exact ⟨le_rfl, le_of_lt hc2⟩
      · -- i ≥ k + 2 : shifted tag in shifted cell
        obtain ⟨j, hjval⟩ : ∃ j, i.val = k + 1 + (j + 1) :=
          ⟨i.val - k - 2, by omega⟩
        have hlt2 : k + (j + 1) < P.n := by
          have hi := i.isLt
          simp [P', insertPoint] at hi
          omega
        have htag : insTags tags kFin c i =
            tags (⟨k + (j + 1), hlt2⟩ : Fin P.n) := by
          rw [insTags_gt tags kFin c (by simpa [kFin, hjval] using hgt1)]
          congr 1
          apply Fin.ext
          simp [hjval]
          omega
        rw [hjval, htag, insert_subinterval_gt P k hkn c hc1 hc2 j hlt2,
          subintervalAtNat_eq P hlt2]
        exact htags ⟨k + (j + 1), hlt2⟩

include hkn hc1 hc2 in
private lemma taggedSum_insert_eq (tags : Fin P.n → ℝ) (f α : ℝ → ℝ) :
    taggedSum P tags f α =
      taggedSum (insertPoint P k hkn c hc1 hc2)
          (insTags tags (⟨k, hkn⟩ : Fin P.n) c) f α
        - (f c * (α c - α (pointAtNat P k)) +
            f c * (α (pointAtNat P (k + 1)) - α c))
        + f (tags ⟨k, hkn⟩) *
            (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) := by
  let P' := insertPoint P k hkn c hc1 hc2
  let kFin : Fin P.n := ⟨k, hkn⟩
  let tags' : Fin P'.n → ℝ := insTags tags kFin c
  have key := sum_insert_diff P.n k hkn
    (taggedTermAtNat P tags f α) (taggedTermAtNat P' tags' f α)
    (f c * (α c - α (pointAtNat P k)))
    (f c * (α (pointAtNat P (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · rw [taggedSum_eq_range P tags, taggedSum_eq_range P' tags']
    simpa [P', insertPoint, taggedTermAtNat, hkn] using key
  case hlt =>
    intro i hi
    have hiP : i < P.n := lt_trans hi hkn
    have hiP' : i < P'.n := by simp [P', insertPoint]; omega
    unfold taggedTermAtNat
    rw [dif_pos hiP', dif_pos hiP]
    dsimp only
    have htag : tags' ⟨i, hiP'⟩ = tags ⟨i, hiP⟩ := by
      dsimp [tags']
      simpa [kFin] using insTags_lt tags kFin c hi
    rw [htag, insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
      insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    have hkP' : k < P'.n := by simp [P', insertPoint]; omega
    unfold taggedTermAtNat
    rw [dif_pos hkP']
    dsimp only
    have htag : tags' ⟨k, hkP'⟩ = c := by
      simp [tags', kFin, insTags]
    rw [htag, insert_pts_lt P k hkn c hc1 hc2 le_rfl,
      insert_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    have hk1P' : k + 1 < P'.n := by simp [P', insertPoint]; omega
    unfold taggedTermAtNat
    rw [dif_pos hk1P']
    dsimp only
    have htag : tags' ⟨k + 1, hk1P'⟩ = c := by
      simp [tags', kFin, insTags]
    have hshift := insert_pts_ge P k hkn c hc1 hc2 0 (Nat.succ_le_of_lt hkn)
    rw [htag, insert_pts_seam P k hkn c hc1 hc2,
      show pointAtNat (insertPoint P k hkn c hc1 hc2) (k + 1 + 1) =
          pointAtNat P (k + 1) by simpa using hshift]
  case hgt =>
    intro j
    by_cases hj : k + (j + 1) < P.n
    · have hjP' : k + 1 + (j + 1) < P'.n := by simp [P', insertPoint]; omega
      unfold taggedTermAtNat
      rw [dif_pos hjP', dif_pos hj]
      dsimp only
      have htag : tags' ⟨k + 1 + (j + 1), hjP'⟩ =
          tags ⟨k + (j + 1), hj⟩ := by
        dsimp [tags']
        rw [insTags_gt tags kFin c (by simp [kFin])]
        congr 1
        apply Fin.ext
        simp
        omega
      have hshiftNext := pointAtNat_insert_shift P k hkn c hc1 hc2 (j + 1) (by omega)
      rw [htag, insert_pts_ge P k hkn c hc1 hc2 j (Nat.le_of_lt hj),
        show pointAtNat (insertPoint P k hkn c hc1 hc2)
              (k + 1 + (j + 1) + 1) = pointAtNat P (k + (j + 1) + 1) by
          simpa only [Nat.add_assoc] using hshiftNext]
    · have hjP' : ¬k + 1 + (j + 1) < P'.n := by simp [P', insertPoint]; omega
      simp [taggedTermAtNat, hj, hjP']

end InsertCells

lemma image_Icc_union {f : ℝ → ℝ} {a d b : ℝ} (had : a ≤ d) (hdb : d ≤ b) :
    f '' Icc a b = f '' Icc a d ∪ f '' Icc d b := by
  rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc had hdb]

lemma sourceHypotheses_glue {a d b : ℝ} {f α : ℝ → ℝ}
    (h₁ : SourceHypotheses a d f α) (h₂ : SourceHypotheses d b f α) :
    SourceHypotheses a b f α := by
  rcases h₁ with ⟨had, hA₁, hB₁, hM₁⟩
  rcases h₂ with ⟨hdb, hA₂, hB₂, hM₂⟩
  have hadb : a ≤ b := le_of_lt (lt_trans had hdb)
  refine ⟨lt_trans had hdb, ?_, ?_, ?_⟩
  · rw [image_Icc_union (le_of_lt had) (le_of_lt hdb)]; exact hA₁.union hA₂
  · rw [image_Icc_union (le_of_lt had) (le_of_lt hdb)]; exact hB₁.union hB₂
  · -- glue monotonicity
    intro x hx y hy hxy
    have hd_ad : d ∈ Icc a d := ⟨le_of_lt had, le_rfl⟩
    have hd_db : d ∈ Icc d b := ⟨le_rfl, le_of_lt hdb⟩
    rcases le_or_gt x d with hxd | hdx
    · rcases le_or_gt y d with hyd | hdy
      · -- both in [a,d]
        exact hM₁ ⟨hx.1, hxd⟩ ⟨hy.1, hyd⟩ hxy
      · -- x ≤ d ≤ y
        have hx_ad : x ∈ Icc a d := ⟨hx.1, hxd⟩
        have hy_db : y ∈ Icc d b := ⟨le_of_lt hdy, hy.2⟩
        exact le_trans (hM₁ hx_ad hd_ad hxd) (hM₂ hd_db hy_db (le_of_lt hdy))
    · -- d < x ≤ y, both in [d,b]
      have hx_db : x ∈ Icc d b := ⟨le_of_lt hdx, hx.2⟩
      have hy_db : y ∈ Icc d b := ⟨le_of_lt (lt_of_lt_of_le hdx hxy), hy.2⟩
      exact hM₂ hx_db hy_db hxy

def Omega (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (f '' Icc a b) - sInf (f '' Icc a b)

lemma omega_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    0 ≤ Omega f a b := by
  have hne : (f '' Icc a b).Nonempty := ⟨f a, a, ⟨le_rfl, le_of_lt hab⟩, rfl⟩
  obtain ⟨y, hy⟩ := hne
  have h1 : sInf (f '' Icc a b) ≤ y := csInf_le hBelow hy
  have h2 : y ≤ sSup (f '' Icc a b) := le_csSup hAbove hy
  unfold Omega; linarith

private lemma cell_osc_le_omega {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {f : ℝ → ℝ}
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    upperStepAtNat P f k - lowerStepAtNat P f k ≤ Omega f a b := by
  let i : Fin P.n := ⟨k, hkn⟩
  rw [upperStepAtNat_eq P f hkn, lowerStepAtNat_eq P f hkn]
  have hcellAbove : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove
  have hcellBelow : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow
  have hsub : f '' subinterval P i ⊆ f '' Icc a b :=
    Set.image_mono (subinterval_subset_Icc_core P)
  have hne : (f '' subinterval P i).Nonempty :=
    ⟨f (P.pts i.castSucc), P.pts i.castSucc,
      ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩, rfl⟩
  have hUp : upperStep P f i ≤ sSup (f '' Icc a b) := by
    unfold upperStep
    exact csSup_le_csSup hAbove hne hsub
  have hLow : sInf (f '' Icc a b) ≤ lowerStep P f i := by
    unfold lowerStep
    exact csInf_le_csInf hBelow hne hsub
  unfold Omega; linarith

private lemma crossing_point_dist_le {a b d : ℝ} (P : Partition a b) {k : ℕ}
    (hkn : k < P.n) (hc1 : pointAtNat P k < d)
    (hc2 : d < pointAtNat P (k + 1)) {x : ℝ}
    (hx : x ∈ subintervalAtNat P k) :
    |x - d| ≤ P.mesh := by
  have hlen : pointAtNat P (k + 1) - pointAtNat P k ≤ P.mesh := by
    rw [pointAtNat_eq P (Nat.succ_le_of_lt hkn),
      pointAtNat_eq P (Nat.le_of_lt hkn)]
    simpa using partition_length_le_mesh P (⟨k, hkn⟩ : Fin P.n)
  rw [subintervalAtNat, dif_pos hkn] at hx
  have : |x - d| ≤ pointAtNat P (k + 1) - pointAtNat P k := by
    rw [abs_le]; constructor
    · nlinarith [hx.1, le_of_lt hc2]
    · nlinarith [hx.2, le_of_lt hc1]
  linarith

private lemma alpha_gap_le_total {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {α : ℝ → ℝ} (hmono : MonotoneOn α (Icc a b)) :
    α (pointAtNat P (k + 1)) - α (pointAtNat P k) ≤ α b - α a := by
  have hkmem : pointAtNat P k ∈ Icc a b := by
    rw [pointAtNat_eq P (Nat.le_of_lt hkn)]
    exact partition_pts_mem_Icc_core P
  have hk1mem : pointAtNat P (k + 1) ∈ Icc a b := by
    rw [pointAtNat_eq P (Nat.succ_le_of_lt hkn)]
    exact partition_pts_mem_Icc_core P
  have hstep : pointAtNat P k < pointAtNat P (k + 1) := by
    rw [pointAtNat_eq P (Nat.le_of_lt hkn),
      pointAtNat_eq P (Nat.succ_le_of_lt hkn)]
    apply P.strict_mono
    simp
  have hamem : a ∈ Icc a b := ⟨le_rfl, le_of_lt (lt_of_le_of_lt hkmem.1 (lt_of_lt_of_le
    hstep hk1mem.2))⟩
  have hbmem : b ∈ Icc a b := ⟨hamem.2, le_rfl⟩
  have h1 : α a ≤ α (pointAtNat P k) := hmono hamem hkmem hkmem.1
  have h2 : α (pointAtNat P (k + 1)) ≤ α b := hmono hk1mem hbmem hk1mem.2
  linarith

private lemma cell_osc_le_of_close {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {f : ℝ → ℝ} {v η : ℝ}
    (hclose : ∀ x ∈ subintervalAtNat P k, |f x - v| ≤ η) :
    upperStepAtNat P f k - lowerStepAtNat P f k ≤ 2 * η := by
  have hne : (f '' subintervalAtNat P k).Nonempty := by
    rw [subintervalAtNat, dif_pos hkn]
    exact ⟨f (pointAtNat P k), pointAtNat P k,
      ⟨le_rfl, le_of_lt (by
        rw [pointAtNat_eq P (Nat.le_of_lt hkn),
          pointAtNat_eq P (Nat.succ_le_of_lt hkn)]
        apply P.strict_mono
        simp)⟩, rfl⟩
  have hAbove : BddAbove (f '' subintervalAtNat P k) := by
    refine ⟨v + η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx
    rw [abs_le] at this; linarith [this.2]
  have hBelow : BddBelow (f '' subintervalAtNat P k) := by
    refine ⟨v - η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx
    rw [abs_le] at this; linarith [this.1]
  have hUp : upperStepAtNat P f k ≤ v + η := by
    unfold upperStepAtNat
    rw [dif_pos hkn]
    refine csSup_le hne ?_
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx; rw [abs_le] at this; linarith [this.2]
  have hLow : v - η ≤ lowerStepAtNat P f k := by
    unfold lowerStepAtNat
    rw [dif_pos hkn]
    refine le_csInf hne ?_
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx; rw [abs_le] at this; linarith [this.1]
  linarith

lemma abs_f_sub_le_omega {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ Omega f a b := by
  have hfx_le : f x ≤ sSup (f '' Icc a b) := le_csSup hAbove ⟨x, hx, rfl⟩
  have hfy_le : f y ≤ sSup (f '' Icc a b) := le_csSup hAbove ⟨y, hy, rfl⟩
  have hle_fx : sInf (f '' Icc a b) ≤ f x := csInf_le hBelow ⟨x, hx, rfl⟩
  have hle_fy : sInf (f '' Icc a b) ≤ f y := csInf_le hBelow ⟨y, hy, rfl⟩
  rw [abs_le]; unfold Omega; constructor <;> linarith

open Classical in

lemma locate_point {a b : ℝ} (P : Partition a b) {d : ℝ}
    (had : a < d) (hdb : d < b) :
    (∃ k, 0 < k ∧ k < P.n ∧ pointAtNat P k = d) ∨
      (∃ k, k < P.n ∧ pointAtNat P k < d ∧ d < pointAtNat P (k + 1)) := by
  set Q : ℕ → Prop := fun i => pointAtNat P i ≤ d with hQ
  set k := Nat.findGreatest Q P.n with hk
  have hzero : pointAtNat P 0 = a := by
    rw [pointAtNat_eq P (Nat.zero_le P.n)]
    simpa using P.pts_start
  have hend : pointAtNat P P.n = b := by
    rw [pointAtNat_eq P le_rfl]
    convert P.pts_end using 1
    congr 1
  have hstart : Q 0 := by
    dsimp [Q]
    rw [hzero]
    exact le_of_lt had
  have hk_le : k ≤ P.n := Nat.findGreatest_le P.n
  have hk_spec : Q k := Nat.findGreatest_spec (Nat.zero_le P.n) hstart
  have hkltn : k < P.n := by
    rcases lt_or_eq_of_le hk_le with h | h
    · exact h
    · exfalso
      rw [h] at hk_spec
      simp only [hQ] at hk_spec
      rw [hend] at hk_spec
      linarith
  have hgt : ¬ Q (k + 1) := by
    apply Nat.findGreatest_is_greatest (by omega : k < k + 1) (by omega : k + 1 ≤ P.n)
  have hd_lt : d < pointAtNat P (k + 1) := by
    simp only [hQ] at hgt; exact lt_of_not_ge hgt
  have hpk_le : pointAtNat P k ≤ d := by simpa [hQ] using hk_spec
  rcases lt_or_eq_of_le hpk_le with hlt | heq
  · -- strictly inside cell k
    exact Or.inr ⟨k, hkltn, hlt, hd_lt⟩
  · -- d is grid point P.pts k, and k > 0 since a < d
    refine Or.inl ⟨k, ?_, hkltn, heq⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso; rw [hk0, hzero] at heq; linarith
    · exact hkpos

theorem upperLowerCommonLimit_glue_alpha {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a d f α L₁) (h₂ : UpperLowerCommonLimit d b f α L₂)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    UpperLowerCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  set Ω := Omega f a b with hΩ
  have hΩnn : 0 ≤ Ω := omega_nonneg hab hAbove hBelow
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  set epsp : ℝ := eps / (4 * (Ω + 1)) with hepsp
  have hΩ1pos : 0 < Ω + 1 := by linarith
  have hepsp_pos : 0 < epsp := by rw [hepsp]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hαd epsp hepsp_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- d is a grid point
    have hpkFin : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = d := by
      rw [← pointAtNat_eq P (le_of_lt hkn)]
      exact hpk
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpkFin with hP₁
    set P₂ := splitRight P k hkn d hpkFin with hP₂
    have hm₁ : P₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpkFin) hmesh₁
    have hm₂ : P₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpkFin) hmesh₂
    have hb₁ := H₁ P₁ hm₁
    have hb₂ := H₂ P₂ hm₂
    constructor
    · rw [upperSum_split P k hk0 hkn d hpkFin f α]
      have heq : upperSum P₁ f α + upperSum P₂ f α - (L₁ + L₂)
          = (upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂)|
            ≤ |upperSum P₁ f α - L₁| + |upperSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.1 hb₂.1
        _ < eps := by linarith
    · rw [lowerSum_split P k hk0 hkn d hpkFin f α]
      have heq : lowerSum P₁ f α + lowerSum P₂ f α - (L₁ + L₂)
          = (lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂)|
            ≤ |lowerSum P₁ f α - L₁| + |lowerSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.2 hb₂.2
        _ < eps := by linarith
  · -- interior cell: insert d
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    -- Δα bound
    have hkmem : pointAtNat P k ∈ Icc a b := cptk_mem P k hkn
    have hk1mem : pointAtNat P (k + 1) ∈ Icc a b := cptk1_mem P k hkn
    have hdmem : d ∈ Icc a b := c_mem P k hkn d hc1 hc2
    have hgapk : pointAtNat P (k + 1) - pointAtNat P k ≤ P.mesh := by
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hkn),
        pointAtNat_eq P (Nat.le_of_lt hkn)]
      simpa using partition_length_le_mesh P (⟨k, hkn⟩ : Fin P.n)
    have hdL_lt : α d - α (pointAtNat P k) < epsp := by
      have hdist : dist (pointAtNat P k) d < δ₃ := by
        rw [Real.dist_eq]
        have : |pointAtNat P k - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc2]; nlinarith [le_of_lt hc1]]
        exact lt_of_le_of_lt this hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh
      have h := (abs_lt.mp hh).1
      linarith
    have hdR_lt : α (pointAtNat P (k + 1)) - α d < epsp := by
      have hdist : dist (pointAtNat P (k + 1)) d < δ₃ := by
        rw [Real.dist_eq]
        have : |pointAtNat P (k + 1) - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc1]; nlinarith [le_of_lt hc2]]
        exact lt_of_le_of_lt this hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh
      have h := (abs_lt.mp hh).2
      linarith
    have hdL_nn : 0 ≤ α d - α (pointAtNat P k) :=
      sub_nonneg.mpr (hmono hkmem hdmem (le_of_lt hc1))
    have hdR_nn : 0 ≤ α (pointAtNat P (k + 1)) - α d :=
      sub_nonneg.mpr (hmono hdmem hk1mem (le_of_lt hc2))
    have hΔ_lt : α (pointAtNat P (k + 1)) - α (pointAtNat P k) < 2 * epsp := by
      linarith
    have hΔ_nn : 0 ≤ α (pointAtNat P (k + 1)) - α (pointAtNat P k) := by
      linarith
    -- oscillation bound M_k - m_k ≤ Ω
    have hosc : upperStepAtNat P f k - lowerStepAtNat P f k ≤ Ω :=
      cell_osc_le_omega P hkn hAbove hBelow
    have hOmega2epsp : Ω * (2 * epsp) < eps / 2 := by
      rw [hepsp]
      rw [show Ω * (2 * (eps / (4 * (Ω + 1)))) = (Ω / (Ω + 1)) * (eps / 2) from by
        field_simp; ring]
      have hratio : Ω / (Ω + 1) < 1 := by rw [div_lt_one hΩ1pos]; linarith
      nlinarith [mul_pos (show (0:ℝ) < eps / 2 by positivity) (show (0:ℝ) < 1 by norm_num)]
    -- change-bound → Ω·2εp
    have hchU : |upperSum P f α - upperSum P' f α| < eps / 2 := by
      have hb := abs_upperSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStepAtNat P f k - lowerStepAtNat P f k) *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
          ≤ Ω * (2 * epsp) := by
        calc
          (upperStepAtNat P f k - lowerStepAtNat P f k) *
                (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
              ≤ Ω * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ Ω * (2 * epsp) := mul_le_mul_of_nonneg_left (le_of_lt hΔ_lt) hΩnn
      exact lt_of_le_of_lt (le_trans hb hchain) hOmega2epsp
    have hchL : |lowerSum P f α - lowerSum P' f α| < eps / 2 := by
      have hb := abs_lowerSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStepAtNat P f k - lowerStepAtNat P f k) *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
          ≤ Ω * (2 * epsp) := by
        calc
          (upperStepAtNat P f k - lowerStepAtNat P f k) *
                (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
              ≤ Ω * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ Ω * (2 * epsp) := mul_le_mul_of_nonneg_left (le_of_lt hΔ_lt) hΩnn
      exact lt_of_le_of_lt (le_trans hb hchain) hOmega2epsp
    -- split P' at k+1 (grid point d)
    have hdgrid : P'.pts ⟨k + 1, by simp [P', insertPoint]; omega⟩ = d := by
      simpa [P'] using insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by have : P'.n = P.n + 1 := rfl; omega
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ hmQ₁
    have hbQ₂ := H₂ Q₂ hmQ₂
    constructor
    · -- upper
      have hP'bound : |upperSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [upperSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : upperSum Q₁ f α + upperSum Q₂ f α - (L₁ + L₂)
            = (upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂)|
              ≤ |upperSum Q₁ f α - L₁| + |upperSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.1 hbQ₂.1
          _ = eps / 2 := by ring
      have heq : upperSum P f α - (L₁ + L₂)
          = (upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂))|
            ≤ |upperSum P f α - upperSum P' f α| + |upperSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchU hP'bound
        _ = eps := by ring
    · -- lower
      have hP'bound : |lowerSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [lowerSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : lowerSum Q₁ f α + lowerSum Q₂ f α - (L₁ + L₂)
            = (lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂)|
              ≤ |lowerSum Q₁ f α - L₁| + |lowerSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.2 hbQ₂.2
          _ = eps / 2 := by ring
      have heq : lowerSum P f α - (L₁ + L₂)
          = (lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂))|
            ≤ |lowerSum P f α - lowerSum P' f α| + |lowerSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchL hP'bound
        _ = eps := by ring

theorem upperLowerCommonLimit_glue_f {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a d f α L₁) (h₂ : UpperLowerCommonLimit d b f α L₂)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    UpperLowerCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  set A : ℝ := α b - α a with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; have := hmono (⟨le_rfl, le_of_lt hab⟩ : a ∈ Icc a b)
      (⟨hab.le, le_rfl⟩ : b ∈ Icc a b) hab.le; linarith
  have hA1pos : 0 < A + 1 := by linarith
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  set eta : ℝ := eps / (4 * (A + 1)) with heta
  have heta_pos : 0 < eta := by rw [heta]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hfd eta heta_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- grid point
    have hpkFin : P.pts ⟨k, Nat.lt_succ_iff.mpr (le_of_lt hkn)⟩ = d := by
      rw [← pointAtNat_eq P (le_of_lt hkn)]
      exact hpk
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpkFin with hP₁
    set P₂ := splitRight P k hkn d hpkFin with hP₂
    have hm₁ : P₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpkFin) hmesh₁
    have hm₂ : P₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpkFin) hmesh₂
    have hb₁ := H₁ P₁ hm₁
    have hb₂ := H₂ P₂ hm₂
    constructor
    · rw [upperSum_split P k hk0 hkn d hpkFin f α]
      have heq : upperSum P₁ f α + upperSum P₂ f α - (L₁ + L₂)
          = (upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂)|
            ≤ |upperSum P₁ f α - L₁| + |upperSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.1 hb₂.1
        _ < eps := by linarith
    · rw [lowerSum_split P k hk0 hkn d hpkFin f α]
      have heq : lowerSum P₁ f α + lowerSum P₂ f α - (L₁ + L₂)
          = (lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂)|
            ≤ |lowerSum P₁ f α - L₁| + |lowerSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.2 hb₂.2
        _ < eps := by linarith
  · -- interior cell
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    have hΔ_nn : 0 ≤ α (pointAtNat P (k + 1)) - α (pointAtNat P k) :=
      sub_nonneg.mpr (hmono (cptk_mem P k hkn) (cptk1_mem P k hkn)
        (le_of_lt (lt_trans hc1 hc2)))
    have hΔ_le : α (pointAtNat P (k + 1)) - α (pointAtNat P k) ≤ A :=
      alpha_gap_le_total P hkn hmono
    -- crossing-cell f-closeness ⇒ M_k - m_k ≤ 2η
    have hclose : ∀ x ∈ subintervalAtNat P k, |f x - f d| ≤ eta := by
      intro x hx
      have hxdist : |x - d| ≤ P.mesh := crossing_point_dist_le P hkn hc1 hc2 hx
      have hdist : dist x d < δ₃ := by
        rw [Real.dist_eq]; exact lt_of_le_of_lt hxdist hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh; exact le_of_lt hh
    have hosc : upperStepAtNat P f k - lowerStepAtNat P f k ≤ 2 * eta :=
      cell_osc_le_of_close P hkn hclose
    have h2etaA : (2 * eta) * A < eps / 2 := by
      rw [heta]
      have hne : (A + 1) ≠ 0 := by positivity
      have hid : 2 * (eps / (4 * (A + 1))) * A = (A / (A + 1)) * (eps / 2) := by
        field_simp
        ring
      rw [hid]
      have hratio : A / (A + 1) < 1 := by rw [div_lt_one hA1pos]; linarith
      have hq : 0 < eps / 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_right hratio hq]
    have hchU : |upperSum P f α - upperSum P' f α| < eps / 2 := by
      have hb := abs_upperSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStepAtNat P f k - lowerStepAtNat P f k) *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
          ≤ (2 * eta) * A := by
        calc
          (upperStepAtNat P f k - lowerStepAtNat P f k) *
                (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
              ≤ (2 * eta) * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ (2 * eta) * A := mul_le_mul_of_nonneg_left hΔ_le (by positivity)
      exact lt_of_le_of_lt (le_trans hb hchain) h2etaA
    have hchL : |lowerSum P f α - lowerSum P' f α| < eps / 2 := by
      have hb := abs_lowerSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStepAtNat P f k - lowerStepAtNat P f k) *
          (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
          ≤ (2 * eta) * A := by
        calc
          (upperStepAtNat P f k - lowerStepAtNat P f k) *
                (α (pointAtNat P (k + 1)) - α (pointAtNat P k))
              ≤ (2 * eta) * (α (pointAtNat P (k + 1)) - α (pointAtNat P k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ (2 * eta) * A := mul_le_mul_of_nonneg_left hΔ_le (by positivity)
      exact lt_of_le_of_lt (le_trans hb hchain) h2etaA
    have hdgrid : P'.pts ⟨k + 1, by simp [P', insertPoint]; omega⟩ = d := by
      simpa [P'] using insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by have : P'.n = P.n + 1 := rfl; omega
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ hmQ₁
    have hbQ₂ := H₂ Q₂ hmQ₂
    constructor
    · have hP'bound : |upperSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [upperSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : upperSum Q₁ f α + upperSum Q₂ f α - (L₁ + L₂)
            = (upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂)|
              ≤ |upperSum Q₁ f α - L₁| + |upperSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.1 hbQ₂.1
          _ = eps / 2 := by ring
      have heq : upperSum P f α - (L₁ + L₂)
          = (upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂))|
            ≤ |upperSum P f α - upperSum P' f α| + |upperSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchU hP'bound
        _ = eps := by ring
    · have hP'bound : |lowerSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [lowerSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : lowerSum Q₁ f α + lowerSum Q₂ f α - (L₁ + L₂)
            = (lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂)|
              ≤ |lowerSum Q₁ f α - L₁| + |lowerSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.2 hbQ₂.2
          _ = eps / 2 := by ring
      have heq : lowerSum P f α - (L₁ + L₂)
          = (lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂))|
            ≤ |lowerSum P f α - lowerSum P' f α| + |lowerSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchL hP'bound
        _ = eps := by ring

noncomputable def rsIntegralWitness_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    RSIntegralWitness f α a b where
  value := rsIntegral f α a d hac + rsIntegral f α d b hcb
  source_limit :=
    upperLowerCommonLimit_glue_alpha (rsIntegral_source_spec hac)
      (rsIntegral_source_spec hcb) hαd had hdb

noncomputable def rsIntegrable_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    RSIntegrable f α a b :=
  (rsIntegralWitness_glue_alpha hac hcb hαd had hdb).toRSIntegrable

theorem rsIntegral_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    rsIntegral f α a b (rsIntegrable_glue_alpha hac hcb hαd had hdb)
      = rsIntegral f α a d hac + rsIntegral f α d b hcb :=
  DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_glue_alpha hac hcb hαd had hdb))
    (taggedCommonLimit_of_upperLowerCommonLimit
      (upperLowerCommonLimit_glue_alpha (rsIntegral_source_spec hac)
        (rsIntegral_source_spec hcb) hαd had hdb))

noncomputable def rsIntegralWitness_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    RSIntegralWitness f α a b where
  value := rsIntegral f α a d hac + rsIntegral f α d b hcb
  source_limit :=
    upperLowerCommonLimit_glue_f (rsIntegral_source_spec hac)
      (rsIntegral_source_spec hcb) hfd had hdb

noncomputable def rsIntegrable_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    RSIntegrable f α a b :=
  (rsIntegralWitness_glue_f hac hcb hfd had hdb).toRSIntegrable

theorem rsIntegral_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    rsIntegral f α a b (rsIntegrable_glue_f hac hcb hfd had hdb)
      = rsIntegral f α a d hac + rsIntegral f α d b hcb :=
  DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_glue_f hac hcb hfd had hdb))
    (taggedCommonLimit_of_upperLowerCommonLimit
      (upperLowerCommonLimit_glue_f (rsIntegral_source_spec hac)
        (rsIntegral_source_spec hcb) hfd had hdb))

theorem rsIntegral_glue {f α : ℝ → ℝ} {a d b : ℝ}
    (had : a < d) (hdb : d < b)
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hcont : ContinuousAt α d ∨ ContinuousAt f d) :
    ∃ hab : RSIntegrable f α a b,
      rsIntegral f α a b hab = rsIntegral f α a d hac + rsIntegral f α d b hcb := by
  rcases hcont with hαd | hfd
  · exact ⟨rsIntegrable_glue_alpha hac hcb hαd had hdb,
      rsIntegral_glue_alpha hac hcb hαd had hdb⟩
  · exact ⟨rsIntegrable_glue_f hac hcb hfd had hdb,
      rsIntegral_glue_f hac hcb hfd had hdb⟩

end Thm12Item4

theorem thm_1_2 {f g α : ℝ → ℝ} {c a b : ℝ} :
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      ∃ hfg : RSIntegrable (fun x => f x + g x) α a b,
        rsIntegral (fun x => f x + g x) α a b hfg =
          rsIntegral f α a b hf + rsIntegral g α a b hg) ∧
    (∀ (hf : RSIntegrable f α a b),
      ∃ hcf : RSIntegrable (fun x => c * f x) α a b,
        rsIntegral (fun x => c * f x) α a b hcf =
          c * rsIntegral f α a b hf) ∧
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      (∀ x ∈ Icc a b, f x ≤ g x) →
        rsIntegral f α a b hf ≤ rsIntegral g α a b hg) ∧
    (∀ (d : ℝ), a < d → d < b →
      ∀ (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b),
        (ContinuousAt α d ∨ ContinuousAt f d) →
        ∃ hab : RSIntegrable f α a b,
          rsIntegral f α a b hab = rsIntegral f α a d hac + rsIntegral f α d b hcb) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf hg
    exact ⟨rsIntegrable_integrand_add hf hg, rsIntegral_integrand_add hf hg⟩
  · intro hf
    exact ⟨rsIntegrable_integrand_const_mul (c := c) hf,
      rsIntegral_integrand_const_mul (c := c) hf⟩
  · intro hf hg hfg
    exact rsIntegral_integrand_mono hf hg hfg
  · intro d had hdb hac hcb hcont
    exact Thm12Item4.rsIntegral_glue had hdb hac hcb hcont
