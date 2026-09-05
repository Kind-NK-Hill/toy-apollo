/-
TASK ID: rs_partition_core
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open scoped Classical
open Finset BigOperators

noncomputable section

namespace RSCore

 
structure TaggedPartition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : ℕ → ℝ
  tags : ℕ → ℝ
  pts_start : pts 0 = a
  pts_end : pts n = b
  pts_sorted : ∀ i, i < n → pts i ≤ pts (i + 1)
  tags_lower : ∀ i, i < n → pts i ≤ tags i
  tags_upper : ∀ i, i < n → tags i ≤ pts (i + 1)

 
lemma TaggedPartition.pts_mono_range {a b : ℝ} (P : TaggedPartition a b)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) : P.pts i ≤ P.pts j := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hij
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        P.pts i ≤ P.pts (i + d) := ih (by omega) (by omega)
        _ ≤ P.pts (i + d + 1) := P.pts_sorted (i + d) (by omega)

 
def TaggedPartition.mesh {a b : ℝ} (P : TaggedPartition a b) : ℝ :=
  Finset.sup' (Finset.range P.n) (⟨0, Finset.mem_range.mpr P.hn⟩)
    fun i => P.pts (i + 1) - P.pts i

 
def RSSum {a b : ℝ} (P : TaggedPartition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, f (P.tags i) * (α (P.pts (i + 1)) - α (P.pts i))

 
def IsRSIntegral (a b : ℝ) (f α : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b, P.mesh < δ → |RSSum P f α - L| < ε

 
def RSIntegrableOnInterval (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, IsRSIntegral a b f α L

 
def RSIntegrableFamily (α : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrableOnInterval f α a b}

 
noncomputable def RSIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if h : RSIntegrableOnInterval f α a b then Classical.choose h else 0

end RSCore
