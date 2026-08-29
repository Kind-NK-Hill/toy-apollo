import Mathlib

open scoped Classical
open Finset BigOperators

noncomputable section

namespace RSCore

/-- A tagged partition of `[a, b]` with `n ≥ 1` subintervals. -/
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

/-- Monotonicity of partition points on the range `[0, n]`. -/
lemma TaggedPartition.pts_mono_range {a b : ℝ} (P : TaggedPartition a b)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) : P.pts i ≤ P.pts j := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hij
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        P.pts i ≤ P.pts (i + d) := ih (by omega) (by omega)
        _ ≤ P.pts (i + d + 1) := P.pts_sorted (i + d) (by omega)

/-- The mesh of a tagged partition. -/
def TaggedPartition.mesh {a b : ℝ} (P : TaggedPartition a b) : ℝ :=
  Finset.sup' (Finset.range P.n) (⟨0, Finset.mem_range.mpr P.hn⟩)
    fun i => P.pts (i + 1) - P.pts i

/-- The Riemann--Stieltjes sum attached to a tagged partition. -/
def RSSum {a b : ℝ} (P : TaggedPartition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, f (P.tags i) * (α (P.pts (i + 1)) - α (P.pts i))

/-- `L` is the Riemann--Stieltjes integral of `f` with respect to `α` on `[a,b]`. -/
def IsRSIntegral (a b : ℝ) (f α : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b, P.mesh < δ → |RSSum P f α - L| < ε

/-- Finite-interval RS integrability. -/
def RSIntegrableOnInterval (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, IsRSIntegral a b f α L

/-- The family `R(α)` on a fixed interval `[a,b]`. -/
def RSIntegrableFamily (α : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrableOnInterval f α a b}

/-- Chosen value of the finite-interval Riemann--Stieltjes integral. -/
noncomputable def RSIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if h : RSIntegrableOnInterval f α a b then Classical.choose h else 0

end RSCore
