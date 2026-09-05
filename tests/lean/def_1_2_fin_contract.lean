import ProbabilityTheory.chapter_01.def_1_2

open Finset BigOperators

noncomputable section

/- This probe fixes the canonical Definition 1.2 interface.  In particular,
the public integrability predicate is the textbook upper/lower common-limit
criterion; tagged convergence is a theorem derived from that criterion. -/

example {a b : ℝ} (P : Partition a b) : Fin (P.n + 1) → ℝ :=
  P.pts

example {a b : ℝ} (P : Partition a b) (i : Fin P.n) : Set ℝ :=
  Partition.subinterval P i

example {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  taggedSum P tags f alpha

example {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    upperStep P f i *
      (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

example (f alpha : ℝ → ℝ) (a b : ℝ) :
    RSIntegrable f alpha a b ↔
      Nonempty (RSIntegralWitness f alpha a b) :=
  Iff.rfl

example {f alpha : ℝ → ℝ} {a b : ℝ} (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  rsIntegral_source_spec h

example {f alpha : ℝ → ℝ} {a b : ℝ} (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  rsIntegral_spec h
