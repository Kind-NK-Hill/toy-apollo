import ToyApollo.Output.def_1_2

open Finset BigOperators

noncomputable section

/- This probe fixes the canonical Definition 1.2 interface.  In particular,
the public integrability predicate is the textbook upper/lower common-limit
criterion; tagged convergence is a theorem derived from that criterion. -/

example {a b : ℝ} (P : DarbouxRS.Partition a b) : Fin (P.n + 1) → ℝ :=
  P.pts

example {a b : ℝ} (P : DarbouxRS.Partition a b) (i : Fin P.n) : Set ℝ :=
  DarbouxRS.subinterval P i

example {a b : ℝ} (P : DarbouxRS.Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.taggedSum P tags f alpha

example {a b : ℝ} (P : DarbouxRS.Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    DarbouxRS.upperStep P f i *
      (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

example (f alpha : ℝ → ℝ) (a b : ℝ) :
    RSIntegrable f alpha a b ↔
      ∃ L, DarbouxRS.UpperLowerCommonLimit a b f alpha L :=
  Iff.rfl

example {f alpha : ℝ → ℝ} {a b L : ℝ}
    (h : DarbouxRS.UpperLowerCommonLimit a b f alpha L) :
    DarbouxRS.TaggedCommonLimit a b f alpha L :=
  DarbouxRS.taggedBridgeObligation h
