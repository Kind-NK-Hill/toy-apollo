import Mathlib

open Finset BigOperators
open scoped Classical

noncomputable section

namespace DarbouxRS

/-- A textbook partition `a = x_0 < x_1 < ... < x_n = b`. -/
structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : ℕ → ℝ
  pts_start : pts 0 = a
  pts_end : pts n = b
  strict_mono : ∀ i, i < n → pts i < pts (i + 1)

/-- The mesh `max_i (x_{i+1} - x_i)` of a partition. -/
def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.range P.n) (⟨0, Finset.mem_range.mpr P.hn⟩)
    fun i => P.pts (i + 1) - P.pts i

/-- The closed subinterval `[x_i, x_{i+1}]` determined by a partition. -/
def subinterval {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  Set.Icc (P.pts i) (P.pts (i + 1))

/-- The textbook upper step `M_i = sup { f x : x_i <= x <= x_{i+1} }`. -/
def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  sSup (f '' subinterval P i)

/-- The textbook lower step `m_i = inf { f x : x_i <= x <= x_{i+1} }`. -/
def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  sInf (f '' subinterval P i)

/-- The upper Riemann-Stieltjes sum `U(P,f,alpha)`. -/
def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    upperStep P f i * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- The lower Riemann-Stieltjes sum `L(P,f,alpha)`. -/
def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    lowerStep P f i * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- A tagged Riemann-Stieltjes sum over the same partition shape. -/
def taggedSum {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    f (tags i) * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- Tags chosen in the corresponding partition subintervals. -/
def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ) : Prop :=
  ∀ i, i < P.n → tags i ∈ subinterval P i

/-- The standing textbook hypotheses from the paragraphs preceding Definition 1.2. -/
def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧ BddAbove (f '' Set.Icc a b) ∧ BddBelow (f '' Set.Icc a b) ∧
    MonotoneOn alpha (Set.Icc a b)

/-- The source criterion: upper and lower sums converge to the same limit as mesh goes to zero. -/
def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps

/-- Riemann-Stieltjes integrability on `[a,b]` with respect to `alpha`. -/
def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L

/-- A stated bridge obligation from the upper/lower criterion to tagged sums. -/
def taggedBridgeObligation (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  UpperLowerCommonLimit a b f alpha L ↔
    SourceHypotheses a b f alpha ∧
      ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : ℕ → ℝ,
        tagsInPartition P tags →
          P.mesh < delta →
            |taggedSum P tags f alpha - L| < eps

end DarbouxRS

/-- Textbook partition interface for Definition 1.2. -/
abbrev RSPartition := DarbouxRS.Partition

/-- Mesh of a textbook partition. -/
def rsPartitionMesh {a b : ℝ} (P : RSPartition a b) : ℝ :=
  DarbouxRS.Partition.mesh P

/-- Upper Riemann-Stieltjes sum `U(P,f,alpha)`. -/
def rsUpperSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.upperSum P f alpha

/-- Lower Riemann-Stieltjes sum `L(P,f,alpha)`. -/
def rsLowerSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.lowerSum P f alpha

/-- Common upper/lower-sum limit semantics from Definition 1.2. -/
def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  DarbouxRS.UpperLowerCommonLimit a b f alpha L

/-- `f` is Riemann-Stieltjes integrable on `[a,b]` with respect to `alpha`. -/
def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  DarbouxRS.RSIntegrableOnInterval f alpha a b

/-- The value of the finite-interval Riemann-Stieltjes integral after integrability is known. -/
noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  Classical.choose h

/-- The chosen integral value satisfies the source upper/lower common-limit criterion. -/
theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  Classical.choose_spec h

/-- The family `R(alpha)` of functions integrable with respect to `alpha` on `[a,b]`. -/
def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}

/-- Exported statement of Definition 1.2. -/
def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b
