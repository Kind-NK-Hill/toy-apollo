import ToyApollo.Output.def_3_6
import ToyApollo.Output.def_3_7
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Heine-Borel Theorem (Theorem 3.4)

Let `A` be a subset of `ℝ`. Then `A` is compact (closed and bounded) if and
only if every open cover of `A` has a finite subcover.
-/

open Set Metric Bornology

/-- Theorem 3.4 (Heine-Borel), using the canonical compactness and open-cover
interfaces from Definitions 3.6 and 3.7. -/
theorem heine_borel (A : Set ℝ) :
    Def36.IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), IsOpenCover A U →
      ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) := by
  rw [Def36.IsCompactTextbook]
  rw [← Metric.isCompact_iff_isClosed_bounded]
  rw [isCompact_iff_finite_subcover]
  constructor
  · intro h ι U hU
    exact h U hU.1 hU.2
  · intro h ι U hopen hcover
    exact h U ⟨hopen, hcover⟩

/-- Canonical task landing for Theorem 3.4. -/
theorem thm_3_4 (A : Set ℝ) :
    Def36.IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), IsOpenCover A U →
      ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) :=
  heine_borel A
