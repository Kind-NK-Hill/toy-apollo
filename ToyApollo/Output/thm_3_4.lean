/-
TASK ID: thm_3_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_6
import ToyApollo.Output.def_3_7
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Bornology

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

theorem thm_3_4 (A : Set ℝ) :
    Def36.IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), IsOpenCover A U →
      ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) :=
  heine_borel A
