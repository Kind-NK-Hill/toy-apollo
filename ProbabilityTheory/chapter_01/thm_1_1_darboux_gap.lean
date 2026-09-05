/-
TASK ID: thm_1_1_darboux_gap
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_01.thm_1_1_bad_cells

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute




def ClosedIntervalDarbouxOscillationSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ → partitionOscillation P f α < eps



def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ →
      upperSum P f α - lowerSum P f α < eps



def ClosedIntervalDarbouxFineCauchy
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P Q : Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      |upperSum P f α - upperSum Q f α| < eps ∧
      |lowerSum P f α - lowerSum Q f α| < eps ∧
      |upperSum P f α - lowerSum Q f α| < eps ∧
      |lowerSum P f α - upperSum Q f α| < eps



lemma upperSum_sub_lowerSum_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) :
    0 ≤ upperSum P f α - lowerSum P f α := by
  have hle : lowerSum P f α ≤ upperSum P f α :=
    DarbouxRS.lowerSum_le_upperSum_core P hs
  exact sub_nonneg.mpr hle



theorem closedIntervalDarbouxAbsGapSmall_of_gapSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α) :
    ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
      P.mesh < δ →
        |upperSum P f α - lowerSum P f α| < eps := by
  intro eps heps
  rcases hgap eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  rw [abs_of_nonneg (upperSum_sub_lowerSum_nonneg_of_source hs P)]
  exact Hδ P hmesh



theorem closedIntervalDarbouxGapSmall_of_oscillationSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hosc : ClosedIntervalDarbouxOscillationSmall a b f α) :
    ClosedIntervalDarbouxGapSmall a b f α := by
  intro eps heps
  rcases hosc eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  rw [upperSum_sub_lowerSum_eq_partitionOscillation]
  exact Hδ P hmesh


end Thm11SourceRoute
