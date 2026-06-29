/-
TASK ID: thm_1_1_common_limit
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_1_1_finite_discontinuity

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

namespace Thm11SourceRoute

def ClosedIntervalDarbouxFineCauchyFromGap : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    DarbouxRS.SourceHypotheses a b f α →
    ClosedIntervalDarbouxGapSmall a b f α →
    ClosedIntervalDarbouxFineCauchy a b f α

theorem closedIntervalDarbouxFineCauchyFromGap_of_commonRefinementSandwich
    (hrefine :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        DarbouxRS.SourceHypotheses a b f α →
        DarbouxCommonRefinementSandwich a b f α) :
    ClosedIntervalDarbouxFineCauchyFromGap := by
  intro f α a b hs hgap
  exact closedIntervalDarbouxFineCauchy_of_commonRefinementSandwich hs hgap (hrefine hs)

theorem closedIntervalDarbouxFineCauchyFromGap_proof :
    ClosedIntervalDarbouxFineCauchyFromGap := by
  intro f α a b hs hgap
  exact closedIntervalDarbouxFineCauchy_of_commonRefinementSandwich hs hgap
    (DarbouxCommonRefinementSandwich_proof hs)

theorem closedIntervalDarbouxCommonLimit_of_fineCauchy
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (hfine : ClosedIntervalDarbouxFineCauchy a b f α) :
    ∃ L, rsUpperLowerCommonLimit a b f α L := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  let hs' : DarbouxRS.SourceHypotheses a b f α := ⟨hab, hAbove, hBelow, hmono⟩
  have hsmall : ∀ n : ℕ, ∃ P : DarbouxRS.Partition a b,
      P.mesh < (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    have hδ : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact DarbouxRS.exists_partition_mesh_lt hab hδ
  let Pseq : ℕ → DarbouxRS.Partition a b := fun n => Classical.choose (hsmall n)
  have hPseq : ∀ n : ℕ, (Pseq n).mesh < (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    exact Classical.choose_spec (hsmall n)
  let U : ℕ → ℝ := fun n => DarbouxRS.upperSum (Pseq n) f α
  have hmesh_lt_of_ge :
      ∀ {N n : ℕ} {δ : ℝ}, N ≤ n →
        (1 : ℝ) / ((N : ℝ) + 1) < δ →
        (Pseq n).mesh < δ := by
    intro N n δ hNn hNδ
    have hden_le : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      nlinarith
    have hden_pos : 0 < (N : ℝ) + 1 := by positivity
    have hrecip :
        (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hden_pos hden_le
    exact lt_trans (lt_of_lt_of_le (hPseq n) hrecip) hNδ
  have hU_cauchy : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro eps heps
    rcases hfine eps heps with ⟨δ, hδ, Hδ⟩
    rcases exists_nat_one_div_lt hδ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm_mesh : (Pseq m).mesh < δ := hmesh_lt_of_ge hm hN
    have hn_mesh : (Pseq n).mesh < δ := hmesh_lt_of_ge hn hN
    have hclose := Hδ (Pseq m) (Pseq n) hm_mesh hn_mesh
    simpa [U, Real.dist_eq] using hclose.1
  rcases cauchySeq_tendsto_of_complete hU_cauchy with ⟨L, hULim⟩
  refine ⟨L, ?_⟩
  refine ⟨hs', ?_⟩
  intro eps heps
  have hthird : 0 < eps / 3 := by linarith
  rcases hfine (eps / 3) hthird with ⟨δ, hδ, Hδ⟩
  have hUevent := (Metric.tendsto_nhds.mp hULim) (eps / 3) hthird
  rcases Filter.eventually_atTop.1 hUevent with ⟨Ntend, hNtend⟩
  rcases exists_nat_one_div_lt hδ with ⟨Nmesh, hNmesh⟩
  let N := max Ntend Nmesh
  have hNtend_le : Ntend ≤ N := le_max_left _ _
  have hNmesh_le : Nmesh ≤ N := le_max_right _ _
  have hN_mesh : (Pseq N).mesh < δ := hmesh_lt_of_ge hNmesh_le hNmesh
  have hN_lim : |DarbouxRS.upperSum (Pseq N) f α - L| < eps / 3 := by
    have hdist := hNtend N hNtend_le
    simpa [U, Real.dist_eq] using hdist
  refine ⟨δ, hδ, ?_⟩
  intro P hPmesh
  have hclose := Hδ P (Pseq N) hPmesh hN_mesh
  constructor
  · have htri :
        |DarbouxRS.upperSum P f α - L| ≤
          |DarbouxRS.upperSum P f α - DarbouxRS.upperSum (Pseq N) f α| +
            |DarbouxRS.upperSum (Pseq N) f α - L| := by
      have hdecomp :
          DarbouxRS.upperSum P f α - L =
            (DarbouxRS.upperSum P f α - DarbouxRS.upperSum (Pseq N) f α) +
              (DarbouxRS.upperSum (Pseq N) f α - L) := by
        ring
      rw [hdecomp]
      exact abs_add_le _ _
    have hsum :
        |DarbouxRS.upperSum P f α - DarbouxRS.upperSum (Pseq N) f α| +
            |DarbouxRS.upperSum (Pseq N) f α - L| < eps / 3 + eps / 3 :=
      add_lt_add hclose.1 hN_lim
    exact lt_of_le_of_lt htri (lt_trans hsum (by linarith))
  · have htri :
        |DarbouxRS.lowerSum P f α - L| ≤
          |DarbouxRS.lowerSum P f α - DarbouxRS.upperSum (Pseq N) f α| +
            |DarbouxRS.upperSum (Pseq N) f α - L| := by
      have hdecomp :
          DarbouxRS.lowerSum P f α - L =
            (DarbouxRS.lowerSum P f α - DarbouxRS.upperSum (Pseq N) f α) +
              (DarbouxRS.upperSum (Pseq N) f α - L) := by
        ring
      rw [hdecomp]
      exact abs_add_le _ _
    have hsum :
        |DarbouxRS.lowerSum P f α - DarbouxRS.upperSum (Pseq N) f α| +
            |DarbouxRS.upperSum (Pseq N) f α - L| < eps / 3 + eps / 3 :=
      add_lt_add hclose.2.2.2 hN_lim
    exact lt_of_le_of_lt htri (lt_trans hsum (by linarith))

def ClosedIntervalDarbouxCommonLimitFromOscillation : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    DarbouxRS.SourceHypotheses a b f α →
    ClosedIntervalDarbouxOscillationSmall a b f α →
    ∃ L, rsUpperLowerCommonLimit a b f α L

def ClosedIntervalDarbouxCommonLimitFromGap : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    DarbouxRS.SourceHypotheses a b f α →
    ClosedIntervalDarbouxGapSmall a b f α →
    ∃ L, rsUpperLowerCommonLimit a b f α L

theorem closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy
    (hfine : ClosedIntervalDarbouxFineCauchyFromGap) :
    ClosedIntervalDarbouxCommonLimitFromGap := by
  intro f α a b hs hgap
  exact closedIntervalDarbouxCommonLimit_of_fineCauchy hs (hfine hs hgap)

theorem closedIntervalDarbouxCommonLimitFromOscillation_of_gap
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromGap) :
    ClosedIntervalDarbouxCommonLimitFromOscillation := by
  intro f α a b hs hosc
  exact hdarboux hs (closedIntervalDarbouxGapSmall_of_oscillationSmall hosc)

theorem strict_upperLower_criterion_of_oscillation
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromOscillation)
    (hosc : StrictFiniteDiscontinuityOscillationCriterion) :
    StrictFiniteDiscontinuityUpperLowerCriterion := by
  intro f α a b hab hα_mono hAbove hBelow hDiscFinite hαCont
  have hs : DarbouxRS.SourceHypotheses a b f α :=
    sourceHypotheses_of_strict_task_hypotheses hab hα_mono hAbove hBelow
  exact hdarboux hs (hosc hab hα_mono hAbove hBelow hDiscFinite hαCont)

theorem strict_upperLower_criterion_of_gap
    (hdarboux : ClosedIntervalDarbouxCommonLimitFromGap)
    (hosc : StrictFiniteDiscontinuityOscillationCriterion) :
    StrictFiniteDiscontinuityUpperLowerCriterion :=
  strict_upperLower_criterion_of_oscillation
    (closedIntervalDarbouxCommonLimitFromOscillation_of_gap hdarboux) hosc

theorem strictFiniteDiscontinuityUpperLowerCriterion_proof :
    StrictFiniteDiscontinuityUpperLowerCriterion :=
  strict_upperLower_criterion_of_gap
    (closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy
      closedIntervalDarbouxFineCauchyFromGap_proof)
    strictFiniteDiscontinuityOscillationCriterion_proof

def StrictFiniteDiscontinuityCommonLimitCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L

theorem strict_common_limit_criterion_of_upperLower_criterion
    (hULcriterion : StrictFiniteDiscontinuityUpperLowerCriterion) :
    StrictFiniteDiscontinuityCommonLimitCriterion := by
  intro f α a b hab hα_mono hAbove hBelow hDiscFinite hαCont
  rcases hULcriterion hab hα_mono hAbove hBelow hDiscFinite hαCont with ⟨L, hUL⟩
  exact ⟨L, hUL, taggedCommonLimit_of_upperLowerCommonLimit hUL⟩

theorem strictFiniteDiscontinuityCommonLimitCriterion_proof :
    StrictFiniteDiscontinuityCommonLimitCriterion :=
  strict_common_limit_criterion_of_upperLower_criterion
    strictFiniteDiscontinuityUpperLowerCriterion_proof

theorem strict_thm_1_1_of_common_limit_criterion
    (hcriterion : StrictFiniteDiscontinuityCommonLimitCriterion)
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b := by
  rw [← common_limits_iff_rsIntegrable]
  exact hcriterion hab hα_mono hAbove hBelow hDiscFinite hαCont

theorem strict_thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b :=
  strict_thm_1_1_of_common_limit_criterion
    strictFiniteDiscontinuityCommonLimitCriterion_proof
    hab hα_mono hAbove hBelow hDiscFinite hαCont

end Thm11SourceRoute
