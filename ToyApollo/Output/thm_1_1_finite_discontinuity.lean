/-
TASK ID: thm_1_1_finite_discontinuity
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_1_1_darboux_refinement

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

namespace Thm11SourceRoute

def StrictFiniteDiscontinuityOscillationCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ClosedIntervalDarbouxOscillationSmall a b f α

theorem strictFiniteDiscontinuityOscillationCriterion_proof :
    StrictFiniteDiscontinuityOscillationCriterion := by
  intro f α a b hab hα_mono hAbove hBelow hDiscFinite hαCont eps heps
  let A : ℝ := α b - α a
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (hα_mono (le_of_lt hab))
  let eta : ℝ := eps / (2 * (A + 1))
  have hA1_pos : 0 < A + 1 := by linarith
  have hden_eta_pos : 0 < 2 * (A + 1) := by positivity
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact div_pos heps hden_eta_pos
  have heta_A1 : eta * (A + 1) = eps / 2 := by
    dsimp [eta]
    field_simp [ne_of_gt hden_eta_pos, ne_of_gt hA1_pos]
  have hgood_term_lt : eta * A < eps / 2 := by
    have hA_lt : A < A + 1 := by linarith
    have hmul_lt : eta * A < eta * (A + 1) :=
      mul_lt_mul_of_pos_left hA_lt heta_pos
    linarith
  rcases exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
      hAbove hBelow with
    ⟨C, hC_pos, hC_bound⟩
  let badQuota : ℝ := eps / (4 * C)
  have hbadQuota_pos : 0 < badQuota := by
    dsimp [badQuota]
    exact div_pos heps (by positivity)
  rcases finite_discontinuity_alpha_local_increment_pairwise_data
      hα_mono hDiscFinite hαCont hbadQuota_pos with
    ⟨S, hS, rho, hrho_pos, hbad_sum_lt, hsep⟩
  let rhoHalf : ℝ → ℝ := fun c : ℝ => rho c / 2
  have hrhoHalf_pos : ∀ c : ℝ, c ∈ S → 0 < rhoHalf c := by
    intro c hc
    dsimp [rhoHalf]
    linarith [hrho_pos c hc]
  rcases exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
      (f := f) (a := a) (b := b) (eta := eta)
      (S := S) (rho := rhoHalf)
      hS hrhoHalf_pos hAbove hBelow heta_pos with
    ⟨δgood, hδgood_pos, hgood_step⟩
  rcases exists_pos_mesh_bound_le_good_and_half_radii
      S rho hδgood_pos hrho_pos with
    ⟨δ, hδ_pos, hδ_good, hδ_half⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hs : DarbouxRS.SourceHypotheses a b f α :=
    sourceHypotheses_of_strict_task_hypotheses hab hα_mono hAbove hBelow
  have hmesh_good : P.mesh < δgood := lt_of_lt_of_le hmesh hδ_good
  have hmesh_bad : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2 := by
    intro c hc
    exact lt_of_lt_of_le hmesh (hδ_half c hc)
  have hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b := by
    intro c hc
    exact ((hS c).1 hc).1
  have hsplit :=
    partitionOscillation_le_goodRemainder_badCell_split
      (f := f) (α := α) (a := a) (b := b)
      (C := C) (eta := eta) (δgood := δgood)
      (S := S) (rho := rhoHalf)
      hs P hC_bound (le_of_lt heta_pos) hgood_step hmesh_good
  have hbad_inc_le := by
    exact partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
      hα_mono P S rho hcI hrho_pos hmesh_bad hsep
  have htwoC_pos : 0 < 2 * C := by positivity
  have htwoC_nonneg : 0 ≤ 2 * C := le_of_lt htwoC_pos
  have hbad_term_le :=
    mul_le_mul_of_nonneg_left hbad_inc_le htwoC_nonneg
  have hbadQuota_eq : (2 * C) * badQuota = eps / 2 := by
    dsimp [badQuota]
    field_simp [ne_of_gt hC_pos]
    ring
  have hbad_term_lt :
      2 * C *
          (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps / 2 := by
    have hmul_lt :=
      mul_lt_mul_of_pos_left hbad_sum_lt htwoC_pos
    linarith
  dsimp [A] at hgood_term_lt
  linarith

end Thm11SourceRoute
