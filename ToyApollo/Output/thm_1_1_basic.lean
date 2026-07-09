/-
TASK ID: thm_1_1_basic
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2

open Finset BigOperators
open MeasureTheory Set Topology

def discontinuitySetOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ ¬ ContinuousAt f x}

namespace Thm11SourceRoute

lemma continuousAt_of_not_mem_discontinuitySetOn {f : ℝ → ℝ} {a b x : ℝ}
    (hxI : x ∈ Icc a b) (hx : x ∉ discontinuitySetOn f a b) :
    ContinuousAt f x := by
  by_contra hcont
  exact hx ⟨hxI, hcont⟩

lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨_L, hSource⟩
  exact hSource.1.1

lemma not_rsIntegrable_refl (f α : ℝ → ℝ) (a : ℝ) :
    ¬ RSIntegrable f α a a := by
  intro h
  exact (lt_irrefl a) (strict_interval_of_rsIntegrable h)

lemma discontinuitySetOn_const_refl_empty (c a : ℝ) :
    discontinuitySetOn (fun _ : ℝ => c) a a = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx.2 (by
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => c) x))
  · intro hx
    cases hx

theorem current_le_interval_claim_creates_degenerate_witness
    (hclaim :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        a ≤ b →
        Monotone α →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (discontinuitySetOn f a b).Finite →
        (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
        RSIntegrable f α a b) :
    RSIntegrable (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0 0 := by
  refine hclaim (f := fun _ : ℝ => 0) (α := fun _ : ℝ => 0)
    (a := 0) (b := 0) le_rfl ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · rw [discontinuitySetOn_const_refl_empty]
    exact Set.finite_empty
  · intro x hx
    simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)

theorem no_source_route_for_current_le_interval_claim :
    ¬ (∀ {f α : ℝ → ℝ} {a b : ℝ},
      a ≤ b →
      Monotone α →
      BddAbove (f '' Icc a b) →
      BddBelow (f '' Icc a b) →
      (discontinuitySetOn f a b).Finite →
      (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
      RSIntegrable f α a b) := by
  intro hclaim
  exact not_rsIntegrable_refl (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0
    (current_le_interval_claim_creates_degenerate_witness hclaim)

lemma sourceHypotheses_of_strict_task_hypotheses {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    DarbouxRS.SourceHypotheses a b f α := by
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x _hx y _hy hxy
  exact hα_mono hxy

lemma discontinuitySetOn_empty_of_forall_continuousAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousAt f x) :
    discontinuitySetOn f a b = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (hf x hx.1))
  · intro hx
    cases hx

lemma finite_discontinuitySetOn_of_forall_continuousAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousAt f x) :
    (discontinuitySetOn f a b).Finite := by
  rw [discontinuitySetOn_empty_of_forall_continuousAt hf]
  exact Set.finite_empty

theorem common_limits_iff_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ} :
    (∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L) ↔
      RSIntegrable f α a b := by
  constructor
  · rintro ⟨L, hSource, hTagged⟩
    exact ⟨L, hSource⟩
  · intro h
    rcases h with ⟨L, hSource⟩
    exact ⟨L, hSource, taggedCommonLimit_of_upperLowerCommonLimit hSource⟩

lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (P : DarbouxRS.Partition a b) (tags : ℕ → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) :
    DarbouxRS.lowerSum P f α ≤ DarbouxRS.taggedSum P tags f α ∧
      DarbouxRS.taggedSum P tags f α ≤ DarbouxRS.upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold DarbouxRS.lowerSum DarbouxRS.taggedSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellBelow : BddBelow (f '' DarbouxRS.subinterval P i) :=
      BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
    have hlow_le_tag : DarbouxRS.lowerStep P f i ≤ f (tags i) := by
      unfold DarbouxRS.lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold DarbouxRS.taggedSum DarbouxRS.upperSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellAbove : BddAbove (f '' DarbouxRS.subinterval P i) :=
      BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
    have htag_le_up : f (tags i) ≤ DarbouxRS.upperStep P f i := by
      unfold DarbouxRS.upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := Hδ P hmesh
  have hbetween := taggedSum_between_lower_upper hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

def StrictFiniteDiscontinuityUpperLowerCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ∃ L, rsUpperLowerCommonLimit a b f α L

end Thm11SourceRoute
