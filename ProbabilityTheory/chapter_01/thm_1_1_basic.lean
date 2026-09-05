/-
TASK ID: thm_1_1_basic
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_01.def_1_2
import ProbabilityTheory.chapter_01.thm_1_2

open Finset BigOperators
open Set Topology

noncomputable section

 
def discontinuitySetOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}

namespace Thm11SourceRoute

 
lemma continuousWithinAt_of_not_mem_discontinuitySetOn {f : ℝ → ℝ} {a b x : ℝ}
    (hxI : x ∈ Icc a b) (hx : x ∉ discontinuitySetOn f a b) :
    ContinuousWithinAt f (Icc a b) x := by
  by_contra hcont
  exact hx ⟨hxI, hcont⟩



lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1



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
      simpa using
        (continuousAt_const.continuousWithinAt :
          ContinuousWithinAt (fun _ : ℝ => c) (Icc a a) x))
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
    SourceHypotheses a b f α := by
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x _hx y _hy hxy
  exact hα_mono hxy



lemma discontinuitySetOn_empty_of_forall_continuousWithinAt
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousWithinAt f (Icc a b) x) :
    discontinuitySetOn f a b = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (hf x hx.1))
  · intro hx
    cases hx



lemma finite_discontinuitySetOn_of_forall_continuousWithinAt
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousWithinAt f (Icc a b) x) :
    (discontinuitySetOn f a b).Finite := by
  rw [discontinuitySetOn_empty_of_forall_continuousWithinAt hf]
  exact Set.finite_empty



theorem common_limits_iff_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ} :
    (∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L) ↔
      RSIntegrable f α a b := by
  constructor
  · rintro ⟨L, hSource, hTagged⟩
    exact ⟨{
      value := L
      source_limit := hSource
      tagged_limit := hTagged
    }⟩
  · intro h
    rcases h with ⟨w⟩
    exact ⟨w.value, w.source_limit, w.tagged_limit⟩

private lemma upperSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b) :
    upperSum P f β = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]

private lemma lowerSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b) :
    lowerSum P f β = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]

private lemma taggedSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b)
    (tags : Fin P.n → ℝ) :
    taggedSum P tags f β = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]

private lemma sourceHypotheses_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hs : SourceHypotheses a b f β) :
    SourceHypotheses a b f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hβmono⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  rw [← hEq hx, ← hEq hy]
  exact hβmono hx hy hxy

private lemma upperLowerCommonLimit_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b L : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hβ : rsUpperLowerCommonLimit a b f β L) :
    rsUpperLowerCommonLimit a b f α L := by
  rcases hβ with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_of_integrator_eqOn_Icc hEq hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := Hdelta P hmesh
  rw [← upperSum_eq_of_integrator_eqOn_Icc hEq P,
    ← lowerSum_eq_of_integrator_eqOn_Icc hEq P]
  exact hP

private lemma taggedCommonLimit_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b L : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hβ : rsTaggedCommonLimit a b f β L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hβ with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_of_integrator_eqOn_Icc hEq hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := Hdelta P tags htags hmesh
  rw [← taggedSum_eq_of_integrator_eqOn_Icc hEq P tags]
  exact hP



theorem _root_.RSIntegrable.congr_integrator_on_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) :
    RSIntegrable f β a b → RSIntegrable f α a b := by
  rintro ⟨w⟩
  refine ⟨{
    value := w.value
    source_limit := upperLowerCommonLimit_of_integrator_eqOn_Icc hEq w.source_limit
    tagged_limit := taggedCommonLimit_of_integrator_eqOn_Icc hEq w.tagged_limit
  }⟩



lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α :=
  ⟨lowerSum_le_taggedSum hs P tags htags,
    taggedSum_le_upperSum hs P tags htags⟩



theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L :=
  rsTaggedCommonLimit_of_rsUpperLowerCommonLimit hUL



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
