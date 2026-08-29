/-
TASK ID: thm_8_2
TYPE: Theorem_Statement
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

noncomputable section

namespace Thm82Support

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def measurableRectangles : Set (Set (α × β)) :=
  Set.image2 (· ×ˢ ·)
    {s : Set α | MeasurableSet s}
    {t : Set β | MeasurableSet t}

def rectangleMass (P : Measure α) (Q : Measure β)
    (s : Set α) (t : Set β) : ENNReal :=
  P s * Q t

@[simp]
theorem rectangleMass_empty_left (P : Measure α) (Q : Measure β) (t : Set β) :
    rectangleMass P Q ∅ t = 0 := by
  simp [rectangleMass]

@[simp]
theorem rectangleMass_empty_right (P : Measure α) (Q : Measure β) (s : Set α) :
    rectangleMass P Q s ∅ = 0 := by
  simp [rectangleMass]

def productSetFunction (P : Measure α) (Q : Measure β)
    (A : Set (α × β)) (_hA : MeasurableSet A) : ENNReal :=
  ∫⁻ x, Q (Prod.mk x ⁻¹' A) ∂P

theorem productSetFunction_empty (P : Measure α) (Q : Measure β) :
    productSetFunction P Q ∅ MeasurableSet.empty = 0 := by
  simp [productSetFunction]

theorem productSetFunction_iUnion (P : Measure α) (Q : Measure β) [SFinite Q]
    {A : ℕ → Set (α × β)} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    productSetFunction P Q (⋃ i, A i) (MeasurableSet.iUnion hA) =
      ∑' i, productSetFunction P Q (A i) (hA i) := by
  unfold productSetFunction
  have hpoint (x : α) :
      Q (Prod.mk x ⁻¹' ⋃ i, A i) = ∑' i, Q (Prod.mk x ⁻¹' A i) := by
    rw [preimage_iUnion, measure_iUnion]
    · exact hdisj.mono fun _ _ hij => hij.preimage _
    · exact fun i => measurable_prodMk_left (hA i)
  simp_rw [hpoint]
  exact lintegral_tsum fun i =>
    (measurable_measure_prodMk_left (ν := Q) (hA i)).aemeasurable

def constructedProduct (P : Measure α) (Q : Measure β) [SFinite Q] : Measure (α × β) :=
  Measure.ofMeasurable
    (productSetFunction P Q)
    (productSetFunction_empty P Q)
    (fun _ hA hdisj => productSetFunction_iUnion P Q hA hdisj)

theorem constructedProduct_apply (P : Measure α) (Q : Measure β) [SFinite Q]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    constructedProduct P Q A = productSetFunction P Q A hA := by
  exact Measure.ofMeasurable_apply A hA

theorem productSetFunction_rectangle (P : Measure α) (Q : Measure β)
    (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    productSetFunction P Q (s ×ˢ t) (hs.prod ht) = rectangleMass P Q s t := by
  classical
  simp_rw [productSetFunction, mk_preimage_prod_right_eq_if, measure_if,
    lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ,
    rectangleMass, mul_comm]

theorem constructedProduct_rectangle (P : Measure α) (Q : Measure β) [SFinite Q]
    (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    constructedProduct P Q (s ×ˢ t) = rectangleMass P Q s t := by
  rw [constructedProduct_apply P Q (hs.prod ht)]
  exact productSetFunction_rectangle P Q s t hs ht

theorem constructedProduct_eq_prod (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    constructedProduct P Q = P.prod Q := by
  symm
  exact Measure.prod_eq (μ := P) (ν := Q) (μν := constructedProduct P Q)
    (by
      intro s t hs ht
      exact constructedProduct_rectangle P Q s t hs ht)

end Thm82Support

theorem thm_8_2
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨Thm82Support.constructedProduct P Q, ?_, ?_⟩
  · intro s t hs ht
    exact Thm82Support.constructedProduct_rectangle P Q s t hs ht
  · intro R hR
    have hprodR : P.prod Q = R :=
      Measure.prod_eq (μ := P) (ν := Q) (μν := R)
        (by intro s t hs ht; exact hR s t hs ht)
    exact hprodR.symm.trans (Thm82Support.constructedProduct_eq_prod P Q).symm
