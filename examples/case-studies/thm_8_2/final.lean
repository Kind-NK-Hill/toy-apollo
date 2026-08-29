import Mathlib

/-!
Sanitized proof-route snapshot for case study `thm_8_2`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory Set

noncomputable section

namespace ReviewedThm82

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def rectangleMass (P : Measure α) (Q : Measure β)
    (s : Set α) (t : Set β) : ENNReal :=
  P s * Q t

/-- Independently defined fibre set function. -/
def productSetFunction (P : Measure α) (Q : Measure β)
    (A : Set (α × β)) (_hA : MeasurableSet A) : ENNReal :=
  ∫⁻ x, Q (Prod.mk x ⁻¹' A) ∂P

theorem productSetFunctionEmpty (P : Measure α) (Q : Measure β) :
    productSetFunction P Q ∅ MeasurableSet.empty = 0 := by
  simp [productSetFunction]

/-- Countable additivity is proved before constructing the measure. -/
theorem productSetFunctionIUnion (P : Measure α) (Q : Measure β) [SFinite Q]
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

/-- The product is built from the checked set function. -/
def constructedProduct (P : Measure α) (Q : Measure β) [SFinite Q] :
    Measure (α × β) :=
  Measure.ofMeasurable
    (productSetFunction P Q)
    (productSetFunctionEmpty P Q)
    (fun _ hA hdisj => productSetFunctionIUnion P Q hA hdisj)

theorem constructedProductApply (P : Measure α) (Q : Measure β) [SFinite Q]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    constructedProduct P Q A = productSetFunction P Q A hA :=
  Measure.ofMeasurable_apply A hA

theorem productSetFunctionRectangle (P : Measure α) (Q : Measure β)
    (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    productSetFunction P Q (s ×ˢ t) (hs.prod ht) = rectangleMass P Q s t := by
  classical
  simp_rw [productSetFunction, mk_preimage_prod_right_eq_if, measure_if,
    lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ,
    rectangleMass, mul_comm]

theorem constructedProductRectangle (P : Measure α) (Q : Measure β) [SFinite Q]
    (s : Set α) (t : Set β) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    constructedProduct P Q (s ×ˢ t) = rectangleMass P Q s t := by
  rw [constructedProductApply P Q (hs.prod ht)]
  exact productSetFunctionRectangle P Q s t hs ht

/-- Only after construction do we identify the result with Mathlib's product. -/
theorem constructedProductEqProd (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    constructedProduct P Q = P.prod Q := by
  symm
  exact Measure.prod_eq (μ := P) (ν := Q) (μν := constructedProduct P Q)
    (by
      intro s t hs ht
      exact constructedProductRectangle P Q s t hs ht)

end ReviewedThm82

theorem reviewedThm82
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨ReviewedThm82.constructedProduct P Q, ?_, ?_⟩
  · intro s t hs ht
    exact ReviewedThm82.constructedProductRectangle P Q s t hs ht
  · intro R hR
    have hprodR : P.prod Q = R :=
      Measure.prod_eq (μ := P) (ν := Q) (μν := R)
        (by intro s t hs ht; exact hR s t hs ht)
    exact hprodR.symm.trans (ReviewedThm82.constructedProductEqProd P Q).symm
