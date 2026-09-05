/-
TASK ID: ex_1_2_2
TYPE: Example_Proof
SOURCE PLAN: 37_chap1_mixed_singular
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_01.DirichletGamma




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

 

 
def ex122GammaTotal {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

 
def ex122DirichletSimplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1}



theorem ex122DirichletSimplex_volume_zero (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ)) (ex122DirichletSimplex n) = 0 := by
  simpa [ex122DirichletSimplex, DirichletFullSimplex] using
    DirichletFullSimplex_volume_zero_succ n

 
def ex122NormalizedVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / ex122GammaTotal x

theorem ex122_normalized_sum {n : ℕ} (x : Fin n → ℝ) (hV : ex122GammaTotal x ≠ 0) :
    (∑ i, ex122NormalizedVector x i) = 1 := by
  simpa [ex122GammaTotal, ex122NormalizedVector, sourceNormalizedVector, gammaVectorTotal] using
    sourceNormalizedVector_sum x hV

theorem ex122_normalized_nonneg {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ∀ i, 0 ≤ ex122NormalizedVector x i := by
  intro i
  exact div_nonneg (hx i) hV.le

theorem ex122_normalized_mem_simplex {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ex122NormalizedVector x ∈ ex122DirichletSimplex n := by
  simpa [ex122DirichletSimplex, ex122GammaTotal, ex122NormalizedVector,
    DirichletFullSimplex, gammaVectorTotal, sourceNormalizedVector] using
    sourceNormalizedVector_mem_fullSimplex x hx hV

theorem measurable_ex122GammaTotal {n : ℕ} :
    Measurable (ex122GammaTotal : (Fin n → ℝ) → ℝ) := by
  unfold ex122GammaTotal
  fun_prop

theorem measurable_ex122NormalizedVector {n : ℕ} :
    Measurable (ex122NormalizedVector : (Fin n → ℝ) → Fin n → ℝ) := by
  unfold ex122NormalizedVector ex122GammaTotal
  fun_prop

theorem measurableSet_ex122DirichletSimplex (n : ℕ) :
    MeasurableSet (ex122DirichletSimplex n) := by
  simpa [ex122DirichletSimplex, DirichletFullSimplex] using
    measurableSet_DirichletFullSimplex (n + 1)

 



def ex122GammaScaleLaw (α β : ℝ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure α β⁻¹

theorem ex122GammaScaleLaw_eq_withDensity_gammaPDFReal (α β : ℝ) :
    ex122GammaScaleLaw α β =
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (ProbabilityTheory.gammaPDFReal α β⁻¹ x)) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  rfl

theorem ex122GammaScaleLaw_isProbability {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaScaleLaw α β) := by
  simpa [ex122GammaScaleLaw, gammaScaleLaw] using gammaScaleLaw_isProbability hα hβ

instance ex122GammaScaleLaw_noAtoms (α β : ℝ) :
    NoAtoms (ex122GammaScaleLaw α β) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure
  infer_instance

instance ex122GammaScaleLaw_sigmaFinite (α β : ℝ) :
    SigmaFinite (ex122GammaScaleLaw α β) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  infer_instance

theorem ex122GammaScaleLaw_positive_ae {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaScaleLaw α β, 0 < x := by
  simpa [ex122GammaScaleLaw, gammaScaleLaw] using gammaScaleLaw_positive_ae hα hβ

 
def ex122GammaProductLaw {n : ℕ} (α : Fin n → ℝ) (β : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun i => ex122GammaScaleLaw (α i) β

theorem ex122GammaProductLaw_isProbability {n : ℕ} (α : Fin n → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaProductLaw α β) := by
  simpa [ex122GammaProductLaw, ex122GammaScaleLaw, gammaProductLaw, gammaScaleLaw] using
    gammaProductLaw_isProbability α hα hβ

theorem ex122GammaProductLaw_coordinates_positive_ae {n : ℕ}
    (α : Fin n → ℝ) {β : ℝ} (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaProductLaw α β, ∀ i, 0 < x i := by
  simpa [ex122GammaProductLaw, ex122GammaScaleLaw, gammaProductLaw, gammaScaleLaw] using
    gammaProductLaw_coordinates_positive_ae α hα hβ

theorem ex122GammaProductLaw_total_positive_ae {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ} (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaProductLaw α β, 0 < ex122GammaTotal x := by
  simpa [ex122GammaProductLaw, ex122GammaScaleLaw, ex122GammaTotal,
    gammaProductLaw, gammaScaleLaw, gammaVectorTotal] using
    gammaProductLaw_total_positive_ae (n := n + 1) (Nat.succ_pos n) α hα hβ



def ex122DirichletLaw {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    Measure (Fin (n + 1) → ℝ) :=
  Measure.map (fun x : Fin (n + 1) → ℝ => ex122NormalizedVector x)
    (ex122GammaProductLaw α β)

theorem ex122DirichletLaw_isProbability {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122DirichletLaw α β) := by
  change IsProbabilityMeasure (DirichletLaw α β)
  exact DirichletLaw_isProbability α hα hβ

theorem ex122DirichletLaw_supported_on_simplex {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ y ∂ex122DirichletLaw α β, y ∈ ex122DirichletSimplex n := by
  change ∀ᵐ y ∂DirichletLaw α β, y ∈ DirichletFullSimplex (n + 1)
  exact DirichletLaw_supported_on_simplex (n := n + 1) (Nat.succ_pos n) α hα hβ

theorem ex122DirichletLaw_simplex_probability_one {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122DirichletLaw α β (ex122DirichletSimplex n) = 1 := by
  change DirichletLaw α β (DirichletFullSimplex (n + 1)) = 1
  exact DirichletLaw_simplex_probability_one (n := n + 1) (Nat.succ_pos n) α hα hβ



theorem ex122_independent_gamma_joint_hasLaw
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) (β : ℝ)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw (fun ω i => X i ω) (ex122GammaProductLaw α β) P := by
  simpa [ex122GammaScaleLaw, ex122GammaProductLaw, gammaScaleLaw, gammaProductLaw] using
    independent_gamma_joint_hasLaw P α β X hXlaw hIndep

theorem ex122_normalization_map_hasLaw_dirichlet
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    HasLaw
      (fun x : Fin (n + 1) → ℝ => ex122NormalizedVector x)
      (ex122DirichletLaw α β)
      (ex122GammaProductLaw α β) := by
  change HasLaw
    (fun x : Fin (n + 1) → ℝ => sourceNormalizedVector x)
    (DirichletLaw α β)
    (gammaProductLaw α β)
  exact normalization_map_hasLaw_dirichlet α β



theorem ex122_independent_gamma_normalized_hasLaw_dirichlet
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) (β : ℝ)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw
      (fun ω => ex122NormalizedVector (fun i => X i ω))
      (ex122DirichletLaw α β)
      P := by
  change HasLaw
    (fun ω => sourceNormalizedVector (fun i => X i ω))
    (DirichletLaw α β)
    P
  exact independent_gamma_normalized_hasLaw_dirichlet P α β X hXlaw hIndep

theorem ex122_independent_gamma_normalized_simplex_ae
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ∀ᵐ ω ∂P,
      ex122NormalizedVector (fun i => X i ω) ∈ ex122DirichletSimplex n := by
  have hlaw := ex122_independent_gamma_normalized_hasLaw_dirichlet P α β X hXlaw hIndep
  exact (hlaw.ae_iff (measurableSet_setOf.1 (measurableSet_ex122DirichletSimplex n))).2
    (ex122DirichletLaw_supported_on_simplex α hα hβ)
