/-
TASK ID: DirichletGamma
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

noncomputable section

 



def gammaScaleLaw (alpha beta : ℝ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure alpha beta⁻¹

theorem gammaScaleLaw_isProbability {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (gammaScaleLaw alpha beta) := by
  unfold gammaScaleLaw
  exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure halpha (inv_pos.mpr hbeta)

instance gammaScaleLaw_noAtoms (alpha beta : ℝ) :
    NoAtoms (gammaScaleLaw alpha beta) := by
  unfold gammaScaleLaw ProbabilityTheory.gammaMeasure
  infer_instance

 
theorem gammaScaleLaw_positive_ae {alpha beta : ℝ}
    (_halpha : 0 < alpha) (_hbeta : 0 < beta) :
    ∀ᵐ x ∂gammaScaleLaw alpha beta, 0 < x := by
  rw [ae_iff]
  have hIio : gammaScaleLaw alpha beta (Set.Iio 0) = 0 := by
    unfold gammaScaleLaw ProbabilityTheory.gammaMeasure
    rw [MeasureTheory.withDensity_apply _ measurableSet_Iio]
    exact setLIntegral_eq_zero measurableSet_Iio
      (fun x hx => ProbabilityTheory.gammaPDF_of_neg (a := alpha) (r := beta⁻¹) hx)
  have hzero : gammaScaleLaw alpha beta ({0} : Set ℝ) = 0 := by
    simp
  have hcompl : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by
    ext x
    simp
  rw [hcompl]
  have hIic : gammaScaleLaw alpha beta (Set.Iic 0) = 0 := by
    have hsplit : Set.Iic (0 : ℝ) = Set.Iio 0 ∪ ({0} : Set ℝ) := by
      ext x
      constructor
      · intro hx
        rcases lt_or_eq_of_le (show x ≤ 0 from hx) with hxlt | hxeq
        · exact Or.inl hxlt
        · exact Or.inr (by simp [hxeq])
      · intro hx
        rcases hx with hxlt | hxeq
        · exact le_of_lt (show x < 0 from hxlt)
        · exact le_of_eq hxeq
    rw [hsplit]
    exact measure_union_null hIio hzero
  exact hIic

 
structure IndependentGammaFamily (Ω : Type*) [MeasurableSpace Ω] (mu : Measure Ω) (n : ℕ) where
  X : Ω → Fin n → ℝ
  shape : Fin n → ℝ
  scale : ℝ
  shape_pos : ∀ i, 0 < shape i
  scale_pos : 0 < scale
  measurable : ∀ i, Measurable fun omega => X omega i
  independent : ProbabilityTheory.iIndepFun (fun i : Fin n => fun omega : Ω => X omega i) mu
  gamma_law : ∀ i, Measure.map (fun omega => X omega i) mu = gammaScaleLaw (shape i) scale

 
def gammaVectorTotal {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

 
def sourceNormalizedVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / gammaVectorTotal x

theorem measurable_sourceNormalizedVector {n : ℕ} :
    Measurable (sourceNormalizedVector : (Fin n → ℝ) → Fin n → ℝ) := by
  unfold sourceNormalizedVector gammaVectorTotal
  fun_prop

theorem sourceNormalizedVector_sum
    {n : ℕ} (x : Fin n → ℝ) (hV : gammaVectorTotal x ≠ 0) :
    (∑ i, sourceNormalizedVector x i) = 1 := by
  calc
    (∑ i, sourceNormalizedVector x i) =
        (∑ i, x i) / gammaVectorTotal x := by
      simp [sourceNormalizedVector, gammaVectorTotal, Finset.sum_div]
    _ = 1 := by
      have hsum : (∑ i, x i) ≠ 0 := by
        simpa [gammaVectorTotal] using hV
      simp [gammaVectorTotal, div_self hsum]

 
def gammaTotal {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {n : ℕ}
    (G : IndependentGammaFamily Ω mu n) (omega : Ω) : ℝ :=
  gammaVectorTotal (fun i => G.X omega i)

 
def normalizedGammaVector {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {n : ℕ}
    (G : IndependentGammaFamily Ω mu n) (omega : Ω) : Fin n → ℝ :=
  sourceNormalizedVector (fun i => G.X omega i)

 
theorem normalizedGammaVector_sum {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {n : ℕ}
    (G : IndependentGammaFamily Ω mu n) (omega : Ω) (hV : gammaTotal G omega ≠ 0) :
    (∑ i, normalizedGammaVector G omega i) = 1 := by
  calc
    (∑ i, normalizedGammaVector G omega i) =
        (∑ i, G.X omega i) / gammaTotal G omega := by
      simp [normalizedGammaVector, sourceNormalizedVector, gammaTotal, gammaVectorTotal,
        Finset.sum_div]
    _ = 1 := by
      have hsum : (∑ i, G.X omega i) ≠ 0 := by
        simpa [gammaTotal, gammaVectorTotal] using hV
      simp [gammaTotal, gammaVectorTotal, div_self hsum]

 
theorem normalizedGammaVector_nonneg {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {n : ℕ}
    (G : IndependentGammaFamily Ω mu n) (omega : Ω)
    (hx : ∀ i, 0 ≤ G.X omega i) (hV : 0 < gammaTotal G omega) :
    ∀ i, 0 ≤ normalizedGammaVector G omega i := by
  intro i
  exact div_nonneg (hx i) hV.le

 

 
def gammaProductLaw {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun i => gammaScaleLaw (alpha i) beta

theorem gammaProductLaw_isProbability {n : ℕ} (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    IsProbabilityMeasure (gammaProductLaw alpha beta) := by
  unfold gammaProductLaw
  letI : ∀ i, IsProbabilityMeasure (gammaScaleLaw (alpha i) beta) :=
    fun i => gammaScaleLaw_isProbability (halpha i) hbeta
  infer_instance

theorem gammaProductLaw_coordinates_positive_ae {n : ℕ}
    (alpha : Fin n → ℝ) {beta : ℝ} (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ∀ᵐ x ∂gammaProductLaw alpha beta, ∀ i, 0 < x i := by
  unfold gammaProductLaw
  letI : ∀ i, IsProbabilityMeasure (gammaScaleLaw (alpha i) beta) :=
    fun i => gammaScaleLaw_isProbability (halpha i) hbeta
  exact Filter.eventually_all.2 fun i =>
    (MeasureTheory.measurePreserving_eval
      (fun i => gammaScaleLaw (alpha i) beta) i).quasiMeasurePreserving.tendsto_ae.eventually
      (gammaScaleLaw_positive_ae (halpha i) hbeta)

theorem gammaProductLaw_total_positive_ae {n : ℕ} (hn : 0 < n)
    (alpha : Fin n → ℝ) {beta : ℝ} (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ∀ᵐ x ∂gammaProductLaw alpha beta, 0 < gammaVectorTotal x := by
  filter_upwards [gammaProductLaw_coordinates_positive_ae alpha halpha hbeta] with x hx
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, by simp⟩
  simpa [gammaVectorTotal] using
    (Finset.sum_pos
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => x i) (fun i _ => hx i) hne)

 
def DirichletFullSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1}

theorem measurableSet_DirichletFullSimplex (n : ℕ) :
    MeasurableSet (DirichletFullSimplex n) := by
  have hnonneg : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : Fin n =>
        isClosed_le continuous_const (continuous_apply i))
  have hsum : IsClosed {y : Fin n → ℝ | (∑ i, y i) = (1 : ℝ)} := by
    exact isClosed_eq
      (continuous_finset_sum Finset.univ fun i _ => continuous_apply i)
      continuous_const
  exact (hnonneg.inter hsum).measurableSet

theorem DirichletFullSimplex_volume_zero_succ (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ)) (DirichletFullSimplex (n + 1)) = 0 := by
  refine measure_mono_null ?_
    (Measure.addHaar_affineSubspace volume (fintypeAffineCoords (Fin (n + 1)) ℝ) ?_)
  · intro y hy
    exact (mem_fintypeAffineCoords_iff_sum).2 hy.2
  · intro htop
    have hzero_mem :
        (0 : Fin (n + 1) → ℝ) ∈ (⊤ : AffineSubspace ℝ (Fin (n + 1) → ℝ)) := by
      simp
    have hzero_mem' :
        (0 : Fin (n + 1) → ℝ) ∈ fintypeAffineCoords (Fin (n + 1)) ℝ := by
      simp [htop] at hzero_mem ⊢
    have hsum : (∑ i : Fin (n + 1), (0 : Fin (n + 1) → ℝ) i) = (1 : ℝ) :=
      (mem_fintypeAffineCoords_iff_sum).1 hzero_mem'
    simp at hsum



def DirichletLaw {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.map (fun x : Fin n → ℝ => sourceNormalizedVector x)
    (gammaProductLaw alpha beta)

theorem DirichletLaw_isProbability {n : ℕ}
    (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    IsProbabilityMeasure (DirichletLaw alpha beta) := by
  unfold DirichletLaw
  letI : IsProbabilityMeasure (gammaProductLaw alpha beta) :=
    gammaProductLaw_isProbability alpha halpha hbeta
  exact Measure.isProbabilityMeasure_map measurable_sourceNormalizedVector.aemeasurable

theorem sourceNormalizedVector_mem_fullSimplex {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < gammaVectorTotal x) :
    sourceNormalizedVector x ∈ DirichletFullSimplex n := by
  refine ⟨?_, ?_⟩
  · intro i
    exact div_nonneg (hx i) hV.le
  · calc
      (∑ i, sourceNormalizedVector x i) = (∑ i, x i) / gammaVectorTotal x := by
        simp [sourceNormalizedVector, gammaVectorTotal, Finset.sum_div]
      _ = 1 := by
        have hsum : (∑ i, x i) ≠ 0 := by
          simpa [gammaVectorTotal] using ne_of_gt hV
        simp [gammaVectorTotal, div_self hsum]

theorem DirichletLaw_supported_on_simplex {n : ℕ} (hn : 0 < n)
    (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ∀ᵐ y ∂DirichletLaw alpha beta, y ∈ DirichletFullSimplex n := by
  rw [DirichletLaw]
  change
    ∀ᵐ y ∂Measure.map
      (fun x : Fin n → ℝ => sourceNormalizedVector x)
      (gammaProductLaw alpha beta),
      (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1
  rw [MeasureTheory.ae_map_iff measurable_sourceNormalizedVector.aemeasurable
    (measurableSet_DirichletFullSimplex n)]
  filter_upwards [gammaProductLaw_coordinates_positive_ae alpha halpha hbeta,
    gammaProductLaw_total_positive_ae hn alpha halpha hbeta] with x hx hV
  exact sourceNormalizedVector_mem_fullSimplex x (fun i => (hx i).le) hV

theorem DirichletLaw_simplex_probability_one {n : ℕ} (hn : 0 < n)
    (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    DirichletLaw alpha beta (DirichletFullSimplex n) = 1 := by
  letI : IsProbabilityMeasure (DirichletLaw alpha beta) :=
    DirichletLaw_isProbability alpha halpha hbeta
  exact (MeasureTheory.mem_ae_iff_prob_eq_one
    (μ := DirichletLaw alpha beta) (measurableSet_DirichletFullSimplex n)).1
    (DirichletLaw_supported_on_simplex hn alpha halpha hbeta)



theorem independent_gamma_joint_hasLaw
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (alpha : Fin n → ℝ) (beta : ℝ)
    (X : Fin n → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (gammaScaleLaw (alpha i) beta) mu)
    (hIndep : ProbabilityTheory.iIndepFun X mu) :
    HasLaw (fun omega i => X i omega) (gammaProductLaw alpha beta) mu := by
  refine ⟨aemeasurable_pi_lambda _ fun i => (hXlaw i).aemeasurable, ?_⟩
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (hXlaw i).aemeasurable)).1 hIndep]
  have hmap :
      (fun i => Measure.map (X i) mu) =
        fun i => gammaScaleLaw (alpha i) beta := by
    funext i
    exact (hXlaw i).map_eq
  simp [gammaProductLaw, hmap]

theorem normalization_map_hasLaw_dirichlet
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    HasLaw
      (fun x : Fin n → ℝ => sourceNormalizedVector x)
      (DirichletLaw alpha beta)
      (gammaProductLaw alpha beta) := by
  refine ⟨measurable_sourceNormalizedVector.aemeasurable, rfl⟩



theorem independent_gamma_normalized_hasLaw_dirichlet
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (alpha : Fin n → ℝ) (beta : ℝ)
    (X : Fin n → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (gammaScaleLaw (alpha i) beta) mu)
    (hIndep : ProbabilityTheory.iIndepFun X mu) :
    HasLaw
      (fun omega => sourceNormalizedVector (fun i => X i omega))
      (DirichletLaw alpha beta)
      mu := by
  have hjoint := independent_gamma_joint_hasLaw mu alpha beta X hXlaw hIndep
  simpa [Function.comp_def] using
    (normalization_map_hasLaw_dirichlet alpha beta).comp hjoint

 
def projectFirst {n : ℕ} (y : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  fun i => y ⟨i.val, by omega⟩

theorem measurable_projectFirst {n : ℕ} :
    Measurable (projectFirst : (Fin n → ℝ) → Fin (n - 1) → ℝ) := by
  exact measurable_pi_lambda _ fun i =>
    measurable_pi_apply (⟨i.val, by omega⟩ : Fin n)

 
def ProjectedDirichletLaw {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    Measure (Fin (n - 1) → ℝ) :=
  Measure.map (projectFirst : (Fin n → ℝ) → Fin (n - 1) → ℝ)
    (DirichletLaw alpha beta)

theorem ProjectedDirichletLaw_isProbability {n : ℕ}
    (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    IsProbabilityMeasure (ProjectedDirichletLaw alpha beta) := by
  unfold ProjectedDirichletLaw
  letI : IsProbabilityMeasure (DirichletLaw alpha beta) :=
    DirichletLaw_isProbability alpha halpha hbeta
  exact Measure.isProbabilityMeasure_map measurable_projectFirst.aemeasurable

def projectedNormalizedGammaVector {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {n : ℕ}
    (G : IndependentGammaFamily Ω mu n) (omega : Ω) : Fin (n - 1) → ℝ :=
  projectFirst (normalizedGammaVector G omega)

theorem projected_normalized_hasLaw_projectedDirichlet
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (alpha : Fin n → ℝ) (beta : ℝ)
    (X : Fin n → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (gammaScaleLaw (alpha i) beta) mu)
    (hIndep : ProbabilityTheory.iIndepFun X mu) :
    HasLaw
      (fun omega => projectFirst (sourceNormalizedVector (fun j => X j omega)))
      (ProjectedDirichletLaw alpha beta)
      mu := by
  have hnorm := independent_gamma_normalized_hasLaw_dirichlet mu alpha beta X hXlaw hIndep
  have hproj :
      HasLaw
        (projectFirst : (Fin n → ℝ) → Fin (n - 1) → ℝ)
        (ProjectedDirichletLaw alpha beta)
        (DirichletLaw alpha beta) := by
    refine ⟨measurable_projectFirst.aemeasurable, rfl⟩
  simpa [Function.comp_def] using hproj.comp hnorm

 



def projectedSourceNormalizedVector {n : ℕ} (x : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  projectFirst (sourceNormalizedVector x)

theorem measurable_projectedSourceNormalizedVector {n : ℕ} :
    Measurable (projectedSourceNormalizedVector : (Fin n → ℝ) → Fin (n - 1) → ℝ) := by
  exact measurable_projectFirst.comp measurable_sourceNormalizedVector

theorem ProjectedDirichletLaw_eq_map_projectedSourceNormalizedVector
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    ProjectedDirichletLaw alpha beta =
      Measure.map (projectedSourceNormalizedVector : (Fin n → ℝ) → Fin (n - 1) → ℝ)
        (gammaProductLaw alpha beta) := by
  unfold ProjectedDirichletLaw DirichletLaw projectedSourceNormalizedVector
  rw [Measure.map_map]
  · rfl
  · exact measurable_projectFirst
  · exact measurable_sourceNormalizedVector
