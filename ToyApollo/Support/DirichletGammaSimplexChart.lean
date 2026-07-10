import ToyApollo.Support.DirichletGammaProductDensity

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

noncomputable section

/-- The normalizing constant in the Dirichlet density formula. -/
def dirichletNormalizer {n : ℕ} (alpha : Fin n → ℝ) : ℝ :=
  Real.Gamma (∑ i, alpha i) / ∏ i, Real.Gamma (alpha i)

/-- The last simplex coordinate determined by the first `n - 1` coordinates. -/
def simplexLastCoord {n : ℕ} (x : Fin (n - 1) → ℝ) : ℝ :=
  1 - ∑ i : Fin (n - 1), x i

theorem fin_sum_projected_last
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) :
    (∑ i : Fin n, alpha i) =
      (∑ i : Fin (n - 1), alpha ⟨i.val, by omega⟩) +
        alpha ⟨n - 1, by omega⟩ := by
  cases n with
  | zero => cases hn
  | succ m =>
      rw [Fin.sum_univ_castSucc]
      congr 1

theorem fin_prod_projected_last
    {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (∏ i : Fin n, f i) =
      (∏ i : Fin (n - 1), f ⟨i.val, by omega⟩) *
        f ⟨n - 1, by omega⟩ := by
  cases n with
  | zero => cases hn
  | succ m =>
      rw [Fin.prod_univ_castSucc]
      congr 1

/-- Inverse chart candidate for the projected normalization map: from projected
coordinates and total mass to the original `n` Gamma coordinates. -/
def projectedSimplexTotalCoord {n : ℕ}
    (x : Fin (n - 1) → ℝ) (s : ℝ) : Fin n → ℝ :=
  fun i =>
    if hi : i.val < n - 1 then
      x ⟨i.val, hi⟩ * s
    else
      simplexLastCoord x * s

/-- Product-space version of `projectedSimplexTotalCoord`, suitable for a
same-dimensional change-of-variables theorem. -/
def projectedSimplexTotalMap {n : ℕ} :
    ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ :=
  fun p => projectedSimplexTotalCoord p.1 p.2

theorem measurable_projectedSimplexTotalMap {n : ℕ} :
    Measurable (projectedSimplexTotalMap :
      ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, hi]
    fun_prop
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, hi, simplexLastCoord]
    fun_prop

theorem projectedSimplexTotalCoord_projectFirst
    {n : ℕ} (x : Fin (n - 1) → ℝ) (s : ℝ) :
    projectFirst (projectedSimplexTotalCoord x s) = fun i => x i * s := by
  funext i
  simp [projectFirst, projectedSimplexTotalCoord]

theorem projectedSimplexTotalCoord_last
    {n : ℕ} (hn : 0 < n) (x : Fin (n - 1) → ℝ) (s : ℝ) :
    projectedSimplexTotalCoord x s ⟨n - 1, by omega⟩ =
      simplexLastCoord x * s := by
  simp [projectedSimplexTotalCoord]

theorem gammaVectorTotal_projectedSimplexTotalCoord
    {n : ℕ} (hn : 0 < n) (x : Fin (n - 1) → ℝ) (s : ℝ) :
    gammaVectorTotal (projectedSimplexTotalCoord x s) = s := by
  rw [gammaVectorTotal, fin_sum_projected_last hn]
  have hfirst :
      (∑ i : Fin (n - 1),
        projectedSimplexTotalCoord x s ⟨i.val, by omega⟩) =
        ∑ i : Fin (n - 1), x i * s := by
    simp [projectedSimplexTotalCoord]
  rw [hfirst, projectedSimplexTotalCoord_last hn]
  simp [simplexLastCoord]
  rw [← Finset.sum_mul]
  ring

theorem projectedSourceNormalizedVector_projectedSimplexTotalCoord
    {n : ℕ} (hn : 0 < n) (x : Fin (n - 1) → ℝ) {s : ℝ} (hs : s ≠ 0) :
    projectedSourceNormalizedVector (projectedSimplexTotalCoord x s) = x := by
  funext i
  rw [projectedSourceNormalizedVector, projectFirst, sourceNormalizedVector]
  rw [gammaVectorTotal_projectedSimplexTotalCoord hn]
  simp [projectedSimplexTotalCoord]
  exact mul_div_cancel_right₀ (x i) hs

theorem simplexLastCoord_projectedSourceNormalizedVector
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hV : gammaVectorTotal x ≠ 0) :
    simplexLastCoord (projectedSourceNormalizedVector x) =
      x ⟨n - 1, by omega⟩ / gammaVectorTotal x := by
  have hsum := sourceNormalizedVector_sum x hV
  have hsplit := fin_sum_projected_last hn (sourceNormalizedVector x)
  have hlast :
      simplexLastCoord (projectedSourceNormalizedVector x) =
        sourceNormalizedVector x ⟨n - 1, by omega⟩ := by
    simp [simplexLastCoord, projectedSourceNormalizedVector, projectFirst]
    rw [hsplit] at hsum
    linarith
  rw [hlast]
  rfl

theorem projectedSimplexTotalCoord_projectedSourceNormalizedVector
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hV : gammaVectorTotal x ≠ 0) :
    projectedSimplexTotalCoord (projectedSourceNormalizedVector x) (gammaVectorTotal x) = x := by
  funext i
  by_cases hi : i.val < n - 1
  · have hidx : (⟨(⟨i.val, hi⟩ : Fin (n - 1)).val, by omega⟩ : Fin n) = i := by
      exact Fin.ext rfl
    simp [projectedSimplexTotalCoord, hi, projectedSourceNormalizedVector, projectFirst,
      sourceNormalizedVector, hidx, div_mul_cancel₀ _ hV]
  · have hle : i.val ≤ n - 1 := Nat.le_pred_of_lt i.isLt
    have hge : n - 1 ≤ i.val := Nat.le_of_not_gt hi
    have hidx : i = (⟨n - 1, by omega⟩ : Fin n) := by
      exact Fin.ext (le_antisymm hle hge)
    rw [hidx]
    simp [projectedSimplexTotalCoord, simplexLastCoord_projectedSourceNormalizedVector hn x hV,
      div_mul_cancel₀ _ hV]

/-- The standard simplex side conditions for the projected Dirichlet coordinates. -/
def DirichletSimplex {n : ℕ} (x : Fin (n - 1) → ℝ) : Prop :=
  (∀ i : Fin (n - 1), 0 ≤ x i) ∧ 0 ≤ simplexLastCoord x

theorem continuous_simplexLastCoord {n : ℕ} :
    Continuous (simplexLastCoord : (Fin (n - 1) → ℝ) → ℝ) := by
  unfold simplexLastCoord
  fun_prop

theorem measurableSet_DirichletSimplex {n : ℕ} :
    MeasurableSet {x : Fin (n - 1) → ℝ | DirichletSimplex x} := by
  have hnonneg : IsClosed {x : Fin (n - 1) → ℝ | ∀ i, 0 ≤ x i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : Fin (n - 1) =>
        isClosed_le continuous_const (continuous_apply i))
  have hlast : IsClosed {x : Fin (n - 1) → ℝ | 0 ≤ simplexLastCoord x} := by
    exact isClosed_le continuous_const continuous_simplexLastCoord
  exact (hnonneg.inter hlast).measurableSet

/-- Domain for the projected simplex plus total-mass chart. -/
def projectedSimplexTotalDomain {n : ℕ} :
    Set ((Fin (n - 1) → ℝ) × ℝ) :=
  {p | DirichletSimplex p.1 ∧ 0 < p.2}

theorem measurableSet_projectedSimplexTotalDomain {n : ℕ} :
    MeasurableSet (projectedSimplexTotalDomain :
      Set ((Fin (n - 1) → ℝ) × ℝ)) := by
  have hsimplex :
      MeasurableSet {p : (Fin (n - 1) → ℝ) × ℝ | DirichletSimplex p.1} :=
    measurableSet_DirichletSimplex.preimage measurable_fst
  have htotal : MeasurableSet {p : (Fin (n - 1) → ℝ) × ℝ | 0 < p.2} :=
    measurableSet_Ioi.preimage measurable_snd
  exact hsimplex.inter htotal

/-- The chart domain over a requested projected-coordinate set. -/
def projectedSimplexChartPreimage {n : ℕ}
    (s : Set (Fin (n - 1) → ℝ)) :
    Set ((Fin (n - 1) → ℝ) × ℝ) :=
  {p | p.1 ∈ s ∧ DirichletSimplex p.1 ∧ 0 < p.2}

theorem measurableSet_projectedSimplexChartPreimage
    {n : ℕ} {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (projectedSimplexChartPreimage (n := n) s) := by
  have hs_pre :
      MeasurableSet
        {p : (Fin (n - 1) → ℝ) × ℝ | p.1 ∈ s} :=
    hs.preimage measurable_fst
  have hsimplex :
      MeasurableSet
        {p : (Fin (n - 1) → ℝ) × ℝ | DirichletSimplex p.1} :=
    measurableSet_DirichletSimplex.preimage measurable_fst
  have htotal :
      MeasurableSet
        {p : (Fin (n - 1) → ℝ) × ℝ | 0 < p.2} :=
    measurableSet_Ioi.preimage measurable_snd
  change
    MeasurableSet
      {p : (Fin (n - 1) → ℝ) × ℝ |
        p.1 ∈ s ∧ DirichletSimplex p.1 ∧ 0 < p.2}
  exact hs_pre.inter (hsimplex.inter htotal)

theorem projectedSimplexChartPreimage_eq_prod
    {n : ℕ} (s : Set (Fin (n - 1) → ℝ)) :
    projectedSimplexChartPreimage (n := n) s =
      (s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x}) ×ˢ Set.Ioi (0 : ℝ) := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
  · intro hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem projectedSimplexChartPreimage_lintegral_eq_iterated
    {n : ℕ} {s : Set (Fin (n - 1) → ℝ)}
    (g : ((Fin (n - 1) → ℝ) × ℝ) → ℝ≥0∞)
    (hg : AEMeasurable g
      ((volume : Measure ((Fin (n - 1) → ℝ) × ℝ)).restrict
        (projectedSimplexChartPreimage (n := n) s))) :
    ∫⁻ p in projectedSimplexChartPreimage (n := n) s, g p =
      ∫⁻ x in s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x},
        ∫⁻ t in Set.Ioi (0 : ℝ), g (x, t) := by
  rw [projectedSimplexChartPreimage_eq_prod]
  rw [Measure.volume_eq_prod]
  apply MeasureTheory.setLIntegral_prod g
  rw [projectedSimplexChartPreimage_eq_prod, Measure.volume_eq_prod] at hg
  exact hg

theorem ofReal_setIntegral_eq_lintegral_ofReal_of_nonneg_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℝ}
    (hf_int : Integrable f (μ.restrict s))
    (hf_nonneg : 0 ≤ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (∫ x in s, f x ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  exact ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg

theorem ofReal_setIntegral_eq_lintegral_ofReal_of_nonneg_on
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ} (hf_int : Integrable f (μ.restrict s))
    (hf_nonneg : ∀ x, x ∈ s → 0 ≤ f x) :
    ENNReal.ofReal (∫ x in s, f x ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  exact ofReal_setIntegral_eq_lintegral_ofReal_of_nonneg_ae hf_int
    (ae_restrict_of_forall_mem hs hf_nonneg)

theorem projectedSimplexChartPreimage_subset_domain
    {n : ℕ} {s : Set (Fin (n - 1) → ℝ)} :
    projectedSimplexChartPreimage (n := n) s ⊆
      (projectedSimplexTotalDomain :
        Set ((Fin (n - 1) → ℝ) × ℝ)) := by
  intro p hp
  exact ⟨hp.2.1, hp.2.2⟩

theorem projectedSimplexChartPreimage_subset_positiveTotal
    {n : ℕ} {s : Set (Fin (n - 1) → ℝ)} :
    projectedSimplexChartPreimage (n := n) s ⊆
      {p : (Fin (n - 1) → ℝ) × ℝ | 0 < p.2} := by
  intro p hp
  exact hp.2.2

theorem projectedSimplexTotalMap_injOn_projectedSimplexTotalDomain
    {n : ℕ} (hn : 0 < n) :
    Set.InjOn
      (projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ)
      (projectedSimplexTotalDomain :
        Set ((Fin (n - 1) → ℝ) × ℝ)) := by
  intro p hp q hq hpq
  have hs_eq : p.2 = q.2 := by
    have htotal := congrArg gammaVectorTotal hpq
    simpa [projectedSimplexTotalMap, gammaVectorTotal_projectedSimplexTotalCoord hn]
      using htotal
  have hx_eq : p.1 = q.1 := by
    have hproj :
        projectedSourceNormalizedVector (projectedSimplexTotalCoord p.1 p.2) =
          projectedSourceNormalizedVector (projectedSimplexTotalCoord q.1 q.2) := by
      simpa [projectedSimplexTotalMap] using congrArg projectedSourceNormalizedVector hpq
    rw [
      projectedSourceNormalizedVector_projectedSimplexTotalCoord hn p.1 hp.2.ne',
      projectedSourceNormalizedVector_projectedSimplexTotalCoord hn q.1 hq.2.ne'] at hproj
    exact hproj
  exact Prod.ext hx_eq hs_eq

theorem differentiable_projectedSimplexTotalMap {n : ℕ} :
    Differentiable ℝ
      (projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  rw [differentiable_pi]
  intro i
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, hi]
    fun_prop
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, simplexLastCoord, hi]
    fun_prop

theorem projectedSimplexTotalMap_hasFDerivWithinAt
    {n : ℕ} (s : Set ((Fin (n - 1) → ℝ) × ℝ))
    (p : (Fin (n - 1) → ℝ) × ℝ) :
    HasFDerivWithinAt
      (projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ)
      (fderiv ℝ
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) p)
      s p := by
  exact (differentiable_projectedSimplexTotalMap.differentiableAt.hasFDerivAt).hasFDerivWithinAt

/-- Intermediate same-space chart `(x, s) ↦ (s • x, s)`.  The existing
`projectedSimplexTotalMap` is this scaling chart followed by the linear
completion of the last Gamma coordinate. -/
def projectedScaleTotalMap {n : ℕ} :
    ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ :=
  fun p => (fun i => p.1 i * p.2, p.2)

theorem measurable_projectedScaleTotalMap {n : ℕ} :
    Measurable (projectedScaleTotalMap :
      ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) := by
  unfold projectedScaleTotalMap
  fun_prop

theorem differentiable_projectedScaleTotalMap {n : ℕ} :
    Differentiable ℝ
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) := by
  unfold projectedScaleTotalMap
  fun_prop

theorem projectedScaleTotalMap_hasFDerivWithinAt
    {n : ℕ} (s : Set ((Fin (n - 1) → ℝ) × ℝ))
    (p : (Fin (n - 1) → ℝ) × ℝ) :
    HasFDerivWithinAt
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      (fderiv ℝ
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) p)
      s p := by
  exact (differentiable_projectedScaleTotalMap.differentiableAt.hasFDerivAt).hasFDerivWithinAt

instance projectedScaleTotalProductVolume_isAddHaar {n : ℕ} :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Fin (n - 1) → ℝ) × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The diagonal part of the scaling chart derivative: first projected
coordinates are multiplied by the total `s`, while the total coordinate itself
is fixed. -/
def projectedScaleTotalDiagonalLinearMap {n : ℕ} (s : ℝ) :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) × ℝ :=
  LinearMap.prodMap
    (s • (LinearMap.id : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ)))
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

theorem projectedScaleTotalDiagonalLinearMap_det
    {n : ℕ} (s : ℝ) :
    (projectedScaleTotalDiagonalLinearMap (n := n) s).det = s ^ (n - 1) := by
  unfold projectedScaleTotalDiagonalLinearMap
  rw [LinearMap.det_prodMap]
  rw [LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id]
  simp [Fintype.card_fin]

/-- The shear part of the scaling chart derivative.  It adds the total-coordinate
increment in the fixed projected direction `x` and leaves the total coordinate
unchanged. -/
def projectedScaleTotalShearLinearMap {n : ℕ} (x : Fin (n - 1) → ℝ) :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) × ℝ :=
  LinearMap.transvection
    (LinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ)
    (x, 0)

theorem projectedScaleTotalShearLinearMap_apply
    {n : ℕ} (x : Fin (n - 1) → ℝ)
    (q : (Fin (n - 1) → ℝ) × ℝ) :
    projectedScaleTotalShearLinearMap x q = (q.1 + q.2 • x, q.2) := by
  ext i <;> simp [projectedScaleTotalShearLinearMap, LinearMap.transvection.apply]

theorem projectedScaleTotalShearLinearMap_det
    {n : ℕ} (x : Fin (n - 1) → ℝ) :
    (projectedScaleTotalShearLinearMap x).det = 1 := by
  unfold projectedScaleTotalShearLinearMap
  rw [LinearMap.transvection.det]
  simp

/-- The full derivative of `(x, s) ↦ (s • x, s)`, factored as shear after
diagonal scaling. -/
def projectedScaleTotalFDerivLinearMap {n : ℕ}
    (p : (Fin (n - 1) → ℝ) × ℝ) :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) × ℝ :=
  (projectedScaleTotalShearLinearMap p.1).comp
    (projectedScaleTotalDiagonalLinearMap p.2)

theorem projectedScaleTotalFDerivLinearMap_apply
    {n : ℕ} (p q : (Fin (n - 1) → ℝ) × ℝ) :
    projectedScaleTotalFDerivLinearMap p q =
      (fun i => p.2 * q.1 i + q.2 * p.1 i, q.2) := by
  ext i <;>
    simp [projectedScaleTotalFDerivLinearMap,
      projectedScaleTotalShearLinearMap_apply,
      projectedScaleTotalDiagonalLinearMap]

theorem projectedScaleTotalFDerivLinearMap_det
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    (projectedScaleTotalFDerivLinearMap p).det = p.2 ^ (n - 1) := by
  unfold projectedScaleTotalFDerivLinearMap
  rw [LinearMap.det_comp]
  rw [projectedScaleTotalShearLinearMap_det, projectedScaleTotalDiagonalLinearMap_det]
  simp

theorem projectedScaleTotalFDerivLinearMap_toContinuousLinearMap_eq
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    LinearMap.toContinuousLinearMap (projectedScaleTotalFDerivLinearMap p) =
      (p.2 • (ContinuousLinearMap.fst ℝ (Fin (n - 1) → ℝ) ℝ) +
          (ContinuousLinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ).smulRight p.1).prod
        (ContinuousLinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ) := by
  ext q i <;>
    simp [projectedScaleTotalFDerivLinearMap_apply]

theorem projectedScaleTotalMap_hasFDerivAt_explicit
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    HasFDerivAt
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      (LinearMap.toContinuousLinearMap (projectedScaleTotalFDerivLinearMap p))
      p := by
  rw [projectedScaleTotalFDerivLinearMap_toContinuousLinearMap_eq]
  have hfirst :
      HasFDerivAt
        (fun q : (Fin (n - 1) → ℝ) × ℝ => q.2 • q.1)
        (p.2 • (ContinuousLinearMap.fst ℝ (Fin (n - 1) → ℝ) ℝ) +
          (ContinuousLinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ).smulRight p.1)
        p :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hsecond :
      HasFDerivAt
        (fun q : (Fin (n - 1) → ℝ) × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ (Fin (n - 1) → ℝ) ℝ)
        p :=
    hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  refine (hfirst.prodMk hsecond).congr_of_eventuallyEq ?_
  filter_upwards with q
  ext i <;> simp [projectedScaleTotalMap, smul_eq_mul, mul_comm]

theorem projectedScaleTotalMap_hasFDerivWithinAt_explicit
    {n : ℕ} (s : Set ((Fin (n - 1) → ℝ) × ℝ))
    (p : (Fin (n - 1) → ℝ) × ℝ) :
    HasFDerivWithinAt
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      (LinearMap.toContinuousLinearMap (projectedScaleTotalFDerivLinearMap p))
      s p := by
  exact (projectedScaleTotalMap_hasFDerivAt_explicit p).hasFDerivWithinAt

theorem projectedScaleTotalMap_fderiv_eq
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    fderiv ℝ
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      p =
      LinearMap.toContinuousLinearMap (projectedScaleTotalFDerivLinearMap p) := by
  exact (projectedScaleTotalMap_hasFDerivAt_explicit p).fderiv

theorem projectedScaleTotalMap_fderiv_det
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    (fderiv ℝ
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      p).det = p.2 ^ (n - 1) := by
  rw [projectedScaleTotalMap_fderiv_eq]
  simp [projectedScaleTotalFDerivLinearMap_det]

theorem projectedScaleTotalMap_injOn_positiveTotal {n : ℕ} :
    Set.InjOn
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ)
      {p : (Fin (n - 1) → ℝ) × ℝ | 0 < p.2} := by
  intro p hp q hq hpq
  have hs_eq : p.2 = q.2 := by
    simpa [projectedScaleTotalMap] using congrArg Prod.snd hpq
  have hx_eq : p.1 = q.1 := by
    funext i
    have hcoord := congrFun (congrArg Prod.fst hpq) i
    simp [projectedScaleTotalMap] at hcoord
    have hs_ne : p.2 ≠ 0 := hp.ne'
    rw [← hs_eq] at hcoord
    exact mul_right_cancel₀ hs_ne hcoord
  exact Prod.ext hx_eq hs_eq

theorem projectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_fderiv_mul
    {n : ℕ} {s : Set ((Fin (n - 1) → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hinj : Set.InjOn
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) s)
    (g : ((Fin (n - 1) → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal
          |(fderiv ℝ
            (projectedScaleTotalMap :
              ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) p).det| *
          g (projectedScaleTotalMap p) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure ((Fin (n - 1) → ℝ) × ℝ)) hs
    (fun p _ => projectedScaleTotalMap_hasFDerivWithinAt s p) hinj g

theorem projectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_totalPow_mul
    {n : ℕ} {s : Set ((Fin (n - 1) → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hinj : Set.InjOn
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) s)
    (g : ((Fin (n - 1) → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal |p.2 ^ (n - 1)| *
          g (projectedScaleTotalMap p) := by
  rw [projectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_fderiv_mul hs hinj g]
  exact setLIntegral_congr_fun hs fun p _ => by
    rw [projectedScaleTotalMap_fderiv_det]

theorem projectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_of_subset_positive
    {n : ℕ} {s : Set ((Fin (n - 1) → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hpos : s ⊆ {p : (Fin (n - 1) → ℝ) × ℝ | 0 < p.2})
    (g : ((Fin (n - 1) → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          g (projectedScaleTotalMap p) := by
  have hinj :
      Set.InjOn
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) s :=
    projectedScaleTotalMap_injOn_positiveTotal.mono hpos
  rw [projectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_totalPow_mul hs hinj g]
  exact setLIntegral_congr_fun hs fun p hp => by
    have hpow_nonneg : 0 ≤ p.2 ^ (n - 1) :=
      pow_nonneg (le_of_lt (hpos hp)) _
    rw [abs_of_nonneg hpow_nonneg]

theorem projectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
    {n : ℕ} {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s)
    (g : ((Fin (n - 1) → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        g y =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          g (projectedScaleTotalMap p) := by
  exact
    projectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_of_subset_positive
      (measurableSet_projectedSimplexChartPreimage hs)
      projectedSimplexChartPreimage_subset_positiveTotal g

/-- Linear completion from scaled projected coordinates and total mass to the
full `n` Gamma coordinates.  It appends the last coordinate as
`total - sum(first coordinates)`. -/
def projectedSimplexLinearCompletionMap {n : ℕ} :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i : Fin n =>
    if hi : i.val < n - 1 then
      p.1 ⟨i.val, hi⟩
    else
      p.2 - ∑ j : Fin (n - 1), p.1 j
  map_add' p q := by
    funext i
    by_cases hi : i.val < n - 1
    · simp [hi]
    · simp [hi]
      rw [Finset.sum_add_distrib]
      ring
  map_smul' c p := by
    funext i
    by_cases hi : i.val < n - 1
    · simp [hi]
    · simp [hi]
      rw [← Finset.mul_sum]
      ring

/-- Coordinate append map `(x, y_last) ↦ (x, y_last)`, used to separate the
volume-preserving coordinate split from the determinant-one completion shear. -/
def projectedSimplexAppendLastLinearMap {m : ℕ} :
    ((Fin m → ℝ) × ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun p := fun i : Fin (m + 1) =>
    if hi : i.val < m then p.1 ⟨i.val, hi⟩ else p.2
  map_add' p q := by
    funext i
    by_cases hi : i.val < m <;> simp [hi]
  map_smul' c p := by
    funext i
    by_cases hi : i.val < m <;> simp [hi]

theorem projectedSimplexAppendLastLinearMap_eq_snoc
    {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    projectedSimplexAppendLastLinearMap p = Fin.snoc p.1 p.2 := by
  funext i
  by_cases hi : i.val < m
  · simp [projectedSimplexAppendLastLinearMap, Fin.snoc, hi]
    apply congrArg p.1
    apply Fin.ext
    rfl
  · have hilast : i = Fin.last m := by
      apply Fin.ext
      have hle : i.val ≤ m := Nat.le_of_lt_succ i.isLt
      have hge : m ≤ i.val := le_of_not_gt hi
      exact le_antisymm hle hge
    subst hilast
    simp [projectedSimplexAppendLastLinearMap, Fin.snoc]

theorem projectedSimplexAppendLastLinearMap_measurePreserving {m : ℕ} :
    MeasurePreserving
      (projectedSimplexAppendLastLinearMap (m := m) :
        ((Fin m → ℝ) × ℝ) → Fin (m + 1) → ℝ) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hsplit :
      MeasurePreserving split.symm (volume : Measure (ℝ × (Fin m → ℝ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have hswap :
      MeasurePreserving Prod.swap
        (volume : Measure ((Fin m → ℝ) × ℝ))
        (volume : Measure (ℝ × (Fin m → ℝ))) := by
    rw [Measure.volume_eq_prod (Fin m → ℝ) ℝ, Measure.volume_eq_prod ℝ (Fin m → ℝ)]
    exact Measure.measurePreserving_swap
  have h := hsplit.comp hswap
  convert h using 1 <;> try rfl
  apply funext
  intro p
  apply funext
  intro i
  simpa [split] using
    congrFun (projectedSimplexAppendLastLinearMap_eq_snoc (m := m) p) i

/-- The linear functional summing the projected coordinates in the source
product space. -/
def projectedSimplexFirstCoordSumLinearMap {m : ℕ} :
    ((Fin m → ℝ) × ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ i : Fin m, p.1 i
  map_add' p q := by
    simp [Finset.sum_add_distrib]
  map_smul' c p := by
    simp [← Finset.mul_sum]

/-- The determinant-one shear `(x, total) ↦ (x, total - sum x)` before appending
the last coordinate. -/
def projectedSimplexCompletionShearLinearMap {m : ℕ} :
    ((Fin m → ℝ) × ℝ) →ₗ[ℝ] (Fin m → ℝ) × ℝ :=
  LinearMap.transvection
    (projectedSimplexFirstCoordSumLinearMap (m := m))
    (0, -1)

theorem projectedSimplexCompletionShearLinearMap_apply
    {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    projectedSimplexCompletionShearLinearMap p =
      (p.1, p.2 - ∑ i : Fin m, p.1 i) := by
  apply Prod.ext
  · funext i
    simp [projectedSimplexCompletionShearLinearMap,
      projectedSimplexFirstCoordSumLinearMap, LinearMap.transvection.apply]
  · simp [projectedSimplexCompletionShearLinearMap,
      projectedSimplexFirstCoordSumLinearMap, LinearMap.transvection.apply]
    ring

theorem projectedSimplexCompletionShearLinearMap_det
    {m : ℕ} :
    (projectedSimplexCompletionShearLinearMap (m := m)).det = 1 := by
  unfold projectedSimplexCompletionShearLinearMap
  rw [LinearMap.transvection.det]
  change 1 + (∑ i : Fin m, (0 : Fin m → ℝ) i) = 1
  simp

theorem projectedSimplexCompletionShearLinearMap_measurePreserving
    {m : ℕ} :
    MeasurePreserving
      (projectedSimplexCompletionShearLinearMap (m := m) :
        ((Fin m → ℝ) × ℝ) → (Fin m → ℝ) × ℝ) := by
  have hdet_ne :
      (projectedSimplexCompletionShearLinearMap (m := m)).det ≠ 0 := by
    rw [projectedSimplexCompletionShearLinearMap_det]
    norm_num
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin m → ℝ) × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(projectedSimplexCompletionShearLinearMap (m := m)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin m → ℝ) × ℝ)) hdet_ne]
  rw [projectedSimplexCompletionShearLinearMap_det]
  simp

/-- The same coordinate append map as `projectedSimplexAppendLastLinearMap`,
indexed by the ambient dimension `n` so its source exactly matches
`projectedSimplexLinearCompletionMap`. -/
def projectedSimplexAppendLastLinearMapFull {n : ℕ} :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i : Fin n =>
    if hi : i.val < n - 1 then p.1 ⟨i.val, hi⟩ else p.2
  map_add' p q := by
    funext i
    by_cases hi : i.val < n - 1 <;> simp [hi]
  map_smul' c p := by
    funext i
    by_cases hi : i.val < n - 1 <;> simp [hi]

theorem projectedSimplexAppendLastLinearMapFull_measurePreserving
    {n : ℕ} (hn : 0 < n) :
    MeasurePreserving
      (projectedSimplexAppendLastLinearMapFull (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  cases n with
  | zero => omega
  | succ m =>
      change MeasurePreserving
        (projectedSimplexAppendLastLinearMap (m := m) :
          ((Fin m → ℝ) × ℝ) → Fin (m + 1) → ℝ)
      exact projectedSimplexAppendLastLinearMap_measurePreserving (m := m)

/-- Full-dimension version of the determinant-one completion shear. -/
def projectedSimplexCompletionShearLinearMapFull {n : ℕ} :
    ((Fin (n - 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) × ℝ :=
  projectedSimplexCompletionShearLinearMap (m := n - 1)

theorem projectedSimplexCompletionShearLinearMapFull_apply
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    projectedSimplexCompletionShearLinearMapFull p =
      (p.1, p.2 - ∑ i : Fin (n - 1), p.1 i) :=
  projectedSimplexCompletionShearLinearMap_apply (m := n - 1) p

theorem projectedSimplexCompletionShearLinearMapFull_measurePreserving
    {n : ℕ} :
    MeasurePreserving
      (projectedSimplexCompletionShearLinearMapFull (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) :=
  projectedSimplexCompletionShearLinearMap_measurePreserving (m := n - 1)

theorem projectedSimplexLinearCompletionMap_eq_appendLast_comp_shear
    {n : ℕ} :
    projectedSimplexLinearCompletionMap (n := n) =
      (projectedSimplexAppendLastLinearMapFull (n := n)).comp
        (projectedSimplexCompletionShearLinearMapFull (n := n)) := by
  apply LinearMap.ext
  intro p
  funext i
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexLinearCompletionMap,
      projectedSimplexAppendLastLinearMapFull,
      projectedSimplexCompletionShearLinearMapFull_apply, hi]
  · simp [projectedSimplexLinearCompletionMap,
      projectedSimplexAppendLastLinearMapFull,
      projectedSimplexCompletionShearLinearMapFull_apply, hi]

theorem projectedSimplexLinearCompletionMap_measurePreserving
    {n : ℕ} (hn : 0 < n) :
    MeasurePreserving
      (projectedSimplexLinearCompletionMap (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  have h :=
    (projectedSimplexAppendLastLinearMapFull_measurePreserving hn).comp
      (projectedSimplexCompletionShearLinearMapFull_measurePreserving (n := n))
  rw [projectedSimplexLinearCompletionMap_eq_appendLast_comp_shear]
  simpa [LinearMap.coe_comp] using h

theorem projectedSimplexLinearCompletionMap_map_volume
    {n : ℕ} (hn : 0 < n) :
    Measure.map
      (projectedSimplexLinearCompletionMap (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ)
      (volume : Measure ((Fin (n - 1) → ℝ) × ℝ)) =
        (volume : Measure (Fin n → ℝ)) :=
  (projectedSimplexLinearCompletionMap_measurePreserving hn).map_eq

theorem projectedSimplexTotalMap_eq_linear_completion_projectedScaleTotalMap
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    projectedSimplexTotalMap p =
      fun i : Fin n =>
        if hi : i.val < n - 1 then
          (projectedScaleTotalMap p).1 ⟨i.val, hi⟩
        else
          (projectedScaleTotalMap p).2 -
            ∑ j : Fin (n - 1), (projectedScaleTotalMap p).1 j := by
  funext i
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, projectedScaleTotalMap, hi]
  · simp [projectedSimplexTotalMap, projectedSimplexTotalCoord, projectedScaleTotalMap,
      simplexLastCoord, hi, sub_eq_add_neg]
    rw [← Finset.sum_mul]
    ring

theorem projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap
    {n : ℕ} (p : (Fin (n - 1) → ℝ) × ℝ) :
    projectedSimplexTotalMap p =
      projectedSimplexLinearCompletionMap (projectedScaleTotalMap p) := by
  rw [projectedSimplexTotalMap_eq_linear_completion_projectedScaleTotalMap]
  rfl

theorem projectedSimplexLinearCompletionMap_left_inverse
    {n : ℕ} (hn : 0 < n) (p : (Fin (n - 1) → ℝ) × ℝ) :
    ((fun y : Fin n → ℝ => (projectFirst y, gammaVectorTotal y))
      (projectedSimplexLinearCompletionMap (n := n) p)) = p := by
  ext i
  · simp [projectFirst, projectedSimplexLinearCompletionMap]
  · calc
      gammaVectorTotal (projectedSimplexLinearCompletionMap (n := n) p) =
          (∑ i : Fin (n - 1),
              projectedSimplexLinearCompletionMap (n := n) p ⟨i.val, by omega⟩) +
            projectedSimplexLinearCompletionMap (n := n) p ⟨n - 1, by omega⟩ := by
        simpa [gammaVectorTotal] using
          fin_sum_projected_last hn (projectedSimplexLinearCompletionMap (n := n) p)
      _ = p.2 := by
        simp [projectedSimplexLinearCompletionMap]

theorem projectedSimplexLinearCompletionMap_right_inverse
    {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    projectedSimplexLinearCompletionMap
      ((projectFirst y, gammaVectorTotal y) :
        (Fin (n - 1) → ℝ) × ℝ) = y := by
  funext i
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexLinearCompletionMap, projectFirst, hi]
  · have hilast : i = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      have hle : i.val ≤ n - 1 := Nat.le_pred_of_lt i.isLt
      have hge : n - 1 ≤ i.val := le_of_not_gt hi
      exact le_antisymm hle hge
    rw [hilast]
    rw [gammaVectorTotal, fin_sum_projected_last hn]
    simp [projectedSimplexLinearCompletionMap, projectFirst]

def projectedSimplexLinearCompletionEquiv {n : ℕ} (hn : 0 < n) :
    ((Fin (n - 1) → ℝ) × ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := projectedSimplexLinearCompletionMap
  invFun := fun y => (projectFirst y, gammaVectorTotal y)
  map_add' := projectedSimplexLinearCompletionMap.map_add
  map_smul' := projectedSimplexLinearCompletionMap.map_smul
  left_inv := projectedSimplexLinearCompletionMap_left_inverse hn
  right_inv := projectedSimplexLinearCompletionMap_right_inverse hn

theorem projectedSimplexLinearCompletionEquiv_apply
    {n : ℕ} (hn : 0 < n) (p : (Fin (n - 1) → ℝ) × ℝ) :
    projectedSimplexLinearCompletionEquiv hn p =
      projectedSimplexLinearCompletionMap p := rfl

theorem projectedSimplexLinearCompletionMap_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective
      (projectedSimplexLinearCompletionMap (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  intro p q hpq
  have h :=
    congrArg
      (fun y : Fin n → ℝ => (projectFirst y, gammaVectorTotal y)) hpq
  simpa [projectedSimplexLinearCompletionMap_left_inverse hn] using h

theorem projectedSimplexTotalMap_image_eq_linearCompletion_image_projectedScaleTotalMap
    {n : ℕ} (s : Set ((Fin (n - 1) → ℝ) × ℝ)) :
    (projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) '' s =
      (projectedSimplexLinearCompletionMap (n := n)) ''
        ((projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨projectedScaleTotalMap p, ⟨p, hp, rfl⟩, ?_⟩
    exact (projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap p).symm
  · rintro ⟨z, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨p, hp, by
      rw [projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap, hz]⟩

theorem projectedSimplexLinearCompletionMap_preimage_projectedSimplexTotalMap_image
    {n : ℕ} (hn : 0 < n) (s : Set ((Fin (n - 1) → ℝ) × ℝ)) :
    (projectedSimplexLinearCompletionMap (n := n)) ⁻¹'
        ((projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) '' s) =
      (projectedScaleTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, hp, hpz⟩
    refine ⟨p, hp, ?_⟩
    exact projectedSimplexLinearCompletionMap_injective hn
      (by
        rw [← projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap p]
        exact hpz)
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap p⟩

theorem projectedSimplexLinearCompletionMap_setLIntegral_map_total_image
    {n : ℕ} (hn : 0 < n) {s : Set ((Fin (n - 1) → ℝ) × ℝ)}
    (hs_image : MeasurableSet
      ((projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) '' s))
    (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) '' s,
        g y
      ∂Measure.map (projectedSimplexLinearCompletionMap (n := n))
        (volume : Measure ((Fin (n - 1) → ℝ) × ℝ)) =
      ∫⁻ z in
        (projectedScaleTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) '' s,
        g (projectedSimplexLinearCompletionMap z) := by
  have hmeas :
      Measurable
        (projectedSimplexLinearCompletionMap (n := n) :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) :=
    (projectedSimplexLinearCompletionMap (n := n)).continuous_of_finiteDimensional.measurable
  rw [MeasureTheory.setLIntegral_map hs_image hg hmeas]
  rw [projectedSimplexLinearCompletionMap_preimage_projectedSimplexTotalMap_image hn s]

theorem projectedSimplexLinearCompletionMap_measurableEmbedding
    {n : ℕ} (hn : 0 < n) :
    MeasurableEmbedding
      (projectedSimplexLinearCompletionMap (n := n) :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) := by
  let e :=
    (projectedSimplexLinearCompletionEquiv hn).toContinuousLinearEquiv.toHomeomorph
  change MeasurableEmbedding (projectedSimplexLinearCompletionEquiv hn)
  exact e.measurableEmbedding

theorem projectedSimplexTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
    {n : ℕ} (hn : 0 < n) {s : Set (Fin (n - 1) → ℝ)}
    (hs : MeasurableSet s) (g : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        g y =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          g (projectedSimplexTotalMap p) := by
  let scaleImage : Set ((Fin (n - 1) → ℝ) × ℝ) :=
    (projectedScaleTotalMap :
      ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) ''
      projectedSimplexChartPreimage (n := n) s
  have hLmp :=
    projectedSimplexLinearCompletionMap_measurePreserving (n := n) hn
  have hLemb :=
    projectedSimplexLinearCompletionMap_measurableEmbedding (n := n) hn
  calc
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        g y =
      ∫⁻ y in
        (projectedSimplexLinearCompletionMap (n := n)) '' scaleImage,
        g y := by
        show
          ∫⁻ y in
              (projectedSimplexTotalMap :
                ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
                projectedSimplexChartPreimage (n := n) s,
              g y =
            ∫⁻ y in
              (projectedSimplexLinearCompletionMap (n := n)) ''
                ((projectedScaleTotalMap :
                  ((Fin (n - 1) → ℝ) × ℝ) → (Fin (n - 1) → ℝ) × ℝ) ''
                  projectedSimplexChartPreimage (n := n) s),
              g y
        rw [projectedSimplexTotalMap_image_eq_linearCompletion_image_projectedScaleTotalMap]
    _ =
      ∫⁻ z in
        scaleImage,
        g (projectedSimplexLinearCompletionMap z) := by
        exact (MeasureTheory.MeasurePreserving.setLIntegral_comp_emb
          hLmp hLemb g scaleImage).symm
    _ =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          g (projectedSimplexTotalMap p) := by
        rw [projectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
          hs (fun z => g (projectedSimplexLinearCompletionMap (n := n) z))]
        exact setLIntegral_congr_fun
          (measurableSet_projectedSimplexChartPreimage hs) fun p _ => by
            rw [projectedSimplexTotalMap_eq_linearCompletion_comp_projectedScaleTotalMap]

theorem projectedSimplexTotalCoord_nonneg
    {n : ℕ} {x : Fin (n - 1) → ℝ} {s : ℝ}
    (hx : DirichletSimplex x) (hs : 0 ≤ s) :
    ∀ i : Fin n, 0 ≤ projectedSimplexTotalCoord x s i := by
  intro i
  by_cases hi : i.val < n - 1
  · simp [projectedSimplexTotalCoord, hi, mul_nonneg (hx.1 ⟨i.val, hi⟩) hs]
  · simp [projectedSimplexTotalCoord, hi, mul_nonneg hx.2 hs]

theorem projectedSourceNormalizedVector_mem_DirichletSimplex
    {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < gammaVectorTotal x) :
    DirichletSimplex (projectedSourceNormalizedVector x) := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [projectedSourceNormalizedVector, projectFirst, sourceNormalizedVector]
    exact div_nonneg (hx ⟨i.val, by omega⟩) hV.le
  · rw [simplexLastCoord_projectedSourceNormalizedVector hn x hV.ne']
    exact div_nonneg (hx ⟨n - 1, by omega⟩) hV.le

theorem projectedSimplexTotalMap_image_projectedSimplexChartPreimage
    {n : ℕ} (hn : 0 < n) (s : Set (Fin (n - 1) → ℝ)) :
    (projectedSimplexTotalMap :
        ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
      projectedSimplexChartPreimage (n := n) s =
      {y : Fin n → ℝ |
        (∀ i, 0 ≤ y i) ∧
          0 < gammaVectorTotal y ∧
          projectedSourceNormalizedVector y ∈ s} := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact projectedSimplexTotalCoord_nonneg hp.2.1 hp.2.2.le
    · have htotal_eq :
          gammaVectorTotal (projectedSimplexTotalMap p) = p.2 := by
        simpa [projectedSimplexTotalMap] using
          gammaVectorTotal_projectedSimplexTotalCoord hn p.1 p.2
      rw [htotal_eq]
      exact hp.2.2
    · show projectedSourceNormalizedVector (projectedSimplexTotalMap p) ∈ s
      simpa [projectedSimplexTotalMap] using
        (by
          rw [projectedSourceNormalizedVector_projectedSimplexTotalCoord hn p.1 hp.2.2.ne']
          exact hp.1)
  · intro hy
    let p : (Fin (n - 1) → ℝ) × ℝ :=
      (projectedSourceNormalizedVector y, gammaVectorTotal y)
    refine ⟨p, ?_, ?_⟩
    · exact
        ⟨hy.2.2,
          projectedSourceNormalizedVector_mem_DirichletSimplex hn hy.1 hy.2.1,
          hy.2.1⟩
    · simpa [p, projectedSimplexTotalMap] using
        projectedSimplexTotalCoord_projectedSourceNormalizedVector hn y hy.2.1.ne'

theorem measurableSet_projectedSimplexTotalMap_image_projectedSimplexChartPreimage
    {n : ℕ} (hn : 0 < n) {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet
      ((projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
        projectedSimplexChartPreimage (n := n) s) := by
  rw [projectedSimplexTotalMap_image_projectedSimplexChartPreimage hn s]
  have hnonneg : MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
    have hclosed : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa [Set.setOf_forall] using
        (isClosed_iInter fun i : Fin n =>
          isClosed_le continuous_const (continuous_apply i))
    exact hclosed.measurableSet
  have htotal : MeasurableSet {y : Fin n → ℝ | 0 < gammaVectorTotal y} := by
    have hmeas : Measurable (gammaVectorTotal : (Fin n → ℝ) → ℝ) := by
      unfold gammaVectorTotal
      fun_prop
    exact measurableSet_Ioi.preimage hmeas
  have hproj : MeasurableSet
      {y : Fin n → ℝ | projectedSourceNormalizedVector y ∈ s} :=
    hs.preimage measurable_projectedSourceNormalizedVector
  exact hnonneg.inter (htotal.inter hproj)

theorem projectedSource_preimage_aeEq_projectedSimplexTotalMap_image
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    (s : Set (Fin (n - 1) → ℝ)) :
    (projectedSourceNormalizedVector ⁻¹' s) =ᵐ[gammaProductLaw alpha beta]
      ((projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
        projectedSimplexChartPreimage (n := n) s) := by
  rw [projectedSimplexTotalMap_image_projectedSimplexChartPreimage hn s]
  filter_upwards
    [gammaProductLaw_coordinates_positive_ae alpha halpha hbeta,
      gammaProductLaw_total_positive_ae hn alpha halpha hbeta] with y hy htotal
  exact propext
    ⟨fun hy_mem => ⟨fun i => (hy i).le, htotal, hy_mem⟩,
      fun hy_mem => hy_mem.2.2⟩

theorem gammaProductLaw_projectedSource_preimage_eq_projectedSimplexTotalMap_image
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    (s : Set (Fin (n - 1) → ℝ)) :
    gammaProductLaw alpha beta (projectedSourceNormalizedVector ⁻¹' s) =
      gammaProductLaw alpha beta
        ((projectedSimplexTotalMap :
            ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s) := by
  exact measure_congr
    (projectedSource_preimage_aeEq_projectedSimplexTotalMap_image
      hn halpha hbeta s)

theorem ProjectedDirichletLaw_supported_on_projectedSimplex
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ∀ᵐ x ∂ProjectedDirichletLaw alpha beta, DirichletSimplex x := by
  rw [ProjectedDirichletLaw_eq_map_projectedSourceNormalizedVector]
  rw [MeasureTheory.ae_map_iff measurable_projectedSourceNormalizedVector.aemeasurable
    measurableSet_DirichletSimplex]
  filter_upwards [gammaProductLaw_coordinates_positive_ae alpha halpha hbeta,
    gammaProductLaw_total_positive_ae hn alpha halpha hbeta] with x hx hV
  exact projectedSourceNormalizedVector_mem_DirichletSimplex hn (fun i => (hx i).le) hV

theorem ProjectedDirichletLaw_projectedSimplex_probability_one
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ProjectedDirichletLaw alpha beta {x | DirichletSimplex x} = 1 := by
  letI : IsProbabilityMeasure (ProjectedDirichletLaw alpha beta) :=
    ProjectedDirichletLaw_isProbability alpha halpha hbeta
  exact (MeasureTheory.mem_ae_iff_prob_eq_one
    (μ := ProjectedDirichletLaw alpha beta) measurableSet_DirichletSimplex).1
    (ProjectedDirichletLaw_supported_on_projectedSimplex hn alpha halpha hbeta)

