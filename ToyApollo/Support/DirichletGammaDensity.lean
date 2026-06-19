import Mathlib
import ToyApollo.Support.DirichletGamma

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

noncomputable section

/-- Source Gamma law displayed as a Lebesgue density. -/
theorem gammaScaleLaw_eq_withDensity_gammaPDF (alpha beta : ℝ) :
    gammaScaleLaw alpha beta =
      (volume : Measure ℝ).withDensity
        (ProbabilityTheory.gammaPDF alpha beta⁻¹) := by
  rfl

/-- Product Gamma law displayed as a finite product of one-dimensional Gamma
Lebesgue densities. This is the source-side measure before the Jacobian step. -/
theorem gammaProductLaw_eq_pi_withDensity_gammaPDF
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    gammaProductLaw alpha beta =
      Measure.pi fun i =>
        (volume : Measure ℝ).withDensity
          (ProbabilityTheory.gammaPDF (alpha i) beta⁻¹) := by
  rfl

theorem gammaProductLaw_eq_pi_withDensity_gammaPDFReal
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    gammaProductLaw alpha beta =
      Measure.pi fun i =>
        (volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal
            (ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ x)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod_ennreal
    {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprodmeas :
          Measurable
            (fun y : (i : Fin n) → E (Fin.succ i) =>
              ∏ i : Fin n, f (Fin.succ i) (y i)) := by
        fun_prop
      calc
        ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂Measure.pi μ =
            ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
              f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
              ∂(μ 0).prod (Measure.pi fun i => μ i.succ) := by
          rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
          apply lintegral_congr
          intro a
          rw [Fin.prod_univ_succ]
          have h0 :
              f 0 ((MeasurableEquiv.piFinSuccAbove E 0).symm a 0) = f 0 a.1 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
            change
              f 0 (Fin.insertNth (0 : Fin (n + 1)) a.1 (fun j => a.2 j) 0) =
                f 0 a.1
            rw [Fin.insertNth_apply_same]
          have htail : ∀ j : Fin n,
              f (Fin.succ j)
                  ((MeasurableEquiv.piFinSuccAbove E 0).symm a (Fin.succ j)) =
                f (Fin.succ j) (a.2 j) := by
            intro j
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
            change
              f ((0 : Fin (n + 1)).succAbove j)
                  (Fin.insertNth (0 : Fin (n + 1)) a.1 (fun j => a.2 j)
                    ((0 : Fin (n + 1)).succAbove j)) =
                f ((0 : Fin (n + 1)).succAbove j) (a.2 j)
            rw [Fin.insertNth_apply_succAbove]
          rw [h0]
          exact congrArg (fun z => f 0 a.1 * z)
            (Finset.prod_congr rfl fun j _ => htail j)
        _ =
            (∫⁻ x, f 0 x ∂μ 0) *
              ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
          rw [MeasureTheory.lintegral_prod]
          · simp_rw [MeasureTheory.lintegral_const_mul _ hprodmeas]
            rw [ih (fun i => f (Fin.succ i)) (fun i => hf _)]
            rw [MeasureTheory.lintegral_mul_const _ (hf 0)]
          · fun_prop
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
          rw [Fin.prod_univ_succ]

theorem pi_withDensity_fin
    {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞)
    [∀ i, SigmaFinite ((μ i).withDensity (f i))]
    (hf : ∀ i, Measurable (f i)) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) ?_
  intro s hs
  rw [withDensity_apply]
  · rw [← lintegral_indicator
      (MeasurableSet.pi Set.finite_univ.countable fun i _ => hs i)]
    calc
      ∫⁻ x : (i : Fin n) → E i,
          Set.indicator (Set.pi Set.univ s) (fun x => ∏ i, f i (x i)) x
          ∂Measure.pi μ =
        ∫⁻ x : (i : Fin n) → E i,
          ∏ i, Set.indicator (s i) (f i) (x i) ∂Measure.pi μ := by
          apply lintegral_congr
          intro x
          classical
          by_cases hx : x ∈ Set.pi Set.univ s
          · have hxi : ∀ i : Fin n, x i ∈ s i := by
              intro i
              exact hx i (Set.mem_univ i)
            rw [Set.indicator_of_mem hx]
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [Set.indicator_of_mem (hxi i)]
          · have hnot : ∃ i : Fin n, x i ∉ s i := by
              by_contra hnone
              rw [not_exists] at hnone
              exact hx (by simpa [Set.mem_pi] using hnone)
            rcases hnot with ⟨i, hi⟩
            have hprod :
                (∏ j : Fin n, Set.indicator (s j) (f j) (x j)) = 0 := by
              exact Finset.prod_eq_zero (Finset.mem_univ i)
                (by rw [Set.indicator_of_notMem hi])
            rw [Set.indicator_of_notMem hx, hprod]
      _ = ∏ i, ∫⁻ x in s i, f i x ∂μ i := by
        rw [lintegral_fin_nat_prod_eq_prod_ennreal
          (fun i x => Set.indicator (s i) (f i) x)
          (fun i => (hf i).indicator (hs i))]
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [lintegral_indicator (hs i)]
      _ = ∏ i, ((μ i).withDensity (f i)) (s i) := by
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [withDensity_apply _ (hs i)]
  · exact MeasurableSet.pi Set.finite_univ.countable fun i _ => hs i

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
      simpa using (Fin.sum_univ_castSucc (f := alpha))

theorem fin_prod_projected_last
    {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (∏ i : Fin n, f i) =
      (∏ i : Fin (n - 1), f ⟨i.val, by omega⟩) *
        f ⟨n - 1, by omega⟩ := by
  cases n with
  | zero => cases hn
  | succ m =>
      simpa using (Fin.prod_univ_castSucc (f := f))

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
  exact MeasureTheory.setLIntegral_prod g (by simpa [projectedSimplexChartPreimage_eq_prod] using hg)

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
  convert hfirst.prodMk hsecond using 1
  apply funext
  intro q
  apply Prod.ext
  · funext i
    simp [projectedScaleTotalMap, smul_eq_mul, mul_comm]
  · simp [projectedScaleTotalMap]

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
  convert h using 1
  ext p i
  simp [projectedSimplexAppendLastLinearMap_eq_snoc, split]

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
      simpa [projectedSimplexAppendLastLinearMapFull,
        projectedSimplexAppendLastLinearMap] using
        (projectedSimplexAppendLastLinearMap_measurePreserving (m := m))

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
  simpa [e, LinearEquiv.coe_toContinuousLinearEquiv'] using e.measurableEmbedding

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

/-- Real-valued product Gamma density on the source coordinates. -/
def gammaProductPDFReal {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ (y i)

theorem measurable_gammaProductPDFReal {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    Measurable (gammaProductPDFReal alpha beta) := by
  unfold gammaProductPDFReal
  fun_prop

theorem gammaProductPDFReal_nonneg {n : ℕ} {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) (y : Fin n → ℝ) :
    0 ≤ gammaProductPDFReal alpha beta y := by
  unfold gammaProductPDFReal
  exact Finset.prod_nonneg fun i _ =>
    ProbabilityTheory.gammaPDFReal_nonneg (halpha i) (inv_pos.mpr hbeta) (y i)

theorem gammaProductPDF_eq_ofReal_gammaProductPDFReal
    {n : ℕ} {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) (y : Fin n → ℝ) :
    (∏ i : Fin n, ProbabilityTheory.gammaPDF (alpha i) beta⁻¹ (y i)) =
      ENNReal.ofReal (gammaProductPDFReal alpha beta y) := by
  rw [gammaProductPDFReal]
  simp only [ProbabilityTheory.gammaPDF]
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact ProbabilityTheory.gammaPDFReal_nonneg (halpha i) (inv_pos.mpr hbeta) (y i)

theorem gammaProductLaw_eq_withDensity_gammaProductPDFReal
    {n : ℕ} {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    gammaProductLaw alpha beta =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun y => ENNReal.ofReal (gammaProductPDFReal alpha beta y)) := by
  rw [gammaProductLaw_eq_pi_withDensity_gammaPDFReal]
  calc
    Measure.pi
        (fun i : Fin n =>
          (volume : Measure ℝ).withDensity
            (fun x =>
              ENNReal.ofReal
                (ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ x))) =
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity
          (fun y : Fin n → ℝ =>
            ∏ i : Fin n,
              ENNReal.ofReal
                (ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ (y i))) := by
      exact pi_withDensity_fin
        (fun i : Fin n =>
          fun x : ℝ =>
            ENNReal.ofReal
              (ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ x))
        (fun i => by fun_prop)
    _ =
        (volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ENNReal.ofReal (gammaProductPDFReal alpha beta y)) := by
      rw [← volume_pi]
      congr with y
      rw [gammaProductPDFReal]
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i _
      exact ProbabilityTheory.gammaPDFReal_nonneg (halpha i) (inv_pos.mpr hbeta) (y i)

theorem gammaProductPDFReal_lintegral_projectedSource_preimage_eq_projectedSimplexTotalMap_image
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ∫⁻ y in projectedSourceNormalizedVector ⁻¹' s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) =
      ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) := by
  have hmeasure :=
    gammaProductLaw_projectedSource_preimage_eq_projectedSimplexTotalMap_image
      hn halpha hbeta s
  rw [gammaProductLaw_eq_withDensity_gammaProductPDFReal halpha hbeta] at hmeasure
  rw [withDensity_apply _
      (hs.preimage measurable_projectedSourceNormalizedVector),
    withDensity_apply _
      (measurableSet_projectedSimplexTotalMap_image_projectedSimplexChartPreimage
        hn hs)] at hmeasure
  exact hmeasure

theorem ProjectedDirichletLaw_eq_lintegral_gammaProductPDFReal_projectedSimplexTotalMap_image
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ProjectedDirichletLaw alpha beta s =
      ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) := by
  rw [ProjectedDirichletLaw_eq_map_projectedSourceNormalizedVector]
  rw [Measure.map_apply measurable_projectedSourceNormalizedVector hs]
  rw [gammaProductLaw_eq_withDensity_gammaProductPDFReal halpha hbeta]
  rw [withDensity_apply _ (hs.preimage measurable_projectedSourceNormalizedVector)]
  exact
    gammaProductPDFReal_lintegral_projectedSource_preimage_eq_projectedSimplexTotalMap_image
      hn halpha hbeta hs

theorem gammaProductPDFReal_projectedSimplexTotalCoord
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (x : Fin (n - 1) → ℝ) (s : ℝ) :
    gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x s) =
      (∏ i : Fin (n - 1),
        ProbabilityTheory.gammaPDFReal
          (alpha ⟨i.val, by omega⟩) beta⁻¹ (x i * s)) *
        ProbabilityTheory.gammaPDFReal
          (alpha ⟨n - 1, by omega⟩) beta⁻¹
          (simplexLastCoord x * s) := by
  rw [gammaProductPDFReal, fin_prod_projected_last hn]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro i _
    simp [projectedSimplexTotalCoord]
  · rw [projectedSimplexTotalCoord_last hn]

theorem projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_iterated
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ)
    (s : Set (Fin (n - 1) → ℝ)) :
    ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) =
      ∫⁻ x in s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x},
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal
            (t ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t)) := by
  refine projectedSimplexChartPreimage_lintegral_eq_iterated
    (n := n) (s := s)
    (fun p =>
      ENNReal.ofReal
        (p.2 ^ (n - 1) *
          gammaProductPDFReal alpha beta (projectedSimplexTotalMap p))) ?_
  have hreal :
      Measurable fun p : (Fin (n - 1) → ℝ) × ℝ =>
        p.2 ^ (n - 1) *
          gammaProductPDFReal alpha beta (projectedSimplexTotalMap p) := by
    exact (by fun_prop : Measurable fun p : (Fin (n - 1) → ℝ) × ℝ => p.2 ^ (n - 1)).mul
      ((measurable_gammaProductPDFReal alpha beta).comp measurable_projectedSimplexTotalMap)
  exact hreal.ennreal_ofReal.aemeasurable

/--
The Dirichlet density on the first `n - 1` coordinates, with the source domain
restriction included in the definition.
-/
def DirichletPDF {n : ℕ} (alpha : Fin n → ℝ) : (Fin (n - 1) → ℝ) → ℝ :=
  by
    classical
    exact fun x =>
      if hn : 0 < n then
        if DirichletSimplex x then
          dirichletNormalizer alpha *
            (∏ i : Fin (n - 1), (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
            (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1)
        else 0
      else 0

theorem DirichletPDF_formula_on_simplex
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {x : Fin (n - 1) → ℝ}
    (hx : DirichletSimplex x) :
    DirichletPDF alpha x =
      dirichletNormalizer alpha *
        (∏ i : Fin (n - 1), (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
        (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1) := by
  simp [DirichletPDF, hn, hx]

/--
Source-side density expression obtained from the normalized-Gamma
change-of-variables calculation before carrying out the final Gamma integral.
This is intentionally not definitionally equal to `DirichletPDF`.
-/
def normalizedGammaDirichletDensity {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    (Fin (n - 1) → ℝ) → ℝ :=
  fun x =>
    if hn : 0 < n then
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (n - 1) *
          (∏ i : Fin (n - 1),
            ProbabilityTheory.gammaPDFReal (alpha ⟨i.val, by omega⟩) beta⁻¹ (x i * s)) *
          ProbabilityTheory.gammaPDFReal (alpha ⟨n - 1, by omega⟩) beta⁻¹
            (simplexLastCoord x * s)
    else 0

theorem normalizedGammaDirichletDensity_source_integral
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (x : Fin (n - 1) → ℝ) :
    normalizedGammaDirichletDensity alpha beta x =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (n - 1) *
          (∏ i : Fin (n - 1),
            ProbabilityTheory.gammaPDFReal (alpha ⟨i.val, by omega⟩) beta⁻¹ (x i * s)) *
          ProbabilityTheory.gammaPDFReal (alpha ⟨n - 1, by omega⟩) beta⁻¹
            (simplexLastCoord x * s) := by
  simp [normalizedGammaDirichletDensity, hn]

theorem normalizedGammaDirichletDensity_source_integral_gammaProductPDFReal
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (x : Fin (n - 1) → ℝ) :
    normalizedGammaDirichletDensity alpha beta x =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (n - 1) *
          gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x s) := by
  rw [normalizedGammaDirichletDensity_source_integral hn]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
    rw [gammaProductPDFReal_projectedSimplexTotalCoord hn]
    ring

theorem ofReal_normalizedGammaDirichletDensity_eq_lintegral_source_integral
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    (x : Fin (n - 1) → ℝ)
    (h_int : Integrable
      (fun t : ℝ =>
        t ^ (n - 1) *
          gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (t ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t)) := by
  rw [normalizedGammaDirichletDensity_source_integral_gammaProductPDFReal hn]
  refine ofReal_setIntegral_eq_lintegral_ofReal_of_nonneg_on
    measurableSet_Ioi h_int ?_
  intro t ht
  exact mul_nonneg (pow_nonneg (le_of_lt ht) _)
    (gammaProductPDFReal_nonneg halpha hbeta _)

theorem projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_on_simplex
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s)
    (h_int : ∀ x : Fin (n - 1) → ℝ,
      Integrable
        (fun t : ℝ =>
          t ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) =
      ∫⁻ x in s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x},
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  rw [projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_iterated]
  exact setLIntegral_congr_fun
    (hs.inter measurableSet_DirichletSimplex) fun x _ =>
      (ofReal_normalizedGammaDirichletDensity_eq_lintegral_source_integral
        hn halpha hbeta x (h_int x)).symm

theorem gammaPDFReal_eq_zero_of_neg {a r x : ℝ} (hx : x < 0) :
    ProbabilityTheory.gammaPDFReal a r x = 0 := by
  simp [ProbabilityTheory.gammaPDFReal, not_le.mpr hx]

theorem DirichletPDF_zero_off_simplex
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {x : Fin (n - 1) → ℝ}
    (hx : ¬ DirichletSimplex x) :
    DirichletPDF alpha x = 0 := by
  simp [DirichletPDF, hn, hx]

theorem DirichletPDF_zero_of_lastCoord_neg
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {x : Fin (n - 1) → ℝ}
    (hxlast : simplexLastCoord x < 0) :
    DirichletPDF alpha x = 0 := by
  exact DirichletPDF_zero_off_simplex hn fun hx => not_le_of_gt hxlast hx.2

theorem DirichletPDF_zero_of_coord_neg
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {x : Fin (n - 1) → ℝ}
    (j : Fin (n - 1)) (hxj : x j < 0) :
    DirichletPDF alpha x = 0 := by
  exact DirichletPDF_zero_off_simplex hn fun hx => not_le_of_gt hxj (hx.1 j)

theorem normalizedGammaDirichletDensity_zero_of_lastCoord_neg
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {x : Fin (n - 1) → ℝ} (hxlast : simplexLastCoord x < 0) :
    normalizedGammaDirichletDensity alpha beta x = 0 := by
  rw [normalizedGammaDirichletDensity_source_integral hn]
  exact setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
    have harg : simplexLastCoord x * s < 0 := mul_neg_of_neg_of_pos hxlast hs
    have hpdf :
        ProbabilityTheory.gammaPDFReal (alpha ⟨n - 1, by omega⟩) beta⁻¹
          (simplexLastCoord x * s) = 0 :=
      gammaPDFReal_eq_zero_of_neg harg
    simp [hpdf]

theorem normalizedGammaDirichletDensity_zero_of_coord_neg
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {x : Fin (n - 1) → ℝ} (j : Fin (n - 1)) (hxj : x j < 0) :
    normalizedGammaDirichletDensity alpha beta x = 0 := by
  rw [normalizedGammaDirichletDensity_source_integral hn]
  exact setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
    have harg : x j * s < 0 := mul_neg_of_neg_of_pos hxj hs
    have hpdf :
        ProbabilityTheory.gammaPDFReal (alpha ⟨j.val, by omega⟩) beta⁻¹ (x j * s) = 0 :=
      gammaPDFReal_eq_zero_of_neg harg
    have hprod :
        (∏ i : Fin (n - 1),
          ProbabilityTheory.gammaPDFReal (alpha ⟨i.val, by omega⟩) beta⁻¹ (x i * s)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ j) hpdf
    simp [hprod]

theorem normalizedGammaDirichletDensity_zero_off_simplex
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {x : Fin (n - 1) → ℝ} (hx : ¬ DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x = 0 := by
  classical
  by_cases hlast : 0 ≤ simplexLastCoord x
  · have hnotcoords : ¬ ∀ i : Fin (n - 1), 0 ≤ x i := by
      intro hcoords
      exact hx ⟨hcoords, hlast⟩
    rw [not_forall] at hnotcoords
    rcases hnotcoords with ⟨j, hj⟩
    exact normalizedGammaDirichletDensity_zero_of_coord_neg hn alpha beta j (lt_of_not_ge hj)
  · exact normalizedGammaDirichletDensity_zero_of_lastCoord_neg hn alpha beta (lt_of_not_ge hlast)

theorem normalizedGammaDirichletDensity_eq_DirichletPDF_off_simplex
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {x : Fin (n - 1) → ℝ} (hx : ¬ DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x = DirichletPDF alpha x := by
  rw [normalizedGammaDirichletDensity_zero_off_simplex hn alpha beta hx,
    DirichletPDF_zero_off_simplex hn hx]

theorem setLIntegral_normalizedGammaDirichletDensity_inter_simplex
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ∫⁻ x in s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x},
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) =
      ∫⁻ x in s, ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  rw [← lintegral_indicator (hs.inter measurableSet_DirichletSimplex)]
  rw [← lintegral_indicator hs]
  exact lintegral_congr_ae <| Filter.Eventually.of_forall fun x => by
    by_cases hx_simplex : DirichletSimplex x
    · by_cases hx_s : x ∈ s
      · simp [Set.indicator_of_mem, hx_s, hx_simplex]
      · simp [Set.indicator_of_notMem, hx_s]
    · have hzero :
          ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) = 0 := by
        rw [normalizedGammaDirichletDensity_zero_off_simplex hn alpha beta hx_simplex]
        simp
      by_cases hx_s : x ∈ s
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx_s, hx_simplex, hzero]
      · simp [Set.indicator_of_notMem, hx_s]

theorem ofReal_normalizedGammaDirichletDensity_eq_lintegral_source_integral_ae_restrict
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ∀ᵐ x ∂(volume : Measure (Fin (n - 1) → ℝ)),
      x ∈ s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x} →
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) =
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal
              (t ^ (n - 1) *
                gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t)) := by
  let A : Set (Fin (n - 1) → ℝ) :=
    s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x}
  let inner : (Fin (n - 1) → ℝ) → ℝ≥0∞ := fun x =>
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (t ^ (n - 1) *
          gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
  have hA : MeasurableSet A := hs.inter measurableSet_DirichletSimplex
  have hinner_meas : AEMeasurable inner ((volume : Measure (Fin (n - 1) → ℝ)).restrict A) := by
    have hF :
        Measurable fun p : (Fin (n - 1) → ℝ) × ℝ =>
          ENNReal.ofReal
            (p.2 ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord p.1 p.2)) := by
      have hreal :
          Measurable fun p : (Fin (n - 1) → ℝ) × ℝ =>
            p.2 ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord p.1 p.2) :=
        (by fun_prop : Measurable fun p : (Fin (n - 1) → ℝ) × ℝ => p.2 ^ (n - 1)).mul
          ((measurable_gammaProductPDFReal alpha beta).comp measurable_projectedSimplexTotalMap)
      exact hreal.ennreal_ofReal
    have hmeas :
        Measurable fun x : Fin (n - 1) → ℝ =>
          ∫⁻ t : ℝ,
            ENNReal.ofReal
              (t ^ (n - 1) *
                gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
            ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa using
        (hF.lintegral_prod_right'
          (ν := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
    simpa [inner] using hmeas.aemeasurable.restrict
  have himage_finite :
      (∫⁻ y in
          (projectedSimplexTotalMap :
            ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
            projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal (gammaProductPDFReal alpha beta y)) ≠ ∞ := by
    have hmeasure_ne_top :
        gammaProductLaw alpha beta
            ((projectedSimplexTotalMap :
              ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
              projectedSimplexChartPreimage (n := n) s) ≠ ∞ :=
      letI : IsProbabilityMeasure (gammaProductLaw alpha beta) :=
        gammaProductLaw_isProbability alpha halpha hbeta
      measure_ne_top (gammaProductLaw alpha beta) _
    rw [gammaProductLaw_eq_withDensity_gammaProductPDFReal halpha hbeta] at hmeasure_ne_top
    rw [withDensity_apply _
      (measurableSet_projectedSimplexTotalMap_image_projectedSimplexChartPreimage
        hn hs)] at hmeasure_ne_top
    exact hmeasure_ne_top
  have himage_eq_chart :
      (∫⁻ y in
          (projectedSimplexTotalMap :
            ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
            projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal (gammaProductPDFReal alpha beta y)) =
        ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal
            (p.2 ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
    calc
      (∫⁻ y in
          (projectedSimplexTotalMap :
            ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
            projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal (gammaProductPDFReal alpha beta y)) =
        ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal (p.2 ^ (n - 1)) *
            ENNReal.ofReal
              (gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
          rw [projectedSimplexTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
            hn hs (fun y => ENNReal.ofReal (gammaProductPDFReal alpha beta y))]
      _ =
        ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
          ENNReal.ofReal
            (p.2 ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
          exact setLIntegral_congr_fun
            (measurableSet_projectedSimplexChartPreimage hs) fun p hp => by
              have hpow_nonneg : 0 ≤ p.2 ^ (n - 1) :=
                pow_nonneg (le_of_lt hp.2.2) _
              exact (ENNReal.ofReal_mul hpow_nonneg).symm
  have hinner_set_finite :
      (∫⁻ x in A, inner x ∂(volume : Measure (Fin (n - 1) → ℝ))) ≠ ∞ := by
    have hiter :=
      projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_iterated
        (n := n) alpha beta s
    rw [← hiter, ← himage_eq_chart]
    exact himage_finite
  have hinner_lt_top_restrict :
      ∀ᵐ x ∂((volume : Measure (Fin (n - 1) → ℝ)).restrict A), inner x < ∞ :=
    ae_lt_top' hinner_meas hinner_set_finite
  have hinner_lt_top :
      ∀ᵐ x ∂(volume : Measure (Fin (n - 1) → ℝ)), x ∈ A → inner x < ∞ := by
    rwa [ae_restrict_iff' hA] at hinner_lt_top_restrict
  filter_upwards [hinner_lt_top] with x hx_finite hxA
  have hreal_to_lintegral :
      normalizedGammaDirichletDensity alpha beta x = (inner x).toReal := by
    rw [normalizedGammaDirichletDensity_source_integral_gammaProductPDFReal hn]
    have hnonneg :
        0 ≤ᵐ[((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))]
          (fun t : ℝ =>
            t ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (pow_nonneg (le_of_lt ht) _)
        (gammaProductPDFReal_nonneg halpha hbeta _)
    have hmeas_coord : Measurable fun t : ℝ => projectedSimplexTotalCoord x t := by
      refine measurable_pi_lambda _ fun i => ?_
      by_cases hi : i.val < n - 1
      · simp [projectedSimplexTotalCoord, hi]
        fun_prop
      · simp [projectedSimplexTotalCoord, hi]
        fun_prop
    have hstrong :
        AEStronglyMeasurable
          (fun t : ℝ =>
            t ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      exact ((by fun_prop : Measurable fun t : ℝ => t ^ (n - 1)).mul
        ((measurable_gammaProductPDFReal alpha beta).comp hmeas_coord)).aestronglyMeasurable.restrict
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg hstrong]
  rw [hreal_to_lintegral]
  exact ENNReal.ofReal_toReal (ne_of_lt (hx_finite hxA))

theorem projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_setwise
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  let A : Set (Fin (n - 1) → ℝ) :=
    s ∩ {x : Fin (n - 1) → ℝ | DirichletSimplex x}
  have hA : MeasurableSet A := hs.inter measurableSet_DirichletSimplex
  rw [projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_iterated]
  calc
    ∫⁻ x in A,
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal
            (t ^ (n - 1) *
              gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t)) =
      ∫⁻ x in A,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
        exact setLIntegral_congr_fun_ae hA
          ((ofReal_normalizedGammaDirichletDensity_eq_lintegral_source_integral_ae_restrict
            hn halpha hbeta hs).mono fun x hx hxA => (hx hxA).symm)
    _ =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
        exact setLIntegral_normalizedGammaDirichletDensity_inter_simplex hn alpha beta hs

theorem projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s)
    (h_int : ∀ x : Fin (n - 1) → ℝ,
      Integrable
        (fun t : ℝ =>
          t ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  rw [projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_on_simplex
    hn halpha hbeta hs h_int]
  exact setLIntegral_normalizedGammaDirichletDensity_inter_simplex hn alpha beta hs

theorem projectedSimplexTotalMap_image_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s)
    (h_int : ∀ x : Fin (n - 1) → ℝ,
      Integrable
        (fun t : ℝ =>
          t ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalCoord x t))
        ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  calc
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          ENNReal.ofReal
            (gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
        rw [projectedSimplexTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
          hn hs (fun y => ENNReal.ofReal (gammaProductPDFReal alpha beta y))]
    _ =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
        exact setLIntegral_congr_fun
          (measurableSet_projectedSimplexChartPreimage hs) fun p hp => by
            have hpow_nonneg : 0 ≤ p.2 ^ (n - 1) :=
              pow_nonneg (le_of_lt hp.2.2) _
            exact (ENNReal.ofReal_mul hpow_nonneg).symm
    _ =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
        exact
          projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity
            hn halpha hbeta hs h_int

theorem projectedSimplexTotalMap_image_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_setwise
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {s : Set (Fin (n - 1) → ℝ)} (hs : MeasurableSet s) :
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
  calc
    ∫⁻ y in
        (projectedSimplexTotalMap :
          ((Fin (n - 1) → ℝ) × ℝ) → Fin n → ℝ) ''
          projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (gammaProductPDFReal alpha beta y) =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal (p.2 ^ (n - 1)) *
          ENNReal.ofReal
            (gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
        rw [projectedSimplexTotalMap_lintegral_image_eq_lintegral_totalPow_mul_chart
          hn hs (fun y => ENNReal.ofReal (gammaProductPDFReal alpha beta y))]
    _ =
      ∫⁻ p in projectedSimplexChartPreimage (n := n) s,
        ENNReal.ofReal
          (p.2 ^ (n - 1) *
            gammaProductPDFReal alpha beta (projectedSimplexTotalMap p)) := by
        exact setLIntegral_congr_fun
          (measurableSet_projectedSimplexChartPreimage hs) fun p hp => by
            have hpow_nonneg : 0 ≤ p.2 ^ (n - 1) :=
              pow_nonneg (le_of_lt hp.2.2) _
            exact (ENNReal.ofReal_mul hpow_nonneg).symm
    _ =
      ∫⁻ x in s,
        ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x) := by
        exact
          projectedSimplexChartPreimage_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_setwise
            hn halpha hbeta hs

theorem gammaDirichlet_projected_power_s_split
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ)
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) {s : ℝ} (hs : 0 < s) :
    (∏ i : Fin (n - 1), (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
        (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1) =
      (∏ i : Fin (n - 1), (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
        (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1) *
        ((∏ i : Fin (n - 1), s ^ (alpha ⟨i.val, by omega⟩ - 1)) *
          s ^ (alpha ⟨n - 1, by omega⟩ - 1)) := by
  have hcoord : ∀ i : Fin (n - 1),
      (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1) =
        (x i) ^ (alpha ⟨i.val, by omega⟩ - 1) *
          s ^ (alpha ⟨i.val, by omega⟩ - 1) := by
    intro i
    exact Real.mul_rpow (hx.1 i) hs.le
  have hlast :
      (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1) =
        (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1) *
          s ^ (alpha ⟨n - 1, by omega⟩ - 1) := by
    exact Real.mul_rpow hx.2 hs.le
  simp_rw [hcoord]
  rw [hlast]
  rw [Finset.prod_mul_distrib]
  ring

theorem gammaDirichlet_s_power_collapse
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (n - 1) *
        ((∏ i : Fin (n - 1), s ^ (alpha ⟨i.val, by omega⟩ - 1)) *
          s ^ (alpha ⟨n - 1, by omega⟩ - 1)) =
      s ^ ((∑ i : Fin n, alpha i) - 1) := by
  have hprod :
      (∏ i : Fin (n - 1), s ^ (alpha ⟨i.val, by omega⟩ - 1)) =
        s ^ ((∑ i : Fin (n - 1), alpha ⟨i.val, by omega⟩) -
          ((n - 1 : ℕ) : ℝ)) := by
    simpa using
      (Real.rpow_sum_of_pos (a := s) hs
        (f := fun i : Fin (n - 1) => alpha ⟨i.val, by omega⟩ - 1)
        Finset.univ).symm
  rw [hprod]
  rw [← Real.rpow_natCast s (n - 1)]
  rw [← Real.rpow_add hs]
  rw [← Real.rpow_add hs]
  congr 1
  have hsplit := fin_sum_projected_last hn alpha
  rw [hsplit]
  ring

theorem gammaDirichlet_exp_factor_collapse
    {n : ℕ} (x : Fin (n - 1) → ℝ) (beta s : ℝ) :
    (∏ i : Fin (n - 1), Real.exp (-(beta⁻¹ * (x i * s)))) *
        Real.exp (-(beta⁻¹ * (simplexLastCoord x * s))) =
      Real.exp (-(beta⁻¹ * s)) := by
  have hsum_mul :
      (∑ i : Fin (n - 1), beta⁻¹ * (x i * s)) =
        beta⁻¹ * ((∑ i : Fin (n - 1), x i) * s) := by
    simp [Finset.mul_sum, mul_assoc, mul_comm]
  have harg :
      (∑ i : Fin (n - 1), -(beta⁻¹ * (x i * s))) +
          -(beta⁻¹ * (simplexLastCoord x * s)) =
        -(beta⁻¹ * s) := by
    rw [Finset.sum_neg_distrib, hsum_mul]
    simp [simplexLastCoord]
    ring
  calc
    (∏ i : Fin (n - 1), Real.exp (-(beta⁻¹ * (x i * s)))) *
        Real.exp (-(beta⁻¹ * (simplexLastCoord x * s)))
        = Real.exp ((∑ i : Fin (n - 1), -(beta⁻¹ * (x i * s))) +
            -(beta⁻¹ * (simplexLastCoord x * s))) := by
          rw [← Real.exp_sum]
          rw [Real.exp_add]
    _ = Real.exp (-(beta⁻¹ * s)) := by rw [harg]

theorem normalizedGammaDirichletDensity_source_integral_on_simplex_expanded
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (n - 1) *
          (∏ i : Fin (n - 1),
            ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
                Real.Gamma (alpha ⟨i.val, by omega⟩) *
              (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1) *
              Real.exp (-(beta⁻¹ * (x i * s))))) *
          ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
              Real.Gamma (alpha ⟨n - 1, by omega⟩) *
            (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1) *
            Real.exp (-(beta⁻¹ * (simplexLastCoord x * s)))) := by
  rw [normalizedGammaDirichletDensity_source_integral hn]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hxcoord : ∀ i : Fin (n - 1), 0 ≤ x i * s :=
    fun i => mul_nonneg (hx.1 i) hs_nonneg
  have hxlast : 0 ≤ simplexLastCoord x * s := mul_nonneg hx.2 hs_nonneg
  simp [ProbabilityTheory.gammaPDFReal, hxcoord, hxlast]

theorem gammaDirichlet_integrand_expanded_exp_collapse
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (x : Fin (n - 1) → ℝ) (s : ℝ) :
    s ^ (n - 1) *
        (∏ i : Fin (n - 1),
          ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
              Real.Gamma (alpha ⟨i.val, by omega⟩) *
            (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1) *
            Real.exp (-(beta⁻¹ * (x i * s))))) *
        ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
            Real.Gamma (alpha ⟨n - 1, by omega⟩) *
          (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1) *
          Real.exp (-(beta⁻¹ * (simplexLastCoord x * s)))) =
      s ^ (n - 1) *
        (∏ i : Fin (n - 1),
          ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
              Real.Gamma (alpha ⟨i.val, by omega⟩) *
            (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
        ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
            Real.Gamma (alpha ⟨n - 1, by omega⟩) *
          (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1)) *
        Real.exp (-(beta⁻¹ * s)) := by
  let A : Fin (n - 1) → ℝ := fun i =>
    (beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
        Real.Gamma (alpha ⟨i.val, by omega⟩) *
      (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1)
  let E : Fin (n - 1) → ℝ := fun i => Real.exp (-(beta⁻¹ * (x i * s)))
  let L : ℝ :=
    (beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
        Real.Gamma (alpha ⟨n - 1, by omega⟩) *
      (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1)
  let EL : ℝ := Real.exp (-(beta⁻¹ * (simplexLastCoord x * s)))
  have hExp : (∏ i : Fin (n - 1), E i) * EL = Real.exp (-(beta⁻¹ * s)) := by
    simpa [E, EL] using gammaDirichlet_exp_factor_collapse x beta s
  change s ^ (n - 1) * (∏ i : Fin (n - 1), A i * E i) * (L * EL) =
    s ^ (n - 1) * (∏ i : Fin (n - 1), A i) * L * Real.exp (-(beta⁻¹ * s))
  rw [Finset.prod_mul_distrib]
  rw [← hExp]
  ring

theorem normalizedGammaDirichletDensity_source_integral_on_simplex_exp_collapsed
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (n - 1) *
          (∏ i : Fin (n - 1),
            ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
                Real.Gamma (alpha ⟨i.val, by omega⟩) *
              (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
          ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
              Real.Gamma (alpha ⟨n - 1, by omega⟩) *
            (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1)) *
          Real.exp (-(beta⁻¹ * s)) := by
  rw [normalizedGammaDirichletDensity_source_integral_on_simplex_expanded hn hx]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ =>
    gammaDirichlet_integrand_expanded_exp_collapse hn alpha beta x s

theorem gammaDirichlet_integrand_as_gamma_kernel
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) {s : ℝ} (hs : 0 < s) :
    s ^ (n - 1) *
        (∏ i : Fin (n - 1),
          ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
              Real.Gamma (alpha ⟨i.val, by omega⟩) *
            (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
        ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
            Real.Gamma (alpha ⟨n - 1, by omega⟩) *
          (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1)) *
        Real.exp (-(beta⁻¹ * s)) =
      ((∏ i : Fin (n - 1),
          ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
              Real.Gamma (alpha ⟨i.val, by omega⟩) *
            (x i) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
        ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
            Real.Gamma (alpha ⟨n - 1, by omega⟩) *
          (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1))) *
        s ^ ((∑ i : Fin n, alpha i) - 1) *
        Real.exp (-(beta⁻¹ * s)) := by
  let C : Fin (n - 1) → ℝ := fun i =>
    (beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
      Real.Gamma (alpha ⟨i.val, by omega⟩)
  let P : Fin (n - 1) → ℝ := fun i =>
    (x i * s) ^ (alpha ⟨i.val, by omega⟩ - 1)
  let Xp : Fin (n - 1) → ℝ := fun i =>
    (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)
  let Sp : Fin (n - 1) → ℝ := fun i =>
    s ^ (alpha ⟨i.val, by omega⟩ - 1)
  let CL : ℝ :=
    (beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
      Real.Gamma (alpha ⟨n - 1, by omega⟩)
  let PL : ℝ :=
    (simplexLastCoord x * s) ^ (alpha ⟨n - 1, by omega⟩ - 1)
  let XL : ℝ :=
    (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1)
  let SL : ℝ := s ^ (alpha ⟨n - 1, by omega⟩ - 1)
  let Exp : ℝ := Real.exp (-(beta⁻¹ * s))
  have hP : (∏ i : Fin (n - 1), P i) * PL =
      (∏ i : Fin (n - 1), Xp i) * XL * ((∏ i : Fin (n - 1), Sp i) * SL) := by
    simpa [P, Xp, Sp, PL, XL, SL] using
      gammaDirichlet_projected_power_s_split hn alpha hx hs
  have hS : s ^ (n - 1) * ((∏ i : Fin (n - 1), Sp i) * SL) =
      s ^ ((∑ i : Fin n, alpha i) - 1) := by
    simpa [Sp, SL] using gammaDirichlet_s_power_collapse hn alpha hs
  change s ^ (n - 1) * (∏ i : Fin (n - 1), C i * P i) * (CL * PL) * Exp =
    ((∏ i : Fin (n - 1), C i * Xp i) * (CL * XL)) *
      s ^ ((∑ i : Fin n, alpha i) - 1) * Exp
  rw [Finset.prod_mul_distrib]
  calc
    s ^ (n - 1) * ((∏ i : Fin (n - 1), C i) * ∏ i : Fin (n - 1), P i) *
        (CL * PL) * Exp =
        ((∏ i : Fin (n - 1), C i) * CL) *
          (s ^ (n - 1) * ((∏ i : Fin (n - 1), P i) * PL)) * Exp := by
      ring
    _ = ((∏ i : Fin (n - 1), C i) * CL) *
          (s ^ (n - 1) *
            (((∏ i : Fin (n - 1), Xp i) * XL) *
              ((∏ i : Fin (n - 1), Sp i) * SL))) * Exp := by
      rw [hP]
    _ = ((∏ i : Fin (n - 1), C i) * CL) *
          (((∏ i : Fin (n - 1), Xp i) * XL) *
            (s ^ (n - 1) * ((∏ i : Fin (n - 1), Sp i) * SL))) * Exp := by
      ring
    _ = ((∏ i : Fin (n - 1), C i) * CL) *
          (((∏ i : Fin (n - 1), Xp i) * XL) *
            s ^ ((∑ i : Fin n, alpha i) - 1)) * Exp := by
      rw [hS]
    _ = ((∏ i : Fin (n - 1), C i * Xp i) * (CL * XL)) *
          s ^ ((∑ i : Fin n, alpha i) - 1) * Exp := by
      rw [Finset.prod_mul_distrib]
      ring

theorem normalizedGammaDirichletDensity_source_integral_on_simplex_gamma_kernel
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x =
      ∫ s in Set.Ioi (0 : ℝ),
        ((∏ i : Fin (n - 1),
            ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
                Real.Gamma (alpha ⟨i.val, by omega⟩) *
              (x i) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
          ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
              Real.Gamma (alpha ⟨n - 1, by omega⟩) *
            (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1))) *
          s ^ ((∑ i : Fin n, alpha i) - 1) *
          Real.exp (-(beta⁻¹ * s)) := by
  rw [normalizedGammaDirichletDensity_source_integral_on_simplex_exp_collapsed hn hx]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    gammaDirichlet_integrand_as_gamma_kernel hn alpha beta hx hs

theorem gammaDirichlet_totalMass_gamma_kernel_integral
    {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    (∫ s in Set.Ioi (0 : ℝ),
        s ^ (a - 1) * Real.exp (-(beta⁻¹ * s))) =
      beta ^ a * Real.Gamma a := by
  have hrate : 0 < beta⁻¹ := inv_pos.mpr hbeta
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrate]
  have hdiv : 1 / beta⁻¹ = beta := by
    field_simp [ne_of_gt hbeta]
  rw [hdiv]

theorem gammaDirichlet_rate_power_projected_last
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) {beta : ℝ}
    (hbeta : 0 < beta) :
    (∏ i : Fin (n - 1), (beta⁻¹) ^ (alpha ⟨i.val, by omega⟩)) *
        (beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) =
      (beta⁻¹) ^ (∑ i : Fin n, alpha i) := by
  have hrate : 0 < beta⁻¹ := inv_pos.mpr hbeta
  have hprod :
      (∏ i : Fin (n - 1), (beta⁻¹) ^ (alpha ⟨i.val, by omega⟩)) =
        (beta⁻¹) ^ (∑ i : Fin (n - 1), alpha ⟨i.val, by omega⟩) := by
    simpa using
      (Real.rpow_sum_of_pos (a := beta⁻¹) hrate
        (f := fun i : Fin (n - 1) => alpha ⟨i.val, by omega⟩)
        Finset.univ).symm
  rw [hprod, ← Real.rpow_add hrate]
  rw [fin_sum_projected_last hn alpha]

theorem gammaDirichlet_rate_scale_cancel {a beta : ℝ} (hbeta : 0 < beta) :
    (beta⁻¹) ^ a * beta ^ a = 1 := by
  rw [Real.inv_rpow hbeta.le]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hbeta a).ne'

theorem gammaDirichlet_gamma_projected_last
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) :
    (∏ i : Fin (n - 1), Real.Gamma (alpha ⟨i.val, by omega⟩)) *
        Real.Gamma (alpha ⟨n - 1, by omega⟩) =
      ∏ i : Fin n, Real.Gamma (alpha i) := by
  exact (fin_prod_projected_last hn fun i : Fin n => Real.Gamma (alpha i)).symm

theorem gammaDirichlet_kernel_constant_collapse
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    (x : Fin (n - 1) → ℝ) :
    ((∏ i : Fin (n - 1),
          ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
              Real.Gamma (alpha ⟨i.val, by omega⟩) *
            (x i) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
        ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
            Real.Gamma (alpha ⟨n - 1, by omega⟩) *
          (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1))) *
        (beta ^ (∑ i : Fin n, alpha i) *
          Real.Gamma (∑ i : Fin n, alpha i)) =
      dirichletNormalizer alpha *
        (∏ i : Fin (n - 1), (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
        (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1) := by
  let R : Fin (n - 1) → ℝ := fun i => (beta⁻¹) ^ (alpha ⟨i.val, by omega⟩)
  let Gm : Fin (n - 1) → ℝ := fun i => Real.Gamma (alpha ⟨i.val, by omega⟩)
  let Xp : Fin (n - 1) → ℝ := fun i => (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)
  let RL : ℝ := (beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩)
  let GLast : ℝ := Real.Gamma (alpha ⟨n - 1, by omega⟩)
  let XL : ℝ := (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1)
  have hRG :
      (∏ i : Fin (n - 1), (R i / (Gm i))) * (RL / GLast) =
        (beta⁻¹) ^ (∑ i : Fin n, alpha i) /
          (∏ i : Fin n, Real.Gamma (alpha i)) := by
    rw [Finset.prod_div_distrib]
    rw [div_mul_div_comm]
    rw [gammaDirichlet_rate_power_projected_last hn alpha hbeta]
    rw [gammaDirichlet_gamma_projected_last hn alpha]
  have hnonzero_prod : (∏ i : Fin n, Real.Gamma (alpha i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      (Real.Gamma_pos_of_pos (halpha i)).ne'
  change
    ((∏ i : Fin (n - 1), ((R i / (Gm i)) * Xp i)) *
        ((RL / GLast) * XL)) *
        (beta ^ (∑ i : Fin n, alpha i) *
          Real.Gamma (∑ i : Fin n, alpha i)) =
      dirichletNormalizer alpha * (∏ i : Fin (n - 1), Xp i) * XL
  rw [Finset.prod_mul_distrib]
  calc
    (((∏ i : Fin (n - 1), (R i / (Gm i))) *
          (∏ i : Fin (n - 1), Xp i)) *
        ((RL / GLast) * XL)) *
        (beta ^ (∑ i : Fin n, alpha i) *
          Real.Gamma (∑ i : Fin n, alpha i)) =
        (((∏ i : Fin (n - 1), (R i / (Gm i))) * (RL / GLast)) *
          (beta ^ (∑ i : Fin n, alpha i) *
            Real.Gamma (∑ i : Fin n, alpha i))) *
          ((∏ i : Fin (n - 1), Xp i) * XL) := by
      ring
    _ =
        (((beta⁻¹) ^ (∑ i : Fin n, alpha i) /
            (∏ i : Fin n, Real.Gamma (alpha i))) *
          (beta ^ (∑ i : Fin n, alpha i) *
            Real.Gamma (∑ i : Fin n, alpha i))) *
          ((∏ i : Fin (n - 1), Xp i) * XL) := by
      rw [hRG]
    _ =
        (dirichletNormalizer alpha *
          ((∏ i : Fin (n - 1), Xp i) * XL)) := by
      rw [dirichletNormalizer]
      have hcancel :
          (beta⁻¹) ^ (∑ i : Fin n, alpha i) *
              beta ^ (∑ i : Fin n, alpha i) = 1 :=
        gammaDirichlet_rate_scale_cancel (a := ∑ i : Fin n, alpha i) hbeta
      have hcancel' :
          (1 / beta) ^ (∑ i : Fin n, alpha i) *
              beta ^ (∑ i : Fin n, alpha i) = 1 := by
        simpa [one_div] using hcancel
      field_simp [hnonzero_prod]
      rw [hcancel']
      ring
    _ = dirichletNormalizer alpha * (∏ i : Fin (n - 1), Xp i) * XL := by
      ring

theorem normalizedGammaDirichletDensity_eq_DirichletPDF_on_simplex
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    {x : Fin (n - 1) → ℝ} (hx : DirichletSimplex x) :
    normalizedGammaDirichletDensity alpha beta x = DirichletPDF alpha x := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, by simp⟩
  have hsum_pos : 0 < ∑ i : Fin n, alpha i :=
    Finset.sum_pos (fun i _ => halpha i) hnonempty
  rw [normalizedGammaDirichletDensity_source_integral_on_simplex_gamma_kernel hn hx]
  rw [DirichletPDF_formula_on_simplex hn hx]
  let K : ℝ :=
    (∏ i : Fin (n - 1),
        ((beta⁻¹) ^ (alpha ⟨i.val, by omega⟩) /
            Real.Gamma (alpha ⟨i.val, by omega⟩) *
          (x i) ^ (alpha ⟨i.val, by omega⟩ - 1))) *
      ((beta⁻¹) ^ (alpha ⟨n - 1, by omega⟩) /
          Real.Gamma (alpha ⟨n - 1, by omega⟩) *
        (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1))
  calc
    (∫ s in Set.Ioi (0 : ℝ),
        K * s ^ ((∑ i : Fin n, alpha i) - 1) *
          Real.exp (-(beta⁻¹ * s))) =
        ∫ s in Set.Ioi (0 : ℝ),
          K * (s ^ ((∑ i : Fin n, alpha i) - 1) *
            Real.exp (-(beta⁻¹ * s))) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring
    _ =
        K *
          ∫ s in Set.Ioi (0 : ℝ),
            s ^ ((∑ i : Fin n, alpha i) - 1) *
              Real.exp (-(beta⁻¹ * s)) := by
      rw [MeasureTheory.integral_const_mul]
    _ =
        K *
          (beta ^ (∑ i : Fin n, alpha i) *
            Real.Gamma (∑ i : Fin n, alpha i)) := by
      rw [gammaDirichlet_totalMass_gamma_kernel_integral hsum_pos hbeta]
    _ =
        dirichletNormalizer alpha *
          (∏ i : Fin (n - 1), (x i) ^ (alpha ⟨i.val, by omega⟩ - 1)) *
          (simplexLastCoord x) ^ (alpha ⟨n - 1, by omega⟩ - 1) := by
      simpa [K] using
        gammaDirichlet_kernel_constant_collapse hn alpha halpha hbeta x

/--
The reusable change-of-variables/Jacobian bridge still needed for the projected
law: the projected pushforward measure should have the source total-mass
integral as a setwise density. This separates the measure-theoretic Jacobian
step from the later one-dimensional Gamma integral evaluation.
-/
def ProjectedDirichletJacobianBridge {n : ℕ}
    (alpha : Fin n → ℝ) (beta : ℝ) : Prop :=
  ∀ s : Set (Fin (n - 1) → ℝ), MeasurableSet s →
    ProjectedDirichletLaw alpha beta s =
      ∫⁻ x in s, ENNReal.ofReal (normalizedGammaDirichletDensity alpha beta x)

theorem ProjectedDirichletJacobianBridge_of_positive
    {n : ℕ} (hn : 0 < n) {alpha : Fin n → ℝ} {beta : ℝ}
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ProjectedDirichletJacobianBridge alpha beta := by
  intro s hs
  rw [ProjectedDirichletLaw_eq_lintegral_gammaProductPDFReal_projectedSimplexTotalMap_image
    hn halpha hbeta hs]
  exact
    projectedSimplexTotalMap_image_lintegral_gammaProductPDFReal_eq_lintegral_normalizedGammaDirichletDensity_setwise
      hn halpha hbeta hs

/--
The reusable integral-evaluation bridge still needed after the Jacobian step:
the source total-mass integral should simplify to the displayed Dirichlet
density, including the zero value off the projected simplex.
-/
def NormalizedGammaIntegralBridge {n : ℕ}
    (alpha : Fin n → ℝ) (beta : ℝ) : Prop :=
  ∀ x : Fin (n - 1) → ℝ,
    normalizedGammaDirichletDensity alpha beta x = DirichletPDF alpha x

theorem NormalizedGammaIntegralBridge_of_on_simplex
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (hOnSimplex : ∀ x : Fin (n - 1) → ℝ, DirichletSimplex x →
      normalizedGammaDirichletDensity alpha beta x = DirichletPDF alpha x) :
    NormalizedGammaIntegralBridge alpha beta := by
  intro x
  by_cases hx : DirichletSimplex x
  · exact hOnSimplex x hx
  · exact normalizedGammaDirichletDensity_eq_DirichletPDF_off_simplex hn alpha beta hx

theorem NormalizedGammaIntegralBridge_of_positive
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    NormalizedGammaIntegralBridge alpha beta := by
  exact NormalizedGammaIntegralBridge_of_on_simplex hn alpha beta fun x hx =>
    normalizedGammaDirichletDensity_eq_DirichletPDF_on_simplex hn halpha hbeta hx

theorem ProjectedDirichletLaw_eq_withDensity_DirichletPDF_of_bridges
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ)
    (hJacobian : ProjectedDirichletJacobianBridge alpha beta)
    (hIntegral : NormalizedGammaIntegralBridge alpha beta) :
    ProjectedDirichletLaw alpha beta =
      (volume : Measure (Fin (n - 1) → ℝ)).withDensity
        (fun x => ENNReal.ofReal (DirichletPDF alpha x)) := by
  ext s hs
  rw [withDensity_apply _ hs, hJacobian s hs]
  exact setLIntegral_congr_fun hs fun x _ => by
    rw [hIntegral x]

theorem ProjectedDirichletLaw_eq_withDensity_DirichletPDF_of_jacobian_positive
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta)
    (hJacobian : ProjectedDirichletJacobianBridge alpha beta) :
    ProjectedDirichletLaw alpha beta =
      (volume : Measure (Fin (n - 1) → ℝ)).withDensity
        (fun x => ENNReal.ofReal (DirichletPDF alpha x)) := by
  exact ProjectedDirichletLaw_eq_withDensity_DirichletPDF_of_bridges alpha beta
    hJacobian (NormalizedGammaIntegralBridge_of_positive hn alpha beta halpha hbeta)

theorem ProjectedDirichletLaw_eq_withDensity_DirichletPDF_positive
    {n : ℕ} (hn : 0 < n) (alpha : Fin n → ℝ) (beta : ℝ)
    (halpha : ∀ i, 0 < alpha i) (hbeta : 0 < beta) :
    ProjectedDirichletLaw alpha beta =
      (volume : Measure (Fin (n - 1) → ℝ)).withDensity
        (fun x => ENNReal.ofReal (DirichletPDF alpha x)) := by
  exact ProjectedDirichletLaw_eq_withDensity_DirichletPDF_of_jacobian_positive
    hn alpha beta halpha hbeta
    (ProjectedDirichletJacobianBridge_of_positive hn halpha hbeta)
