import ToyApollo.Support.DirichletGammaSimplexChart

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

noncomputable section

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
