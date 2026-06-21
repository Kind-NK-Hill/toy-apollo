import ToyApollo.Output.prob_14_8_montel_support
import ToyApollo.Output.chapter14_mgf_support

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Uniformity

noncomputable section

/-- The moment generating function of a law on `ℝ`, using the same Mathlib
`mgf` primitive as Definition 9.2. -/
def prob_14_8_mgfOfLaw (P : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  chapter14_mgfOfLaw P t

/-- The law characteristic function is the complex MGF of the identity random
variable on the imaginary axis. -/
theorem prob_14_8_characteristic_eq_complexMGF
    (P : ProbabilityMeasure ℝ) (t : ℝ) :
    thm_14_1_characteristicFunction P t =
      complexMGF (fun x : ℝ => x) (P : Measure ℝ) (t * Complex.I) := by
  exact chapter14_characteristic_eq_complexMGF P t

/-- The textbook assumption that the MGF is finite on the closed interval
`[-δ,δ]`. -/
def prob_14_8_mgfDefinedOn
    (P : ProbabilityMeasure ℝ) (δ : ℝ) : Prop :=
  chapter14_mgfDefinedOn P δ

/-- Source-level setup for Problem 14.8.

This child obligation only exposes the MGF hypotheses needed for tightness. -/
structure prob_14_8_MgfConvergenceSetup where
  laws : ℕ → ProbabilityMeasure ℝ
  targetLaw : ProbabilityMeasure ℝ
  δ : ℝ
  δ_pos : 0 < δ
  mgf_defined :
    ∀ n : ℕ, prob_14_8_mgfDefinedOn (laws n) δ
  target_mgf_defined :
    prob_14_8_mgfDefinedOn targetLaw δ
  mgf_converges :
    ∀ t : ℝ, t ∈ Icc (-δ) δ →
      Tendsto (fun n : ℕ => prob_14_8_mgfOfLaw (laws n) t) atTop
        (𝓝 (prob_14_8_mgfOfLaw targetLaw t))

/-- On the real axis, the MGF convergence hypothesis is exactly convergence of
the complex MGF after coercing real points into `ℂ`. -/
theorem prob_14_8_real_axis_complexMGF_convergence_at
    (S : prob_14_8_MgfConvergenceSetup) {t : ℝ}
    (ht : t ∈ Icc (-S.δ) S.δ) :
    Tendsto
      (fun n : ℕ => complexMGF (fun x : ℝ => x) (S.laws n : Measure ℝ) (t : ℂ))
      atTop
      (𝓝 (complexMGF (fun x : ℝ => x) (S.targetLaw : Measure ℝ) (t : ℂ))) := by
  have hReal :
      Tendsto (fun n : ℕ => prob_14_8_mgfOfLaw (S.laws n) t) atTop
        (𝓝 (prob_14_8_mgfOfLaw S.targetLaw t)) :=
    S.mgf_converges t ht
  exact
    chapter14_real_axis_complexMGF_convergence_at S.laws S.targetLaw
      (by simpa [prob_14_8_mgfOfLaw] using hReal)

/-- The closed interval MGF-defined hypothesis gives interior real-domain
facts for the real MGF integrability set. -/
theorem prob_14_8_mgf_defined_interval_to_strip_domain
    (S : prob_14_8_MgfConvergenceSetup) :
    (∀ n : ℕ, ∀ t : ℝ, -S.δ < t → t < S.δ →
      t ∈ interior (integrableExpSet id (S.laws n : Measure ℝ))) ∧
    (∀ t : ℝ, -S.δ < t → t < S.δ →
      t ∈ interior (integrableExpSet id (S.targetLaw : Measure ℝ))) := by
  constructor
  · intro n t ht_left ht_right
    rw [mem_interior]
    refine ⟨Set.Ioo (-S.δ) S.δ, ?_, isOpen_Ioo, ⟨ht_left, ht_right⟩⟩
    intro u hu
    have huIcc : u ∈ Set.Icc (-S.δ) S.δ :=
      ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    simpa [integrableExpSet, id_eq] using S.mgf_defined n u huIcc
  · intro t ht_left ht_right
    rw [mem_interior]
    refine ⟨Set.Ioo (-S.δ) S.δ, ?_, isOpen_Ioo, ⟨ht_left, ht_right⟩⟩
    intro u hu
    have huIcc : u ∈ Set.Icc (-S.δ) S.δ :=
      ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    simpa [integrableExpSet, id_eq] using S.target_mgf_defined u huIcc

/-- The common vertical strip on which all complex MGFs are analytic. -/
def prob_14_8_complexMGFStrip
    (S : prob_14_8_MgfConvergenceSetup) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Ioo (-S.δ) S.δ}

/-- The common complex-MGF strip is open. -/
theorem prob_14_8_complexMGFStrip_isOpen
    (S : prob_14_8_MgfConvergenceSetup) :
    IsOpen (prob_14_8_complexMGFStrip S) := by
  simpa [prob_14_8_complexMGFStrip] using
    (isOpen_Ioo.preimage Complex.continuous_re)

/-- The common complex-MGF strip is preconnected because it is convex. -/
theorem prob_14_8_complexMGFStrip_isPreconnected
    (S : prob_14_8_MgfConvergenceSetup) :
    IsPreconnected (prob_14_8_complexMGFStrip S) := by
  have hconv : Convex ℝ (prob_14_8_complexMGFStrip S) := by
    have hleft : Convex ℝ {z : ℂ | -S.δ < z.re} :=
      convex_halfSpace_re_gt (-S.δ)
    have hright : Convex ℝ {z : ℂ | z.re < S.δ} :=
      convex_halfSpace_re_lt S.δ
    simpa [prob_14_8_complexMGFStrip] using hleft.inter hright
  exact hconv.isPreconnected

/-- Zero belongs to the common complex-MGF strip. -/
theorem prob_14_8_zero_mem_complexMGFStrip
    (S : prob_14_8_MgfConvergenceSetup) :
    (0 : ℂ) ∈ prob_14_8_complexMGFStrip S := by
  simpa [prob_14_8_complexMGFStrip] using S.δ_pos

/-- The imaginary axis belongs to the common complex-MGF strip. -/
theorem prob_14_8_imaginary_axis_mem_complexMGFStrip
    (S : prob_14_8_MgfConvergenceSetup) (t : ℝ) :
    t * Complex.I ∈ prob_14_8_complexMGFStrip S := by
  simpa [prob_14_8_complexMGFStrip] using S.δ_pos

/-- Any compact subset of the common vertical strip is contained in a smaller
closed vertical substrip `|re z| ≤ eta` with `eta < δ`. -/
theorem prob_14_8_compact_subset_strip_subset_substrip
    (S : prob_14_8_MgfConvergenceSetup) {K : Set ℂ}
    (hK : IsCompact K)
    (hKU : K ⊆ prob_14_8_complexMGFStrip S) :
    ∃ eta : ℝ, 0 < eta ∧ eta < S.δ ∧ ∀ z ∈ K, |z.re| ≤ eta := by
  by_cases hne : K.Nonempty
  · let f : ℂ → ℝ := fun z => |z.re|
    have hf : ContinuousOn f K := by fun_prop
    rcases hK.exists_isMaxOn hne hf with ⟨z0, hz0, hmax⟩
    have hzstrip : z0.re ∈ Set.Ioo (-S.δ) S.δ := hKU hz0
    have hzabs : |z0.re| < S.δ := abs_lt.mpr hzstrip
    refine ⟨(|z0.re| + S.δ) / 2, ?_, ?_, ?_⟩
    · nlinarith [abs_nonneg z0.re, S.δ_pos]
    · nlinarith
    · intro z hz
      have hzle : f z ≤ f z0 := hmax hz
      dsimp [f] at hzle
      nlinarith
  · refine ⟨S.δ / 2, half_pos S.δ_pos, half_lt_self S.δ_pos, ?_⟩
    intro z hz
    exact False.elim (hne ⟨z, hz⟩)

/-- MGF-definedness on `[-δ,δ]` gives analyticity of every sequence complex
MGF and the target complex MGF on the common open vertical strip. -/
theorem prob_14_8_complexMGF_analytic_on_common_strip
    (S : prob_14_8_MgfConvergenceSetup) :
    (∀ n : ℕ,
      AnalyticOnNhd ℂ
        (fun z : ℂ => complexMGF id (S.laws n : Measure ℝ) z)
        (prob_14_8_complexMGFStrip S)) ∧
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexMGF id (S.targetLaw : Measure ℝ) z)
      (prob_14_8_complexMGFStrip S) := by
  have hdomain := prob_14_8_mgf_defined_interval_to_strip_domain S
  constructor
  · intro n
    exact (analyticOnNhd_complexMGF
      (X := id) (μ := (S.laws n : Measure ℝ))).mono (by
        intro z hz
        exact hdomain.1 n z.re hz.1 hz.2)
  · exact (analyticOnNhd_complexMGF
      (X := id) (μ := (S.targetLaw : Measure ℝ))).mono (by
        intro z hz
        exact hdomain.2 z.re hz.1 hz.2)

theorem prob_14_8_exp_mul_le_endpoint_sum {eta r x : ℝ}
    (hr : |r| ≤ eta) :
    Real.exp (r * x) ≤ Real.exp (eta * x) + Real.exp ((-eta) * x) := by
  by_cases hx : 0 ≤ x
  · have hr_le : r ≤ eta := (le_abs_self r).trans hr
    have hmul : r * x ≤ eta * x := mul_le_mul_of_nonneg_right hr_le hx
    exact (Real.exp_le_exp.mpr hmul).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hx_nonpos : x ≤ 0 := le_of_not_ge hx
    have hneg_le : -eta ≤ r := by
      have h : -r ≤ eta := (neg_le_abs r).trans hr
      linarith
    have hmul : r * x ≤ (-eta) * x :=
      mul_le_mul_of_nonpos_right hneg_le hx_nonpos
    exact (Real.exp_le_exp.mpr hmul).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

theorem prob_14_8_mgf_re_le_endpoint_mgfs
    (P : ProbabilityMeasure ℝ) {eta r : ℝ}
    (hpos : Integrable (fun x : ℝ => Real.exp (eta * x)) (P : Measure ℝ))
    (hneg : Integrable (fun x : ℝ => Real.exp ((-eta) * x)) (P : Measure ℝ))
    (hr : |r| ≤ eta) :
    mgf id (P : Measure ℝ) r ≤
      mgf id (P : Measure ℝ) eta + mgf id (P : Measure ℝ) (-eta) := by
  have hr_le : r ≤ eta := (le_abs_self r).trans hr
  have hneg_le : -eta ≤ r := by
    have h : -r ≤ eta := (neg_le_abs r).trans hr
    linarith
  have hr_int : Integrable (fun x : ℝ => Real.exp (r * x)) (P : Measure ℝ) :=
    integrable_exp_mul_of_le_of_le (X := id) (μ := (P : Measure ℝ))
      (a := -eta) (b := eta) hneg hpos hneg_le hr_le
  have hsum_int :
      Integrable (fun x : ℝ =>
        Real.exp (eta * x) + Real.exp ((-eta) * x)) (P : Measure ℝ) := by
    simpa [Pi.add_apply] using hpos.add hneg
  have hmono :
      (∫ x : ℝ, Real.exp (r * x) ∂(P : Measure ℝ)) ≤
        ∫ x : ℝ, Real.exp (eta * x) + Real.exp ((-eta) * x) ∂(P : Measure ℝ) := by
    exact MeasureTheory.integral_mono hr_int hsum_int
      (fun x =>
        prob_14_8_exp_mul_le_endpoint_sum (eta := eta) (r := r) (x := x) hr)
  have hadd :
      (∫ x : ℝ, Real.exp (eta * x) + Real.exp ((-eta) * x) ∂(P : Measure ℝ)) =
        (∫ x : ℝ, Real.exp (eta * x) ∂(P : Measure ℝ)) +
          ∫ x : ℝ, Real.exp ((-eta) * x) ∂(P : Measure ℝ) :=
    MeasureTheory.integral_add hpos hneg
  rw [hadd] at hmono
  simpa [mgf, id_eq] using hmono

theorem prob_14_8_complexMGF_norm_le_endpoint_mgfs
    (P : ProbabilityMeasure ℝ) {eta : ℝ}
    (_heta_nonneg : 0 ≤ eta)
    (hpos : Integrable (fun x : ℝ => Real.exp (eta * x)) (P : Measure ℝ))
    (hneg : Integrable (fun x : ℝ => Real.exp ((-eta) * x)) (P : Measure ℝ)) :
    ∀ z : ℂ, |z.re| ≤ eta →
      ‖complexMGF id (P : Measure ℝ) z‖ ≤
        mgf id (P : Measure ℝ) eta + mgf id (P : Measure ℝ) (-eta) := by
  intro z hz
  exact (norm_complexMGF_le_mgf (X := id) (μ := (P : Measure ℝ)) (z := z)).trans
    (prob_14_8_mgf_re_le_endpoint_mgfs P hpos hneg hz)

theorem prob_14_8_target_complexMGF_substrip_bound
    (S : prob_14_8_MgfConvergenceSetup) {eta : ℝ}
    (heta_pos : 0 < eta) (heta_delta : eta < S.δ) :
    ∃ C : ℝ, ∀ z : ℂ, |z.re| ≤ eta →
      ‖complexMGF id (S.targetLaw : Measure ℝ) z‖ ≤ C := by
  have heta_mem : eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  have hneg_eta_mem : -eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  refine ⟨mgf id (S.targetLaw : Measure ℝ) eta +
      mgf id (S.targetLaw : Measure ℝ) (-eta), ?_⟩
  intro z hz
  exact prob_14_8_complexMGF_norm_le_endpoint_mgfs
    S.targetLaw
    (le_of_lt heta_pos)
    (S.target_mgf_defined eta heta_mem)
    (S.target_mgf_defined (-eta) hneg_eta_mem)
    z hz

theorem prob_14_8_eventual_sequence_complexMGF_substrip_bound
    (S : prob_14_8_MgfConvergenceSetup) {eta : ℝ}
    (heta_pos : 0 < eta) (heta_delta : eta < S.δ) :
    ∃ N : ℕ, ∃ C : ℝ, ∀ n : ℕ, N ≤ n →
      ∀ z : ℂ, |z.re| ≤ eta →
        ‖complexMGF id (S.laws n : Measure ℝ) z‖ ≤ C := by
  have heta_mem : eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  have hneg_eta_mem : -eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  let Bpos : ℝ := mgf id (S.targetLaw : Measure ℝ) eta + 1
  let Bneg : ℝ := mgf id (S.targetLaw : Measure ℝ) (-eta) + 1
  have hpos_event :
      ∀ᶠ n : ℕ in atTop, mgf id (S.laws n : Measure ℝ) eta < Bpos := by
    exact (S.mgf_converges eta heta_mem).eventually_lt_const (by
      dsimp [Bpos, prob_14_8_mgfOfLaw]
      change
        mgf (fun x : ℝ => x) (S.targetLaw : Measure ℝ) eta <
          mgf (fun x : ℝ => x) (S.targetLaw : Measure ℝ) eta + 1
      exact lt_add_one _)
  have hneg_event :
      ∀ᶠ n : ℕ in atTop, mgf id (S.laws n : Measure ℝ) (-eta) < Bneg := by
    exact (S.mgf_converges (-eta) hneg_eta_mem).eventually_lt_const (by
      dsimp [Bneg, prob_14_8_mgfOfLaw]
      change
        mgf (fun x : ℝ => x) (S.targetLaw : Measure ℝ) (-eta) <
          mgf (fun x : ℝ => x) (S.targetLaw : Measure ℝ) (-eta) + 1
      exact lt_add_one _)
  rcases (eventually_atTop.1 (hpos_event.and hneg_event)) with ⟨N, hN⟩
  refine ⟨N, Bpos + Bneg, ?_⟩
  intro n hn z hz
  have hbounds := hN n hn
  have hendpoint :
      ‖complexMGF id (S.laws n : Measure ℝ) z‖ ≤
        mgf id (S.laws n : Measure ℝ) eta +
          mgf id (S.laws n : Measure ℝ) (-eta) :=
    prob_14_8_complexMGF_norm_le_endpoint_mgfs
      (S.laws n) (le_of_lt heta_pos)
      (S.mgf_defined n eta heta_mem)
      (S.mgf_defined n (-eta) hneg_eta_mem)
      z hz
  exact hendpoint.trans (add_le_add (le_of_lt hbounds.1) (le_of_lt hbounds.2))

theorem prob_14_8_finite_prefix_complexMGF_substrip_bound
    (S : prob_14_8_MgfConvergenceSetup) {eta : ℝ}
    (heta_pos : 0 < eta) (heta_delta : eta < S.δ) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ n : ℕ, n < N →
      ∀ z : ℂ, |z.re| ≤ eta →
        ‖complexMGF id (S.laws n : Measure ℝ) z‖ ≤ C := by
  have heta_mem : eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  have hneg_eta_mem : -eta ∈ Set.Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos, heta_pos, heta_delta]
  intro N
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro n hn
      exact (Nat.not_lt_zero n hn).elim
  | succ N ih =>
      rcases ih with ⟨C, hC⟩
      let CN : ℝ :=
        mgf id (S.laws N : Measure ℝ) eta +
          mgf id (S.laws N : Measure ℝ) (-eta)
      have hNbound :
          ∀ z : ℂ, |z.re| ≤ eta →
            ‖complexMGF id (S.laws N : Measure ℝ) z‖ ≤ CN := by
        intro z hz
        dsimp [CN]
        exact prob_14_8_complexMGF_norm_le_endpoint_mgfs
          (S.laws N) (le_of_lt heta_pos)
          (S.mgf_defined N eta heta_mem)
          (S.mgf_defined N (-eta) hneg_eta_mem)
          z hz
      refine ⟨max C CN, ?_⟩
      intro n hn z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hnlt | rfl
      · exact (hC n hnlt z hz).trans (le_max_left C CN)
      · exact (hNbound z hz).trans (le_max_right C CN)

/-- Source-facing uniform boundedness statement on each smaller vertical
substrip. -/
def prob_14_8_uniformComplexMGFSubstripBound
    (S : prob_14_8_MgfConvergenceSetup) : Prop :=
  ∀ eta : ℝ, 0 < eta → eta < S.δ →
    ∃ C : ℝ,
      (∀ z : ℂ, |z.re| ≤ eta →
        ‖complexMGF id (S.targetLaw : Measure ℝ) z‖ ≤ C) ∧
      (∀ n : ℕ, ∀ z : ℂ, |z.re| ≤ eta →
        ‖complexMGF id (S.laws n : Measure ℝ) z‖ ≤ C)

/-- Assemble the target-law, eventual-tail, and finite-prefix bounds into a
single uniform substrip bound. -/
theorem prob_14_8_uniform_strip_bounds
    (S : prob_14_8_MgfConvergenceSetup) :
    prob_14_8_uniformComplexMGFSubstripBound S := by
  intro eta heta_pos heta_delta
  rcases prob_14_8_target_complexMGF_substrip_bound S heta_pos heta_delta with
    ⟨Ct, hCt⟩
  rcases prob_14_8_eventual_sequence_complexMGF_substrip_bound S heta_pos heta_delta with
    ⟨N, ⟨Ctail, hTail⟩⟩
  rcases prob_14_8_finite_prefix_complexMGF_substrip_bound S heta_pos heta_delta N with
    ⟨Cprefix, hPrefix⟩
  refine ⟨max Ct (max Ctail Cprefix), ?_, ?_⟩
  · intro z hz
    exact (hCt z hz).trans (le_max_left Ct (max Ctail Cprefix))
  · intro n z hz
    by_cases hn : N ≤ n
    · exact (hTail n hn z hz).trans
        ((le_max_left Ctail Cprefix).trans
          (le_max_right Ct (max Ctail Cprefix)))
    · have hnlt : n < N := Nat.lt_of_not_ge hn
      exact (hPrefix n hnlt z hz).trans
        ((le_max_right Ctail Cprefix).trans
          (le_max_right Ct (max Ctail Cprefix)))

/-- Compact-facing bound adapter for the Vitali/Montel route: every compact
subset of the common strip has a single complex-MGF bound for the target and
the whole sequence. -/
theorem prob_14_8_uniformComplexMGFCompactBound
    (S : prob_14_8_MgfConvergenceSetup) {K : Set ℂ}
    (hK : IsCompact K)
    (hKU : K ⊆ prob_14_8_complexMGFStrip S) :
    ∃ C : ℝ,
      (∀ z : ℂ, z ∈ K →
        ‖complexMGF id (S.targetLaw : Measure ℝ) z‖ ≤ C) ∧
      (∀ n : ℕ, ∀ z : ℂ, z ∈ K →
        ‖complexMGF id (S.laws n : Measure ℝ) z‖ ≤ C) := by
  rcases prob_14_8_compact_subset_strip_subset_substrip S hK hKU with
    ⟨eta, heta_pos, heta_delta, hKeta⟩
  rcases prob_14_8_uniform_strip_bounds S eta heta_pos heta_delta with
    ⟨C, hTarget, hSeq⟩
  refine ⟨C, ?_, ?_⟩
  · intro z hz
    exact hTarget z (hKeta z hz)
  · intro n z hz
    exact hSeq n z (hKeta z hz)

/-- The underlying real sequence of positive points in the MGF interval,
tending to the accumulation point `0`. -/
def prob_14_8_realAxisAccumulationRealSequence
    (S : prob_14_8_MgfConvergenceSetup) : ℕ → ℝ :=
  fun n : ℕ => (S.δ / 2) * (1 / ((n : ℝ) + 1))

/-- A concrete nonzero sequence of real-axis complex points inside the open
strip, tending to the accumulation point `0`. -/
def prob_14_8_realAxisAccumulationSequence
    (S : prob_14_8_MgfConvergenceSetup) : ℕ → ℂ :=
  fun n : ℕ => (prob_14_8_realAxisAccumulationRealSequence S n : ℂ)

theorem prob_14_8_realAxisAccumulationSequence_real_pos
    (S : prob_14_8_MgfConvergenceSetup) (n : ℕ) :
    0 < prob_14_8_realAxisAccumulationRealSequence S n := by
  have hden_pos : 0 < (n : ℝ) + 1 := by positivity
  simpa [prob_14_8_realAxisAccumulationRealSequence] using
    mul_pos (half_pos S.δ_pos) (one_div_pos.mpr hden_pos)

theorem prob_14_8_realAxisAccumulationSequence_real_mem_interval
    (S : prob_14_8_MgfConvergenceSetup) (n : ℕ) :
    prob_14_8_realAxisAccumulationRealSequence S n ∈
      Set.Ioo (-S.δ) S.δ := by
  have hden_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hfrac_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hden_ge_one
  have hhalf_pos : 0 < S.δ / 2 := half_pos S.δ_pos
  have hvalue_pos :
      0 < prob_14_8_realAxisAccumulationRealSequence S n :=
    prob_14_8_realAxisAccumulationSequence_real_pos S n
  have hvalue_le_half :
      prob_14_8_realAxisAccumulationRealSequence S n ≤ S.δ / 2 := by
    simpa [prob_14_8_realAxisAccumulationRealSequence] using
      (mul_le_mul_of_nonneg_left hfrac_le_one (le_of_lt hhalf_pos))
  have hvalue_lt_delta :
      prob_14_8_realAxisAccumulationRealSequence S n < S.δ :=
    hvalue_le_half.trans_lt (half_lt_self S.δ_pos)
  exact ⟨by linarith [S.δ_pos, hvalue_pos], hvalue_lt_delta⟩

theorem prob_14_8_realAxisAccumulationSequence_ne_zero
    (S : prob_14_8_MgfConvergenceSetup) (n : ℕ) :
    prob_14_8_realAxisAccumulationSequence S n ≠ 0 := by
  intro hzero
  have hzero' :
      (prob_14_8_realAxisAccumulationRealSequence S n : ℂ) = 0 := by
    simpa [prob_14_8_realAxisAccumulationSequence] using hzero
  have hreal_zero :
      prob_14_8_realAxisAccumulationRealSequence S n = 0 :=
    Complex.ofReal_eq_zero.mp hzero'
  have hpos := prob_14_8_realAxisAccumulationSequence_real_pos S n
  linarith

theorem prob_14_8_realAxisAccumulationSequence_tendsto_zero
    (S : prob_14_8_MgfConvergenceSetup) :
    Tendsto (prob_14_8_realAxisAccumulationSequence S) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal :
      Tendsto (prob_14_8_realAxisAccumulationRealSequence S) atTop (𝓝 0) := by
    change
      Tendsto
        (fun n : ℕ => (S.δ / 2) * (1 / ((n : ℝ) + 1)))
        atTop
        (𝓝 0)
    simpa [one_div] using
      (Filter.Tendsto.const_mul (S.δ / 2) hbase)
  simpa [prob_14_8_realAxisAccumulationSequence] using
    (Complex.continuous_ofReal.tendsto 0).comp hreal

/-- The concrete accumulation input required before applying a later analytic
identity/Vitali foundation: there are nonzero real-axis points tending to `0`,
and complex-MGFs converge on every point in that sequence. -/
def prob_14_8_realAxisAccumulationConvergenceInput
    (S : prob_14_8_MgfConvergenceSetup) : Prop :=
  ∃ a : ℕ → ℂ,
    Tendsto a atTop (𝓝 0) ∧
    (∀ n : ℕ, a n ≠ 0) ∧
    (∀ n : ℕ,
      ∃ t : ℝ, t ∈ Set.Ioo (-S.δ) S.δ ∧
        a n = (t : ℂ) ∧
        Tendsto
          (fun k : ℕ => complexMGF id (S.laws k : Measure ℝ) (a n))
          atTop
          (𝓝 (complexMGF id (S.targetLaw : Measure ℝ) (a n))))

theorem prob_14_8_real_axis_accumulation_convergence_input
    (S : prob_14_8_MgfConvergenceSetup) :
    prob_14_8_realAxisAccumulationConvergenceInput S := by
  refine ⟨prob_14_8_realAxisAccumulationSequence S,
    prob_14_8_realAxisAccumulationSequence_tendsto_zero S,
    prob_14_8_realAxisAccumulationSequence_ne_zero S, ?_⟩
  intro n
  let t : ℝ := prob_14_8_realAxisAccumulationRealSequence S n
  have ht : t ∈ Set.Ioo (-S.δ) S.δ := by
    simpa [t] using
      prob_14_8_realAxisAccumulationSequence_real_mem_interval S n
  have htIcc : t ∈ Set.Icc (-S.δ) S.δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have htend := prob_14_8_real_axis_complexMGF_convergence_at S htIcc
  refine ⟨t, ht, ?_, ?_⟩
  · simp [prob_14_8_realAxisAccumulationSequence, t]
  · simpa [prob_14_8_realAxisAccumulationSequence, t] using htend

/-- Any locally uniform subsequential analytic limit on the common strip is
the target complex MGF, by real-axis MGF convergence and the identity theorem. -/
theorem prob_14_8_locally_uniform_subseq_limit_eq_target
    (S : prob_14_8_MgfConvergenceSetup) {f : ℂ → ℂ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hlim :
      TendstoLocallyUniformlyOn
        (fun k z => complexMGF id (S.laws (φ k) : Measure ℝ) z)
        f atTop (prob_14_8_complexMGFStrip S))
    (hf : AnalyticOnNhd ℂ f (prob_14_8_complexMGFStrip S)) :
    Set.EqOn f
      (fun z : ℂ => complexMGF id (S.targetLaw : Measure ℝ) z)
      (prob_14_8_complexMGFStrip S) := by
  rcases prob_14_8_real_axis_accumulation_convergence_input S with
    ⟨a, ha_lim, ha_ne, ha_conv⟩
  have htarget_analytic :=
    (prob_14_8_complexMGF_analytic_on_common_strip S).2
  refine prob_14_8_locally_uniform_subseq_limit_eqOn_of_real_axis
    (F := fun k z => complexMGF id (S.laws k : Measure ℝ) z)
    (g := fun z : ℂ => complexMGF id (S.targetLaw : Measure ℝ) z)
    (U := prob_14_8_complexMGFStrip S)
    (φ := φ) (z0 := 0) (a := a)
    hf htarget_analytic
    (prob_14_8_complexMGFStrip_isPreconnected S)
    (prob_14_8_zero_mem_complexMGFStrip S)
    hφ hlim ha_lim ha_ne ?_ ?_
  · intro n
    rcases ha_conv n with ⟨t, ht, haeq, _htend⟩
    simpa [prob_14_8_complexMGFStrip, haeq] using ht
  · intro n
    rcases ha_conv n with ⟨_t, _ht, _haeq, htend⟩
    exact htend

/-- Normal-family extraction for every subsequence of the sequence complex
MGFs on the common strip. -/
theorem prob_14_8_complexMGF_subseq_locallyUniform_limit
    (S : prob_14_8_MgfConvergenceSetup)
    {φ : ℕ → ℕ} (_hφ : StrictMono φ) :
    ∃ f : ℂ → ℂ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn
        (fun k z => complexMGF id (S.laws (φ (ψ k)) : Measure ℝ) z)
        f atTop (prob_14_8_complexMGFStrip S) := by
  exact prob_14_8_montel_subseq_of_analytic_compact_bounds
    (F := fun n z => complexMGF id (S.laws (φ n) : Measure ℝ) z)
    (U := prob_14_8_complexMGFStrip S)
    (prob_14_8_complexMGFStrip_isOpen S)
    (fun n => (prob_14_8_complexMGF_analytic_on_common_strip S).1 (φ n))
    (by
      intro K hK hKU
      rcases prob_14_8_uniformComplexMGFCompactBound S hK hKU with
        ⟨C, _hTarget, hSeq⟩
      exact ⟨C, fun n z hz => hSeq (φ n) z hz⟩)

/-- The MGF hypotheses give a common exponential tail cutoff for all
sufficiently large indices.  This proves the tightness part independently of
the later analytic continuation step. -/
theorem prob_14_8_eventualTailBound_from_mgf
    (S : prob_14_8_MgfConvergenceSetup) :
    ∀ ε : ℝ, 0 < ε → ∃ M0 : ℝ, 0 ≤ M0 ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → thm_14_5_tailMass (S.laws n) M0 < ε := by
  intro ε hε
  let Bp : ℝ := prob_14_8_mgfOfLaw S.targetLaw S.δ + 1
  let Bn : ℝ := prob_14_8_mgfOfLaw S.targetLaw (-S.δ) + 1
  let B : ℝ := Bp + Bn
  have hδmem : S.δ ∈ Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos]
  have hnegδmem : -S.δ ∈ Icc (-S.δ) S.δ := by
    constructor <;> linarith [S.δ_pos]
  have hBp_event :
      ∀ᶠ n : ℕ in atTop, prob_14_8_mgfOfLaw (S.laws n) S.δ < Bp := by
    exact (S.mgf_converges S.δ hδmem).eventually_lt_const (by
      dsimp [Bp]
      linarith)
  have hBn_event :
      ∀ᶠ n : ℕ in atTop, prob_14_8_mgfOfLaw (S.laws n) (-S.δ) < Bn := by
    exact (S.mgf_converges (-S.δ) hnegδmem).eventually_lt_const (by
      dsimp [Bn]
      linarith)
  have harg : Tendsto (fun M : ℝ => (-S.δ) * M) atTop atBot := by
    exact Filter.Tendsto.neg_mul_atTop (C := -S.δ)
      (by linarith [S.δ_pos]) tendsto_const_nhds tendsto_id
  have hexp : Tendsto (fun M : ℝ => Real.exp ((-S.δ) * M)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hprod : Tendsto (fun M : ℝ => Real.exp ((-S.δ) * M) * B) atTop (𝓝 0) := by
    simpa using hexp.mul (tendsto_const_nhds (x := B))
  have hsmall_event : ∀ᶠ M : ℝ in atTop, Real.exp ((-S.δ) * M) * B < ε :=
    hprod.eventually_lt_const (by simpa using hε)
  rcases (eventually_atTop.1 hsmall_event) with ⟨Mexp, hMexp⟩
  rcases (eventually_atTop.1 (hBp_event.and hBn_event)) with ⟨N, hN⟩
  let M0 : ℝ := max Mexp 0
  refine ⟨M0, le_max_right Mexp 0, ⟨N, ?_⟩⟩
  intro n hn
  have hbounds := hN n hn
  have hp_le : prob_14_8_mgfOfLaw (S.laws n) S.δ ≤ Bp := le_of_lt hbounds.1
  have hn_le : prob_14_8_mgfOfLaw (S.laws n) (-S.δ) ≤ Bn := le_of_lt hbounds.2
  have hsmallM : Real.exp ((-S.δ) * M0) * B < ε :=
    hMexp M0 (le_max_left Mexp 0)
  have htail_le :
      thm_14_5_tailMass (S.laws n) M0 ≤ Real.exp ((-S.δ) * M0) * B := by
    haveI : IsProbabilityMeasure (S.laws n : Measure ℝ) := (S.laws n).property
    let upper : Set ℝ := {x : ℝ | M0 ≤ x}
    let lower : Set ℝ := {x : ℝ | x ≤ -M0}
    have hsubset : {x : ℝ | M0 < |x|} ⊆ upper ∪ lower := by
      intro x hx
      by_cases hxnonneg : 0 ≤ x
      · left
        have habs : |x| = x := abs_of_nonneg hxnonneg
        exact le_of_lt (by simpa [upper, habs] using hx)
      · right
        have hxneg : x < 0 := lt_of_not_ge hxnonneg
        have habs : |x| = -x := abs_of_neg hxneg
        have hMx : M0 < -x := by simpa [habs] using hx
        have hxle : x < -M0 := by linarith [hMx]
        exact le_of_lt hxle
    have hmono :
        thm_14_5_tailMass (S.laws n) M0 ≤
          (S.laws n : Measure ℝ).real (upper ∪ lower) :=
      measureReal_mono hsubset
    have hunion :
        (S.laws n : Measure ℝ).real (upper ∪ lower) ≤
          (S.laws n : Measure ℝ).real upper +
            (S.laws n : Measure ℝ).real lower :=
      measureReal_union_le upper lower
    have hupper :
        (S.laws n : Measure ℝ).real upper ≤
          Real.exp ((-S.δ) * M0) * prob_14_8_mgfOfLaw (S.laws n) S.δ := by
      simpa [upper, prob_14_8_mgfOfLaw, neg_mul] using
        (ProbabilityTheory.measure_ge_le_exp_mul_mgf
          (μ := (S.laws n : Measure ℝ)) (X := fun x : ℝ => x)
          (ε := M0) (t := S.δ) S.δ_pos.le (S.mgf_defined n S.δ hδmem))
    have hlower :
        (S.laws n : Measure ℝ).real lower ≤
          Real.exp ((-S.δ) * M0) * prob_14_8_mgfOfLaw (S.laws n) (-S.δ) := by
      have h :=
        (ProbabilityTheory.measure_le_le_exp_mul_mgf
          (μ := (S.laws n : Measure ℝ)) (X := fun x : ℝ => x)
          (ε := -M0) (t := -S.δ) (by linarith [S.δ_pos])
          (S.mgf_defined n (-S.δ) hnegδmem))
      simpa [lower, prob_14_8_mgfOfLaw, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h
    calc
      thm_14_5_tailMass (S.laws n) M0
          ≤ (S.laws n : Measure ℝ).real (upper ∪ lower) := hmono
      _ ≤ (S.laws n : Measure ℝ).real upper +
          (S.laws n : Measure ℝ).real lower := hunion
      _ ≤ Real.exp ((-S.δ) * M0) * prob_14_8_mgfOfLaw (S.laws n) S.δ +
          Real.exp ((-S.δ) * M0) * prob_14_8_mgfOfLaw (S.laws n) (-S.δ) := by
            exact add_le_add hupper hlower
      _ ≤ Real.exp ((-S.δ) * M0) * Bp + Real.exp ((-S.δ) * M0) * Bn := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hp_le (Real.exp_pos _).le)
              (mul_le_mul_of_nonneg_left hn_le (Real.exp_pos _).le)
      _ = Real.exp ((-S.δ) * M0) * B := by
            ring
  exact lt_of_le_of_lt htail_le hsmallM

/-- The MGF hypotheses imply the uniform tail estimate used by the interval
form of tightness. -/
theorem prob_14_8_uniformTailBound_from_mgf
    (S : prob_14_8_MgfConvergenceSetup) :
    thm_14_5_uniformTailBound S.laws := by
  intro ε hε
  rcases prob_14_8_eventualTailBound_from_mgf S ε hε with
    ⟨M0, hM0_nonneg, ⟨N, htail_eventual⟩⟩
  rcases thm_14_5_source_route_finite_prefix_tail_bound S.laws ε hε N M0 hM0_nonneg with
    ⟨M, hM0M, htail_prefix⟩
  refine ⟨M, hM0_nonneg.trans hM0M, ?_⟩
  intro n
  by_cases hn : n < N
  · exact htail_prefix n hn
  · exact lt_of_le_of_lt
      (thm_14_5_tailMass_mono (S.laws n) hM0M)
      (htail_eventual n (le_of_not_gt hn))

/-- Part (a): MGF control on a neighborhood of zero implies tightness. -/
theorem prob_14_8_tight
    (S : prob_14_8_MgfConvergenceSetup) :
    def_14_3 S.laws := by
  exact thm_14_5_of_uniformTailBound S.laws (prob_14_8_uniformTailBound_from_mgf S)

/-- Characteristic convergence to the target characteristic function implies
the distribution-convergence conclusion of part (b).  The missing analytic
work is precisely to derive `hChar` from the MGF-neighborhood hypotheses. -/
theorem prob_14_8_converges_in_distribution_of_characteristic_convergence
    (S : prob_14_8_MgfConvergenceSetup)
    (hChar :
      thm_14_1_pointwiseCharFunConvergence
        S.laws
        (fun t : ℝ => thm_14_1_characteristicFunction S.targetLaw t)) :
    Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := S.laws) (μ₀ := S.targetLaw)).2
      (fun t => by
        simpa [thm_14_1_characteristicFunction] using hChar t)

/-- Convergence of the complex MGF on the imaginary axis gives the pointwise
characteristic-function convergence required by Levy's theorem. -/
theorem prob_14_8_characteristic_convergence_from_imaginary_axis_complexMGF
    (S : prob_14_8_MgfConvergenceSetup)
    (hImag :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ => complexMGF id (S.laws n : Measure ℝ) (t * Complex.I))
          atTop
          (𝓝 (complexMGF id (S.targetLaw : Measure ℝ) (t * Complex.I)))) :
    thm_14_1_pointwiseCharFunConvergence
      S.laws
      (fun t : ℝ => thm_14_1_characteristicFunction S.targetLaw t) := by
  intro t
  simpa [prob_14_8_characteristic_eq_complexMGF] using hImag t

/-- Once the analytic continuation step proves imaginary-axis complex-MGF
convergence, the distribution-convergence conclusion follows. -/
theorem prob_14_8_distribution_convergence_from_imaginary_axis_complexMGF
    (S : prob_14_8_MgfConvergenceSetup)
    (hImag :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ => complexMGF id (S.laws n : Measure ℝ) (t * Complex.I))
          atTop
          (𝓝 (complexMGF id (S.targetLaw : Measure ℝ) (t * Complex.I)))) :
    Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact prob_14_8_converges_in_distribution_of_characteristic_convergence S
    (prob_14_8_characteristic_convergence_from_imaginary_axis_complexMGF S hImag)

/-- Source-facing final assembly conditional only on the exact remaining
imaginary-axis complex-MGF convergence theorem. -/
theorem prob_14_8_tight_and_distribution_from_imaginary_axis_complexMGF
    (S : prob_14_8_MgfConvergenceSetup)
    (hImag :
      ∀ t : ℝ,
        Tendsto
          (fun n : ℕ => complexMGF id (S.laws n : Measure ℝ) (t * Complex.I))
          atTop
          (𝓝 (complexMGF id (S.targetLaw : Measure ℝ) (t * Complex.I)))) :
    def_14_3 S.laws ∧ Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact ⟨prob_14_8_tight S,
    prob_14_8_distribution_convergence_from_imaginary_axis_complexMGF S hImag⟩

/-- The precise remaining theorem shape needed to remove the public `hChar`
premise from the final Problem 14.8 assembly. -/
def prob_14_8_remaining_imaginary_axis_complexMGF_convergence
    (S : prob_14_8_MgfConvergenceSetup) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun n : ℕ => complexMGF id (S.laws n : Measure ℝ) (t * Complex.I))
      atTop
      (𝓝 (complexMGF id (S.targetLaw : Measure ℝ) (t * Complex.I)))

/-- If every subsequence has a locally uniformly convergent further subsequence
on the common strip, then the already-proved real-axis identity step identifies
all subsequential limits with the target and yields full imaginary-axis
complex-MGF convergence. -/
theorem prob_14_8_imaginary_axis_complexMGF_convergence_of_subseq_locallyUniform
    (S : prob_14_8_MgfConvergenceSetup)
    (hExtract :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ f : ℂ → ℂ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          TendstoLocallyUniformlyOn
            (fun k z => complexMGF id (S.laws (φ (ψ k)) : Measure ℝ) z)
            f atTop (prob_14_8_complexMGFStrip S)) :
    prob_14_8_remaining_imaginary_axis_complexMGF_convergence S := by
  intro t
  refine prob_14_8_tendsto_of_subseq_subseq_tendsto ?_
  intro φ hφ
  rcases hExtract φ hφ with ⟨f, ψ, hψ, hlim⟩
  let target : ℂ → ℂ := fun z : ℂ =>
    complexMGF id (S.targetLaw : Measure ℝ) z
  have hF_event :
      ∀ᶠ k : ℕ in atTop,
        AnalyticOnNhd ℂ
          (fun z : ℂ => complexMGF id (S.laws (φ (ψ k)) : Measure ℝ) z)
          (prob_14_8_complexMGFStrip S) :=
    Filter.Eventually.of_forall
      (fun k => (prob_14_8_complexMGF_analytic_on_common_strip S).1 (φ (ψ k)))
  have hf :
      AnalyticOnNhd ℂ f (prob_14_8_complexMGFStrip S) :=
    prob_14_8_locally_uniform_limit_of_analytic_is_analytic
      (prob_14_8_complexMGFStrip_isOpen S) hF_event hlim
  have hEq :
      Set.EqOn f target (prob_14_8_complexMGFStrip S) := by
    simpa [target] using
      prob_14_8_locally_uniform_subseq_limit_eq_target
        (S := S) (φ := fun k : ℕ => φ (ψ k))
        (hφ.comp hψ) hlim hf
  have ht_mem : t * Complex.I ∈ prob_14_8_complexMGFStrip S :=
    prob_14_8_imaginary_axis_mem_complexMGFStrip S t
  refine ⟨ψ, hψ, ?_⟩
  have hpoint :
      Tendsto
        (fun k : ℕ =>
          complexMGF id (S.laws (φ (ψ k)) : Measure ℝ) (t * Complex.I))
        atTop
        (𝓝 (f (t * Complex.I))) :=
    hlim.tendsto_at ht_mem
  have htarget_eq : f (t * Complex.I) = target (t * Complex.I) :=
    hEq ht_mem
  simpa [target, htarget_eq] using hpoint

/-- MGF convergence on a neighborhood of zero implies convergence of complex
MGFs on the imaginary axis. This is the internal Curtiss/Vitali bridge; no
characteristic-convergence premise is exposed. -/
theorem prob_14_8_imaginary_axis_complexMGF_convergence_from_mgf_setup
    (S : prob_14_8_MgfConvergenceSetup) :
    prob_14_8_remaining_imaginary_axis_complexMGF_convergence S := by
  exact prob_14_8_imaginary_axis_complexMGF_convergence_of_subseq_locallyUniform S
    (fun φ hφ =>
      prob_14_8_complexMGF_subseq_locallyUniform_limit S hφ)

/-- Characteristic convergence from the MGF setup once the single remaining
analytic-continuation theorem is supplied. -/
theorem prob_14_8_characteristic_convergence_from_mgf_setup_of_remaining
    (S : prob_14_8_MgfConvergenceSetup)
    (hRemaining :
      prob_14_8_remaining_imaginary_axis_complexMGF_convergence S) :
    thm_14_1_pointwiseCharFunConvergence
      S.laws
      (fun t : ℝ => thm_14_1_characteristicFunction S.targetLaw t) := by
  exact prob_14_8_characteristic_convergence_from_imaginary_axis_complexMGF S
    hRemaining

/-- Distribution convergence from the MGF setup once the remaining
imaginary-axis complex-MGF convergence theorem is supplied. -/
theorem prob_14_8_distribution_convergence_from_mgf_setup_of_remaining
    (S : prob_14_8_MgfConvergenceSetup)
    (hRemaining :
      prob_14_8_remaining_imaginary_axis_complexMGF_convergence S) :
    Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact prob_14_8_distribution_convergence_from_imaginary_axis_complexMGF S
    hRemaining

/-- Safe partial assembly for Problem 14.8: part (a), plus part (b) once the
remaining MGF-to-characteristic theorem is supplied. -/
theorem prob_14_8_tight_and_distribution_from_characteristic_convergence
    (S : prob_14_8_MgfConvergenceSetup)
    (hChar :
      thm_14_1_pointwiseCharFunConvergence
        S.laws
        (fun t : ℝ => thm_14_1_characteristicFunction S.targetLaw t)) :
    def_14_3 S.laws ∧ Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact ⟨prob_14_8_tight S,
    prob_14_8_converges_in_distribution_of_characteristic_convergence S hChar⟩

/-- Problem 14.8: MGF convergence on a neighborhood of zero implies tightness
and convergence in distribution to the target law. -/
theorem prob_14_8_support_result
    (S : prob_14_8_MgfConvergenceSetup) :
    def_14_3 S.laws ∧ Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  exact prob_14_8_tight_and_distribution_from_imaginary_axis_complexMGF S
    (prob_14_8_imaginary_axis_complexMGF_convergence_from_mgf_setup S)

