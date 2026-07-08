import Mathlib
import ToyApollo.Output.def_13_4
import ToyApollo.Output.ex_1_3_2
import ToyApollo.Output.thm_13_2

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-!
Parent-owned support for Problem 13.2.

This file isolates the Gaussian tail, symmetry, scaling, and finite-observation
conditional-expectation bridge work required before the source-facing parent
problem can be reassembled.
-/

/-- The thresholded observation from Problem 13.2. -/
def prob_13_2_thresholdY (sigma x : ℝ) : ℝ :=
  if x < -sigma then -1 else if x <= sigma then 0 else 1

/-- Standard normal density at `1`. -/
def prob_13_2_standardNormalPdfAtOne : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) 1

/-- Standard normal right-tail mass as a real number. -/
def prob_13_2_standardNormalUpperTailMass : ℝ :=
  (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ))).toReal

/-- The positive-tail conditional mean for `X ~ N(0, sigma^2)`. -/
def prob_13_2_positiveTailMean (sigma : ℝ) : ℝ :=
  sigma * prob_13_2_standardNormalPdfAtOne /
    prob_13_2_standardNormalUpperTailMass

/-- The candidate value of `E[X | Y]` on the three observation atoms. -/
def prob_13_2_E_X_given_Y_value (sigma y : ℝ) : ℝ :=
  if y = -1 then -prob_13_2_positiveTailMean sigma
  else if y = 0 then 0
  else if y = 1 then prob_13_2_positiveTailMean sigma
  else 0

/-- The candidate value of `E[X | Y^2]`. -/
def prob_13_2_E_X_given_Y_sq_value (_sigma _z : ℝ) : ℝ := 0

/-- The three labels used by the threshold observation. -/
def prob_13_2_threeLabel (i : Fin 3) : ℝ :=
  if i = 0 then -1 else if i = 1 then 0 else 1

theorem prob_13_2_threeLabel_injective :
    Function.Injective prob_13_2_threeLabel := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [prob_13_2_threeLabel] at h ⊢ <;>
    norm_num at h

/-- The atom of a three-valued observation corresponding to one label. -/
def prob_13_2_observationAtom {Ω : Type*} (Y : Ω → ℝ) (i : Fin 3) : Set Ω :=
  {ω | Y ω = prob_13_2_threeLabel i}

theorem prob_13_2_observationAtom_disjoint {Ω : Type*} {Y : Ω → ℝ} :
    Pairwise fun i j : Fin 3 => Disjoint (prob_13_2_observationAtom Y i)
      (prob_13_2_observationAtom Y j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro ω hi hj
  have hlabels : prob_13_2_threeLabel i = prob_13_2_threeLabel j :=
    hi.symm.trans hj
  exact hij (prob_13_2_threeLabel_injective hlabels)

/-- Finite-valued-observation bridge to Definition 13.4 for observations with
values in `{-1, 0, 1}`. -/
theorem prob_13_2_finite_observation_def_13_4_atom_bridge {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X CE Y : Ω → ℝ}
    (hXint : Integrable X P) (hCEint : Integrable CE P)
    (hYmeas : Measurable Y)
    (hCEmeas : Measurable[def_13_4_sigma Y] CE)
    (hYrange : ∀ ω, Y ω = -1 ∨ Y ω = 0 ∨ Y ω = 1)
    (hm :
      ∫ ω in prob_13_2_observationAtom Y 0, CE ω ∂P =
        ∫ ω in prob_13_2_observationAtom Y 0, X ω ∂P)
    (h0 :
      ∫ ω in prob_13_2_observationAtom Y 1, CE ω ∂P =
        ∫ ω in prob_13_2_observationAtom Y 1, X ω ∂P)
    (h1 :
      ∫ ω in prob_13_2_observationAtom Y 2, CE ω ∂P =
        ∫ ω in prob_13_2_observationAtom Y 2, X ω ∂P) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X CE := by
  classical
  unfold def_13_4 def_13_3 ConditionalExpectationSetFormula
  refine ⟨hXint, hCEint, hCEmeas, ?_⟩
  intro B hB
  rcases (MeasurableSpace.measurableSet_comap.mp hB) with ⟨A, _hA, hBA⟩
  let I : Finset (Fin 3) :=
    Finset.univ.filter (fun i => prob_13_2_threeLabel i ∈ A)
  have hAtomMeas : ∀ i : Fin 3, MeasurableSet (prob_13_2_observationAtom Y i) := by
    intro i
    exact (measurableSet_singleton (prob_13_2_threeLabel i)).preimage hYmeas
  have hBunion : B = ⋃ i ∈ I, prob_13_2_observationAtom Y i := by
    ext ω
    constructor
    · intro hωB
      have hYA : Y ω ∈ A := by
        rw [← hBA] at hωB
        exact hωB
      rcases hYrange ω with hneg | hzero | hone
      · have hlabelA : (-1 : ℝ) ∈ A := by
          simpa [hneg] using hYA
        refine Set.mem_iUnion.2 ⟨(0 : Fin 3), ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        · simp [I, prob_13_2_threeLabel, hlabelA]
        · simpa [prob_13_2_observationAtom, prob_13_2_threeLabel] using hneg
      · have hlabelA : (0 : ℝ) ∈ A := by
          simpa [hzero] using hYA
        refine Set.mem_iUnion.2 ⟨(1 : Fin 3), ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        · simp [I, prob_13_2_threeLabel, hlabelA]
        · simpa [prob_13_2_observationAtom, prob_13_2_threeLabel] using hzero
      · have hlabelA : (1 : ℝ) ∈ A := by
          simpa [hone] using hYA
        refine Set.mem_iUnion.2 ⟨(2 : Fin 3), ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        · simp [I, prob_13_2_threeLabel, hlabelA]
        · simpa [prob_13_2_observationAtom, prob_13_2_threeLabel] using hone
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨i, hi_rest⟩
      rcases Set.mem_iUnion.1 hi_rest with ⟨hiI, hωatom⟩
      have hlabelA : prob_13_2_threeLabel i ∈ A := by
        simpa [I] using hiI
      rw [← hBA]
      have hYeq : Y ω = prob_13_2_threeLabel i := by
        simpa [prob_13_2_observationAtom] using hωatom
      simpa [hYeq] using hlabelA
  have hCEsum := thm_13_2_right_selected_sum (P := P)
    (A := prob_13_2_observationAtom Y) (X := CE)
    hAtomMeas prob_13_2_observationAtom_disjoint hCEint hBunion
  have hXsum := thm_13_2_right_selected_sum (P := P)
    (A := prob_13_2_observationAtom Y) (X := X)
    hAtomMeas prob_13_2_observationAtom_disjoint hXint hBunion
  calc
    ∫ ω in B, CE ω ∂P =
        ∑ i ∈ I, ∫ ω in prob_13_2_observationAtom Y i, CE ω ∂P := hCEsum
    _ = ∑ i ∈ I, ∫ ω in prob_13_2_observationAtom Y i, X ω ∂P := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      fin_cases i <;> simp [hm, h0, h1]
    _ = ∫ ω in B, X ω ∂P := hXsum.symm

theorem prob_13_2_standardNormal_tail_exp_core :
    (∫ x in Set.Ioi (1 : ℝ), x * Real.exp (-(x^2) / 2)) =
      Real.exp (-(1 : ℝ)^2 / 2) := by
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => - Real.exp (-(y^2) / 2))
        (x * Real.exp (-(x^2) / 2)) x := by
    intro x hx
    have hinner : HasDerivAt (fun y : ℝ => -(y^2) / 2) (-x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using ((hasDerivAt_id x).pow 2)
      convert hsq.neg.div_const 2 using 1 <;> ring
    have hexp := hinner.exp
    have hneg := hexp.neg
    convert hneg using 1 <;> ring
  have hint : IntegrableOn
      (fun x : ℝ => x * Real.exp (-(x^2) / 2)) (Set.Ioi (1 : ℝ)) := by
    have hglobal : Integrable
        (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
    exact hglobal.integrableOn.congr_fun (fun x hx => by
      congr 1
      ring_nf) measurableSet_Ioi
  have htend :
      Tendsto (fun x : ℝ => - Real.exp (-(x^2) / 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) atTop atTop := by
      exact tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)
    have hhalf : Tendsto
        (fun x : ℝ => (x ^ (2 : ℕ)) / 2) atTop atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        hsq.const_mul_atTop (by norm_num : (0 : ℝ) < (1 / 2))
    have hneg :
        Tendsto (fun x : ℝ => - ((x ^ (2 : ℕ)) / 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hhalf
    have h0 :
        Tendsto (fun x : ℝ => Real.exp (- ((x ^ (2 : ℕ)) / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hfun :
        (fun x : ℝ => - Real.exp (- ((x ^ (2 : ℕ)) / 2))) =
          (fun x : ℝ => - Real.exp (-(x^2) / 2)) := by
      funext x
      congr 2
      ring
    simpa [hfun] using h0.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  simpa using h

/-- Standard normal right-tail first-moment numerator. -/
theorem prob_13_2_standardNormal_right_tail_numerator :
    (∫ z in Set.Ioi (1 : ℝ),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) =
      ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) 1 := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show
      (fun z : ℝ =>
        z * ((√(2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2))) =
      fun z : ℝ =>
        (√(2 * Real.pi))⁻¹ * (z * Real.exp (-(z ^ 2) / 2)) by
    funext z
    ring]
  rw [integral_const_mul]
  rw [prob_13_2_standardNormal_tail_exp_core]

/-- The standard normal right-tail denominator is positive. -/
theorem prob_13_2_standardNormal_right_tail_mass_pos :
    0 < ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ)) := by
  rw [ProbabilityTheory.gaussianReal_apply (μ := 0) (v := (1 : NNReal)) (by norm_num)
    (Set.Ioi (1 : ℝ))]
  rw [lintegral_pos_iff_support (ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal))]
  simp [ProbabilityTheory.support_gaussianPDF (μ := 0) (v := (1 : NNReal)) (by norm_num),
    Real.volume_Ioi]

theorem prob_13_2_standardNormal_right_tail_mass_toReal_pos :
    0 < (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ))).toReal := by
  have hpos := prob_13_2_standardNormal_right_tail_mass_pos
  have hlt :
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ)) < ⊤ := by
    exact measure_lt_top _ _
  exact ENNReal.toReal_pos hpos.ne' hlt.ne

theorem prob_13_2_standardNormal_right_tail_mass_toReal_ne_zero :
    (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ))).toReal ≠ 0 :=
  ne_of_gt prob_13_2_standardNormal_right_tail_mass_toReal_pos

/-- Scaling a nondegenerate zero-mean Gaussian by its standard deviation gives
the standard normal law. -/
theorem prob_13_2_gaussian_scale_to_standard {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hX : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    HasLaw (fun ω => X ω / sigma)
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P := by
  have h := ProbabilityTheory.gaussianReal_div_const hX sigma
  convert h using 2
  · simp
  · ext
    simp [hsigma.ne']

theorem prob_13_2_standard_threshold_right_event {Ω : Type*}
    {X : Ω → ℝ} {sigma : ℝ} (hsigma : 0 < sigma) :
    {ω : Ω | 1 < X ω / sigma} = {ω : Ω | sigma < X ω} := by
  ext ω
  constructor
  · intro h
    simpa using (lt_div_iff₀ hsigma).mp h
  · intro h
    have hmul : (1 : ℝ) * sigma < X ω := by
      simpa using h
    simpa using (lt_div_iff₀ hsigma).mpr hmul

theorem prob_13_2_standard_threshold_left_event {Ω : Type*}
    {X : Ω → ℝ} {sigma : ℝ} (hsigma : 0 < sigma) :
    {ω : Ω | X ω / sigma < -1} = {ω : Ω | X ω < -sigma} := by
  ext ω
  constructor
  · intro h
    have hmul := (div_lt_iff₀ hsigma).mp h
    simpa using hmul
  · intro h
    have hmul : X ω < (-1 : ℝ) * sigma := by
      simpa using h
    have hdiv := (div_lt_iff₀ hsigma).mpr hmul
    simpa using hdiv

theorem prob_13_2_standard_threshold_central_event {Ω : Type*}
    {X : Ω → ℝ} {sigma : ℝ} (hsigma : 0 < sigma) :
    {ω : Ω | -1 ≤ X ω / sigma ∧ X ω / sigma ≤ 1} =
      {ω : Ω | -sigma ≤ X ω ∧ X ω ≤ sigma} := by
  ext ω
  constructor
  · intro h
    constructor
    · have hmul := (le_div_iff₀ hsigma).mp h.1
      simpa using hmul
    · simpa using (div_le_iff₀ hsigma).mp h.2
  · intro h
    constructor
    · have hmul : (-1 : ℝ) * sigma ≤ X ω := by
        simpa using h.1
      have hdiv := (le_div_iff₀ hsigma).mpr hmul
      simpa using hdiv
    · have hmul : X ω ≤ (1 : ℝ) * sigma := by
        simpa using h.2
      simpa using (div_le_iff₀ hsigma).mpr hmul

/-- The central standard-normal odd integral over `[-1, 1]` is zero, written
with the local standard-normal kernel from Example 1.3.2. -/
theorem prob_13_2_central_atom_odd_integral_zero_kernel :
    ∫ y in (-(1 : ℝ))..(1 : ℝ), y * Ex132.standardNormalKernel y = 0 := by
  set c : ℝ := 1 with hc
  set g : ℝ → ℝ := fun y => y * Ex132.standardNormalKernel y with hg
  have hcomp :
      ∫ x in (-c : ℝ)..c, g (-x) = ∫ x in (-c : ℝ)..c, g x := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := (-c : ℝ)) (b := c)
    simp only [neg_neg] at h
    exact h
  have hodd : ∫ x in (-c : ℝ)..c, g (-x) = -∫ x in (-c : ℝ)..c, g x := by
    have hpt : ∀ x, g (-x) = -g x := by
      intro x
      simp only [hg]
      exact Ex132.mixedIntegrand_odd x
    calc
      ∫ x in (-c : ℝ)..c, g (-x) = ∫ x in (-c : ℝ)..c, -g x := by
        simp only [hpt]
      _ = -∫ x in (-c : ℝ)..c, g x := by
        rw [intervalIntegral.integral_neg]
  have hself : ∫ x in (-c : ℝ)..c, g x = -∫ x in (-c : ℝ)..c, g x := by
    calc
      ∫ x in (-c : ℝ)..c, g x = ∫ x in (-c : ℝ)..c, g (-x) := hcomp.symm
      _ = -∫ x in (-c : ℝ)..c, g x := hodd
  have hzero : ∫ x in (-c : ℝ)..c, g x = 0 := by
    linarith [hself]
  simpa [hc, hg] using hzero

/-- The central standard-normal odd integral over `[-1, 1]` is zero. -/
theorem prob_13_2_central_atom_odd_integral_zero :
    ∫ y in (-(1 : ℝ))..(1 : ℝ),
      y * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) y = 0 := by
  have hconv :
      (∫ y in (-(1 : ℝ))..(1 : ℝ),
        y * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) y) =
      ∫ y in (-(1 : ℝ))..(1 : ℝ), y * Ex132.standardNormalKernel y := by
    apply intervalIntegral.integral_congr
    intro y _hy
    change y * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) y =
      y * Ex132.standardNormalKernel y
    rw [← Ex132.standardNormalKernel_eq_gaussianPDFReal y]
  rw [hconv, prob_13_2_central_atom_odd_integral_zero_kernel]

theorem prob_13_2_standardNormal_left_tail_exp_core :
    (∫ x in Set.Iic (-(1 : ℝ)), x * Real.exp (-(x^2) / 2)) =
      -Real.exp (-(1 : ℝ)^2 / 2) := by
  have hderiv : ∀ x ∈ Set.Iic (-(1 : ℝ)),
      HasDerivAt (fun y : ℝ => - Real.exp (-(y^2) / 2))
        (x * Real.exp (-(x^2) / 2)) x := by
    intro x hx
    have hinner : HasDerivAt (fun y : ℝ => -(y^2) / 2) (-x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using ((hasDerivAt_id x).pow 2)
      convert hsq.neg.div_const 2 using 1 <;> ring
    have hexp := hinner.exp
    have hneg := hexp.neg
    convert hneg using 1 <;> ring
  have hint : IntegrableOn
      (fun x : ℝ => x * Real.exp (-(x^2) / 2)) (Set.Iic (-(1 : ℝ))) := by
    have hglobal : Integrable
        (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
    exact hglobal.integrableOn.congr_fun (fun x hx => by
      congr 1
      ring_nf) measurableSet_Iic
  have htend :
      Tendsto (fun x : ℝ => - Real.exp (-(x^2) / 2)) atBot (𝓝 0) := by
    have hsq_pos :
        Tendsto (fun x : ℝ => (-x) ^ (2 : ℕ)) atBot atTop := by
      exact (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
        tendsto_neg_atBot_atTop
    have hsq : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) atBot atTop := by
      have hfun : (fun x : ℝ => (-x) ^ (2 : ℕ)) = fun x : ℝ => x ^ (2 : ℕ) := by
        funext x
        ring
      simpa [hfun] using hsq_pos
    have hhalf :
        Tendsto (fun x : ℝ => (x ^ (2 : ℕ)) / 2) atBot atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        hsq.const_mul_atTop (by norm_num : (0 : ℝ) < (1 / 2))
    have hneg :
        Tendsto (fun x : ℝ => - ((x ^ (2 : ℕ)) / 2)) atBot atBot :=
      tendsto_neg_atTop_atBot.comp hhalf
    have h0 :
        Tendsto (fun x : ℝ => Real.exp (- ((x ^ (2 : ℕ)) / 2))) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hfun :
        (fun x : ℝ => - Real.exp (- ((x ^ (2 : ℕ)) / 2))) =
          (fun x : ℝ => - Real.exp (-(x^2) / 2)) := by
      funext x
      congr 2
      ring
    simpa [hfun] using h0.neg
  have h := integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint htend
  simpa using h

/-- Standard normal left-tail first-moment numerator. -/
theorem prob_13_2_standardNormal_left_tail_numerator_Iic :
    (∫ z in Set.Iic (-(1 : ℝ)),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) =
      -ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) 1 := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show
      (fun z : ℝ =>
        z * ((√(2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2))) =
      fun z : ℝ =>
        (√(2 * Real.pi))⁻¹ * (z * Real.exp (-(z ^ 2) / 2)) by
    funext z
    ring]
  rw [integral_const_mul]
  rw [prob_13_2_standardNormal_left_tail_exp_core]
  ring

/-- The open-left-tail and closed-left-tail first moments agree because the
endpoint is Lebesgue-null. -/
theorem prob_13_2_standardNormal_left_tail_numerator :
    (∫ z in Set.Iio (-(1 : ℝ)),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) =
      -ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) 1 := by
  rw [← integral_Iic_eq_integral_Iio]
  exact prob_13_2_standardNormal_left_tail_numerator_Iic

/-- The symmetric two-tail first moment cancels. -/
theorem prob_13_2_two_tail_odd_integral_zero :
    (∫ z in Set.Iio (-(1 : ℝ)),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) +
      (∫ z in Set.Ioi (1 : ℝ),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) = 0 := by
  rw [prob_13_2_standardNormal_left_tail_numerator,
    prob_13_2_standardNormal_right_tail_numerator]
  ring

theorem prob_13_2_standardNormal_Iio_eq_Iic (a : ℝ) :
    ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iio a) =
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iic a) := by
  have hac :
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) ≪ (volume : Measure ℝ) := by
    simpa using
      ProbabilityTheory.gaussianReal_absolutelyContinuous (0 : ℝ)
        (v := (1 : NNReal)) (by norm_num)
  have hsing :
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) ({a} : Set ℝ) = 0 := by
    exact hac (by simp)
  exact measure_congr (Iio_ae_eq_Iic' hsing)

theorem prob_13_2_standardNormal_Ioi_eq_Ici (a : ℝ) :
    ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi a) =
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ici a) := by
  have hac :
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) ≪ (volume : Measure ℝ) := by
    simpa using
      ProbabilityTheory.gaussianReal_absolutelyContinuous (0 : ℝ)
        (v := (1 : NNReal)) (by norm_num)
  have hsing :
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) ({a} : Set ℝ) = 0 := by
    exact hac (by simp)
  exact measure_congr (Ioi_ae_eq_Ici' hsing)

/-- Standard normal left and right open tails have equal mass. -/
theorem prob_13_2_standardNormal_left_tail_mass_eq_right_tail_mass :
    ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iio (-(1 : ℝ))) =
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ)) := by
  calc
    ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iio (-(1 : ℝ))) =
        ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iic (-(1 : ℝ))) :=
      prob_13_2_standardNormal_Iio_eq_Iic (-(1 : ℝ))
    _ = ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ici (1 : ℝ)) := by
      have h := ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := (1 : NNReal))
      have hmeas : Measurable (fun x : ℝ => -x) := measurable_neg
      calc
        ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iic (-(1 : ℝ))) =
            Measure.map (fun x : ℝ => -x)
              (ProbabilityTheory.gaussianReal 0 (1 : NNReal))
              (Set.Iic (-(1 : ℝ))) := by
          rw [h]
          simp
        _ = ProbabilityTheory.gaussianReal 0 (1 : NNReal)
            ((fun x : ℝ => -x) ⁻¹' Set.Iic (-(1 : ℝ))) := by
          rw [Measure.map_apply hmeas measurableSet_Iic]
        _ = ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ici (1 : ℝ)) := by
          congr 1
          ext x
          simp
    _ = ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ)) :=
      (prob_13_2_standardNormal_Ioi_eq_Ici (1 : ℝ)).symm

theorem prob_13_2_standardNormal_left_tail_mass_toReal_eq_right_tail_mass_toReal :
    (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iio (-(1 : ℝ)))).toReal =
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ))).toReal := by
  rw [prob_13_2_standardNormal_left_tail_mass_eq_right_tail_mass]

/-- The left-tail conditional mean is the negative of the right-tail
conditional mean for the standard normal threshold at `1`. -/
theorem prob_13_2_negative_tail_mean_from_symmetry :
    ((∫ z in Set.Iio (-(1 : ℝ)),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) /
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Iio (-(1 : ℝ)))).toReal) =
      -((∫ z in Set.Ioi (1 : ℝ),
        z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) /
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal) (Set.Ioi (1 : ℝ))).toReal) := by
  rw [prob_13_2_standardNormal_left_tail_numerator,
    prob_13_2_standardNormal_right_tail_numerator,
    prob_13_2_standardNormal_left_tail_mass_toReal_eq_right_tail_mass_toReal]
  ring
