import Mathlib
import ToyApollo.Output.thm_7_9

/-
TASK ID: ex_7_3_2
TYPE: Example_Proof
SOURCE PLAN: 27_chap7_stieltjes_integrals
TASK CONTENT:
\textbf{Example 7.3.2 (Expected Value of the Exponential Distribution)} \\
The probability density function of the exponential distribution is given by
\[
f(x)\triangleq \lambda e^{-\lambda x}\cdot 1_{[0,\infty)}(x),
\]
where $\lambda$ is a positive constant. We can create an LS measure on $\mathbb{R}$ from the Stieltjes measure function
\[
F(x)=
\begin{cases}
\int_{0}^{x} \lambda e^{-\lambda t}\, dt & \text{if } x\ge 0,\\
0 & \text{if } x<0.
\end{cases}
\]

Denote the resulting LS measure by $P$. Suppose we want to compute the mean $\int_{\mathbb{R}} x\, dP(x)$. Since the negative real number line has measure zero with respect to measure $P$, we may focus on the positive real number line. To apply Theorem 7.9, we check that the RS integral
\[
\int_{a}^{b} x\, dF(x)=\int_{a}^{b} x\lambda e^{-\lambda x}\, dx
\]
exists for all $0\le a<b$, and moreover, the improper integral $\int_{0}^{\infty} x\lambda e^{-\lambda x}\, dx$ exists and is equal to $1/\lambda$, which is a finite value. Therefore $\int_{[0,\infty)} x\, dP(x)=1/\lambda$.
-/

open MeasureTheory Set ProbabilityTheory

noncomputable section

private lemma exponentialPDFReal_eq (rate x : ℝ) :
    ProbabilityTheory.exponentialPDFReal rate x =
      if 0 ≤ x then rate * Real.exp (-(rate * x)) else 0 := by
  rw [ProbabilityTheory.exponentialPDFReal, ProbabilityTheory.gammaPDFReal]
  simp [Real.Gamma_one]

private lemma measurable_exponentialPDF (rate : ℝ) :
    Measurable (ProbabilityTheory.exponentialPDF rate) := by
  simpa [ProbabilityTheory.exponentialPDF] using
    ENNReal.measurable_ofReal.comp
      (ProbabilityTheory.measurable_exponentialPDFReal rate)

private lemma exponentialPDF_lt_top_ae (rate : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ProbabilityTheory.exponentialPDF rate x < ⊤ := by
  filter_upwards with x
  simp [ProbabilityTheory.exponentialPDF]

private lemma toReal_exponentialPDF {rate x : ℝ} (hrate : 0 < rate) :
    (ProbabilityTheory.exponentialPDF rate x).toReal =
      ProbabilityTheory.exponentialPDFReal rate x := by
  simp [ProbabilityTheory.exponentialPDF, ENNReal.toReal_ofReal,
    ProbabilityTheory.exponentialPDFReal_nonneg hrate x]

private lemma integrableOn_Ioi_id_mul_exp {rate : ℝ} (hrate : 0 < rate) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(rate * x))) (Ioi 0) := by
  simpa [Real.rpow_natCast] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := rate)
      (by norm_num) (by norm_num) hrate)

private lemma integrable_id_mul_exponentialPDFReal {rate : ℝ}
    (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x * ProbabilityTheory.exponentialPDFReal rate x) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine (integrableOn_zero :
      IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun ?_
      measurableSet_Iio
    intro x hx
    have hxlt : x < 0 := hx
    simp [exponentialPDFReal_eq, not_le_of_gt hxlt]
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hScaled :
        IntegrableOn
          (fun x : ℝ => rate * (x * Real.exp (-(rate * x)))) (Ioi 0) :=
      (integrableOn_Ioi_id_mul_exp hrate).const_mul rate
    refine hScaled.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    simp [exponentialPDFReal_eq, hx0, mul_assoc, mul_left_comm, mul_comm]

private lemma abs_mul_exponentialPDFReal_eq (rate : ℝ) :
    (fun x : ℝ => |x| * ProbabilityTheory.exponentialPDFReal rate x) =
      fun x => x * ProbabilityTheory.exponentialPDFReal rate x := by
  funext x
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx]
  · have hpdf : ProbabilityTheory.exponentialPDFReal rate x = 0 := by
      simp [exponentialPDFReal_eq, hx]
    simp [hpdf, abs_of_neg (lt_of_not_ge hx)]

private lemma integrable_abs_exponential {rate : ℝ} (hrate : 0 < rate) :
    Integrable (fun x : ℝ => |x|) (ProbabilityTheory.expMeasure rate) := by
  have hBase :
      Integrable
        (fun x : ℝ => |x| * (ProbabilityTheory.exponentialPDF rate x).toReal) := by
    rw [show
      (fun x : ℝ => |x| * (ProbabilityTheory.exponentialPDF rate x).toReal) =
        fun x : ℝ => |x| * ProbabilityTheory.exponentialPDFReal rate x by
          funext x
          rw [toReal_exponentialPDF hrate]]
    rw [abs_mul_exponentialPDFReal_eq rate]
    exact integrable_id_mul_exponentialPDFReal (rate := rate) hrate
  exact (integrable_withDensity_iff
    (measurable_exponentialPDF rate) (exponentialPDF_lt_top_ae rate)).2 hBase

private lemma id_mul_exponentialPDFReal_eq_indicator (rate : ℝ) :
    (fun x : ℝ => x * ProbabilityTheory.exponentialPDFReal rate x) =
      Set.indicator (Ioi (0 : ℝ))
        (fun x =>
          rate * (x ^ (1 : ℝ) * Real.exp (-(rate * x ^ (1 : ℝ))))) := by
  funext x
  by_cases hx : 0 < x
  · have hx0 : 0 ≤ x := le_of_lt hx
    simp [hx, exponentialPDFReal_eq, hx0, Real.rpow_one,
      mul_assoc, mul_left_comm, mul_comm]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    rcases lt_or_eq_of_le hxle with hxneg | rfl
    · simp [hx, exponentialPDFReal_eq, not_le_of_gt hxneg]
    · simp [hx, exponentialPDFReal_eq]

private lemma integral_Ioi_id_mul_exp {rate : ℝ} (hrate : 0 < rate) :
    ∫ x : ℝ in Ioi 0,
        x ^ (1 : ℝ) * Real.exp (-(rate * x ^ (1 : ℝ))) =
      rate ^ (-1 + -1 : ℝ) * Real.Gamma (1 + 1) := by
  simpa using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (q := (1 : ℝ)) (b := rate)
      (by norm_num) (by norm_num) hrate)

private lemma integral_id_mul_exponentialPDFReal {rate : ℝ}
    (hrate : 0 < rate) :
    ∫ x : ℝ, x * ProbabilityTheory.exponentialPDFReal rate x = 1 / rate := by
  calc
    ∫ x : ℝ, x * ProbabilityTheory.exponentialPDFReal rate x
        = ∫ x, Set.indicator (Ioi (0 : ℝ))
            (fun x =>
              rate * (x ^ (1 : ℝ) *
                Real.exp (-(rate * x ^ (1 : ℝ))))) x := by
            rw [id_mul_exponentialPDFReal_eq_indicator rate]
    _ = ∫ x : ℝ in Ioi 0,
          rate * (x ^ (1 : ℝ) *
            Real.exp (-(rate * x ^ (1 : ℝ)))) := by
          rw [integral_indicator measurableSet_Ioi]
    _ = rate * ∫ x : ℝ in Ioi 0,
          x ^ (1 : ℝ) * Real.exp (-(rate * x ^ (1 : ℝ))) := by
          rw [integral_const_mul]
    _ = rate * (rate ^ (-1 + -1 : ℝ) * Real.Gamma (1 + 1)) := by
          rw [integral_Ioi_id_mul_exp hrate]
    _ = 1 / rate := by
          norm_num [Real.Gamma_nat_eq_factorial]
          field_simp [hrate.ne']

private lemma integral_id_expMeasure {rate : ℝ} (hrate : 0 < rate) :
    ∫ x : ℝ, x ∂ProbabilityTheory.expMeasure rate = 1 / rate := by
  calc
    ∫ x : ℝ, x ∂ProbabilityTheory.expMeasure rate
        = ∫ x : ℝ,
            (ProbabilityTheory.exponentialPDF rate x).toReal * x := by
            simpa [ProbabilityTheory.expMeasure, smul_eq_mul, mul_comm] using
              (integral_withDensity_eq_integral_toReal_smul
                (μ := (volume : Measure ℝ))
                (f := ProbabilityTheory.exponentialPDF rate)
                (g := fun x : ℝ => x)
                (measurable_exponentialPDF rate)
                (exponentialPDF_lt_top_ae rate))
    _ = ∫ x : ℝ, x * ProbabilityTheory.exponentialPDFReal rate x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [toReal_exponentialPDF hrate]
          ring
    _ = 1 / rate := integral_id_mul_exponentialPDFReal hrate

private theorem ex_7_3_2_id_source_regular (F : StieltjesFunction ℝ) :
    Thm79FiniteDiscontinuityInputs F (fun x : ℝ => x) := by
  refine ⟨measurable_id, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b _hab
    constructor
    · exact ⟨b, by
        rintro y ⟨x, hx, rfl⟩
        exact hx.2⟩
    · exact ⟨a, by
        rintro y ⟨x, hx, rfl⟩
        exact hx.1⟩
  · intro a b _hab
    constructor
    · refine ⟨max |a| |b|, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact abs_le_max_abs_abs hx.1 hx.2
    · exact ⟨0, by
        rintro y ⟨x, _hx, rfl⟩
        exact abs_nonneg x⟩
  · intro a b _hab
    exact Thm11SourceRoute.finite_discontinuitySetOn_of_forall_continuousAt
      (fun x _hx => by
        simpa using (continuousAt_id : ContinuousAt (fun y : ℝ => y) x))
  · intro a b _hab
    exact Thm11SourceRoute.finite_discontinuitySetOn_of_forall_continuousAt
      (fun x _hx => by
        simpa using
          (continuous_abs.continuousAt : ContinuousAt (fun y : ℝ => |y|) x))
  · intro _a _b x _hab hx
    exact False.elim
      (hx.2 (by
        simpa using (continuousAt_id : ContinuousAt (fun y : ℝ => y) x)))
  · intro _a _b x _hab hx
    exact False.elim
      (hx.2 (by
        simpa using
          (continuous_abs.continuousAt : ContinuousAt (fun y : ℝ => |y|) x)))

/-- Example 7.3.2: the exponential law with rate `λ` has mean `1 / λ`, and
Theorem 7.9 identifies that LS expectation with the improper RS integral
against the associated cdf. -/
theorem ex_7_3_2 {rate : ℝ} (hrate : 0 < rate) :
    let P := ProbabilityTheory.expMeasure rate
    let F := ProbabilityTheory.cdf P
    ∃ hImp : ImproperRSIntegrable (fun x => x) F,
      (∫ x, x ∂P) = improperRSIntegral (fun x => x) F hImp ∧
      improperRSIntegral (fun x => x) F hImp = 1 / rate := by
  let P : Measure ℝ := ProbabilityTheory.expMeasure rate
  let F : StieltjesFunction ℝ := ProbabilityTheory.cdf P
  haveI : IsProbabilityMeasure P := by
    simpa [P] using
      ProbabilityTheory.isProbabilityMeasure_expMeasure (r := rate) hrate
  have hFmeasure : F.measure = P := by
    simpa [F] using (ProbabilityTheory.measure_cdf P)
  have hRegular : Thm79FiniteDiscontinuityInputs F (fun x : ℝ => x) :=
    ex_7_3_2_id_source_regular F
  have hIntAbs : Integrable (fun x : ℝ => |x|) F.measure := by
    simpa [hFmeasure, P] using integrable_abs_exponential (rate := rate) hrate
  rcases (thm_7_9 F (g := fun x => x) hRegular).2 hIntAbs with
    ⟨hImp, hEq⟩
  have hMean : ∫ x : ℝ, x ∂P = 1 / rate := by
    simpa [P] using integral_id_expMeasure (rate := rate) hrate
  refine ⟨hImp, ?_⟩
  constructor
  · simpa [hFmeasure] using hEq
  · calc
      improperRSIntegral (fun x => x) F hImp =
          ∫ x : ℝ, x ∂F.measure := by
        symm
        exact hEq
      _ = ∫ x : ℝ, x ∂P := by rw [hFmeasure]
      _ = 1 / rate := hMean
