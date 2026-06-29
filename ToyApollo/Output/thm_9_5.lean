import Mathlib
import ToyApollo.Output.thm_7_7
import ToyApollo.Output.thm_9_5_kernel

/-
TASK ID: thm_9_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\begin{thmbox}{9.5}
\textbf{Inversion Formula.}
Let $X$ be a random variable on a probability space $(\Omega,\mathcal{F},P)$, and let $\phi_X(t)$ be the characteristic function of $X$. Denote the push-forward measure of $P$ by $\mu$. For $a<b$,
\[
\mu((a,b))+\frac{\mu(\{a\})}{2}+\frac{\mu(\{b\})}{2}
=\frac{1}{2\pi}\lim_{T\to\infty}
\int_{-T}^{T}\frac{e^{-ita}-e^{-itb}}{it}\phi_X(t)\,dt.
\]
\end{thmbox}

On the left-hand side of the equation in Theorem 9.5, $(a,b)$ denotes an open interval, and $\mu(\{a\})$ and $\mu(\{b\})$ are probabilities at the points $a$ and $b$, respectively. This formulation is necessary to account for possible discontinuities in the cumulative distribution function. If the cdf is continuous, then both $\mu(\{a\})$ and $\mu(\{b\})$ are zero, and $\mu((a,b))=\mu([a,b])$. The limit on the right-hand side is the Cauchy principal value of the integral, and its existence is part of the theorem.

In the proof we use the Dirichlet integral
\[
\lim_{T\to\infty}\int_0^T \frac{\sin u}{u}\,du=\frac{\pi}{2}.
\]
This limit is obtained from the Riemann integral of the function $(\sin u)/u$.

\textit{Proof}
For fixed $T$, consider
\[
I_T \coloneqq
\int_{-T}^{T}\frac{e^{-ita}-e^{-itb}}{it}\phi_X(t)\,dt
=\int_{-T}^{T}\int_{\mathbb{R}}
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}\,d\mu(x)\,dt.
\]
Using Theorem 9.4, we can bound the integrand by
\[
\left\lvert
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}
\right\rvert
=\left\lvert \frac{1}{t}(e^{it(b-a)}-1)\right\rvert
\leq b-a.
\]
Therefore, by Fubini theorem (Theorem 8.5),
\[
I_T=\int_{\mathbb{R}}\int_{-T}^{T}
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}\,dt\,d\mu(x).
\tag{9.1}
\]

Let $f(x,T)$ denote the inner integral in (9.1). The imaginary part of the integrand is odd and the real part is even, so integration over $[-T,T]$ gives
\[
f(x,T)
=2\int_0^T \frac{1}{t}\sin(t(b-x))\,dt
-2\int_0^T \frac{1}{t}\sin(t(a-x))\,dt.
\]
Changing variables gives
\[
f(x,T)
=2\int_{(a-x)T}^{(b-x)T}\frac{\sin u}{u}\,du.
\]
There are four cases. If $a<x<b$, then $f(x,T)\to 2\pi$. If $x=a$ or $x=b$, then $f(x,T)\to \pi$. If $x<a$ or $x>b$, then $f(x,T)\to 0$. Thus
\[
\lim_{T\to\infty} f(x,T)=
\begin{cases}
2\pi, & x\in(a,b),\\
\pi, & x=a\text{ or }x=b,\\
0, & \text{otherwise}.
\end{cases}
\]
The integral $\int_0^v (\sin u)/u\,du$ converges as $v\to\infty$ and is continuous as a function of $v$. Hence $\lvert f(x,T)\rvert$ is bounded by a constant independent of $x$ and $T$. Applying the complex version of the dominated convergence theorem (Theorem 7.6), we get
\[
\lim_{T\to\infty} I_T
=2\pi\int 1_{(a,b)}(x)\,d\mu(x)
+\pi\int 1_{\{a\}}(x)\,d\mu(x)
+\pi\int 1_{\{b\}}(x)\,d\mu(x).
\]
Dividing by $2\pi$ gives the inversion formula.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

/-- The DCT/Fubini assembly before dividing by `2π`. -/
def characteristicInversionLimitAssembly
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => characteristicInversionTruncation μ a b T)
    atTop
    (nhds ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b))

/-- The DCT limit after the source proof has moved the finite-`T` integral inside. -/
def characteristicInversionDCTInnerLimit
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => ∫ x, characteristicInversionInnerKernel a b x T ∂μ)
    atTop
    (nhds ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b))

/--
Hypotheses for the real-parameter `T -> atTop` DCT step actually needed by
Theorem 9.5. This is an interface bridge for the cutoff parameter, not a
replacement for the Dirichlet/sine-kernel proof obligations that establish the
pointwise limit and domination hypotheses.
-/
def characteristicInversionDCTAtTopHypotheses
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  ∃ Y : ℝ → ℝ,
    (∀ T : ℝ,
      AEStronglyMeasurable
        (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ) ∧
    Integrable Y μ ∧
    (∀ T : ℝ, ∀ᵐ x ∂μ,
      ‖characteristicInversionInnerKernel a b x T‖ ≤ Y x) ∧
    (∀ᵐ x ∂μ,
      Tendsto
        (fun T : ℝ => characteristicInversionInnerKernel a b x T)
        atTop
        (nhds (characteristicInversionKernelLimitValue a b x)))

/-- Package the DCT hypotheses from the three concrete ingredients used in
the source proof: measurability of each cutoff kernel, a uniform dominating
constant, and the pointwise kernel limit. -/
theorem characteristicInversionDCTAtTopHypotheses_of_pointwise_dominated
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ)
    (hmeas :
      ∀ T : ℝ,
        AEStronglyMeasurable
          (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ)
    (hdom : characteristicInversionKernelDominated a b)
    (hpoint :
      ∀ x : ℝ, characteristicInversionKernelPointwiseLimit a b x) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  rcases hdom with ⟨C, hC_nonneg, hbound⟩
  refine ⟨fun _ : ℝ => C, hmeas, integrable_const C, ?_, ?_⟩
  · intro T
    exact ae_of_all μ fun x => hbound x T
  · exact ae_of_all μ hpoint

/-- Conditional DCT package after the source kernel has been reduced to the
sine kernel. This removes another raw source-spine field modulo the remaining
Dirichlet, change-of-variables, and measurability bridges. -/
theorem characteristicInversionDCTAtTopHypotheses_of_dirichlet
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hlim : characteristicInversionDirichletIntegralLimit)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x)
    (hmeas :
      ∀ T : ℝ,
        AEStronglyMeasurable
          (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  have hdom : characteristicInversionKernelDominated a b :=
    characteristicInversionKernelDominated_of_dirichlet hlim hchange
  have hpoint :
      ∀ x : ℝ, characteristicInversionKernelPointwiseLimit a b x := by
    intro x
    exact characteristicInversionKernelFromSine_of_change a b x
      (hchange x)
      (characteristicInversionSineKernelLimit_of_dirichlet hlim hab)
  exact characteristicInversionDCTAtTopHypotheses_of_pointwise_dominated
    μ a b hmeas hdom hpoint

/-- Reconstruct the DCT package from the remaining two analytic bridges:
Dirichlet and change-of-variables. Measurability is no longer an independent
source-spine field. -/
theorem characteristicInversionDCTAtTopHypotheses_of_dirichlet_change
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hlim : characteristicInversionDirichletIntegralLimit)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  exact characteristicInversionDCTAtTopHypotheses_of_dirichlet μ hab hlim hchange
    (characteristicInversionInnerKernel_aestronglyMeasurable_of_change
      μ a b hchange)

/-- Apply the underlying filter-form dominated convergence theorem at `atTop`
for the real cutoff parameter. -/
theorem characteristicInversionDCTInnerLimit_of_atTop
    (μ : Measure ℝ) (a b : ℝ)
    (hhyp : characteristicInversionDCTAtTopHypotheses μ a b)
    (hid :
      ∫ x, characteristicInversionKernelLimitValue a b x ∂μ =
        (2 * Real.pi : ℂ) * characteristicInversionMass μ a b) :
    characteristicInversionDCTInnerLimit μ a b := by
  rcases hhyp with ⟨Y, hXm, hYint, hbound, hlim⟩
  have hdct :
      Tendsto
        (fun T : ℝ => ∫ x,
          characteristicInversionInnerKernel a b x T ∂μ)
        atTop
        (nhds (∫ x,
          characteristicInversionKernelLimitValue a b x ∂μ)) :=
    thm_7_DCT_filter μ
      (fun T x => characteristicInversionInnerKernel a b x T)
      (fun x => characteristicInversionKernelLimitValue a b x)
      Y atTop
      (Eventually.of_forall hXm) hYint
      (Eventually.of_forall hbound) hlim
  simpa [characteristicInversionDCTInnerLimit, hid] using hdct

/--
The limit-version DCT conclusion needed by the principal-value parameter `T`.
The existing Chapter 7 outputs record the textbook DCT references, but the
Chapter 9 cutoff proof needs the `T -> atTop` bridge above.
-/
def characteristicInversionDCTLimitVersion
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  characteristicInversionDCTInnerLimit μ a b

/-- The textbook inversion formula stated as a law-level `charFun` limit. -/
def CharacteristicInversionFormula (μ : Measure ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a < b →
    Tendsto
      (fun T : ℝ =>
        ((2 * Real.pi : ℂ)⁻¹) *
          characteristicInversionTruncation μ a b T)
      atTop
      (nhds (characteristicInversionMass μ a b))

/-- Integrating the endpoint-valued pointwise kernel gives the
endpoint-corrected mass appearing in the inversion formula. -/
theorem characteristicInversionKernelLimitValue_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b) :
    (∫ x, characteristicInversionKernelLimitValue a b x ∂μ) =
      (2 * Real.pi : ℂ) * characteristicInversionMass μ a b := by
  let f : ℝ → ℂ := (Ioo a b).indicator (fun _ : ℝ => (2 * Real.pi : ℂ))
  let g : ℝ → ℂ := ({a} : Set ℝ).indicator (fun _ : ℝ => (Real.pi : ℂ))
  let h : ℝ → ℂ := ({b} : Set ℝ).indicator (fun _ : ℝ => (Real.pi : ℂ))
  have hpoint : (fun x => characteristicInversionKernelLimitValue a b x) =
      (fun x => f x + g x + h x) := by
    funext x
    by_cases hinside : a < x ∧ x < b
    · have hxa : x ≠ a := ne_of_gt hinside.1
      have hxb : x ≠ b := ne_of_lt hinside.2
      simp [f, g, h, characteristicInversionKernelLimitValue, hinside, hxa, hxb]
    · by_cases hxa : x = a
      · have hxnotinside : x ∉ Ioo a b := by simp [hxa]
        simp [f, g, h, characteristicInversionKernelLimitValue,
          hxa, hab.ne]
      · by_cases hxb : x = b
        · have hxnotinside : x ∉ Ioo a b := by simp [hxb]
          simp [f, g, h, characteristicInversionKernelLimitValue,
            hxb, hab.ne']
        · have hxnotinside : x ∉ Ioo a b := by simpa using hinside
          simp [f, g, h, characteristicInversionKernelLimitValue,
            hinside, hxnotinside, hxa, hxb]
  rw [hpoint]
  have hf : Integrable f μ := by
    dsimp [f]
    exact (MeasureTheory.integrable_const (2 * Real.pi : ℂ)).indicator
      measurableSet_Ioo
  have hg : Integrable g μ := by
    dsimp [g]
    exact (MeasureTheory.integrable_const (Real.pi : ℂ)).indicator
      (MeasurableSet.singleton a)
  have hh : Integrable h μ := by
    dsimp [h]
    exact (MeasureTheory.integrable_const (Real.pi : ℂ)).indicator
      (MeasurableSet.singleton b)
  rw [MeasureTheory.integral_add (f := fun x => f x + g x) (g := h)
    (hf.add hg) hh]
  rw [MeasureTheory.integral_add (f := f) (g := g) hf hg]
  dsimp [f, g, h]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (2 * Real.pi : ℂ)) measurableSet_Ioo]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (Real.pi : ℂ)) (MeasurableSet.singleton a)]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (Real.pi : ℂ)) (MeasurableSet.singleton b)]
  have halg :
      μ.real (Ioo a b) • ((2 * Real.pi) : ℂ) +
          μ.real ({a} : Set ℝ) • (Real.pi : ℂ) +
        μ.real ({b} : Set ℝ) • (Real.pi : ℂ) =
          (2 * Real.pi : ℂ) * characteristicInversionMass μ a b := by
    simp [characteristicInversionMass]
    ring_nf
  simpa using halg

/--
The source-proof obligations for the inversion formula. This is still a repair
scaffold: the field names the Dirichlet obligation that must eventually be
proved rather than supplied as an assumption.
-/
structure CharacteristicInversionSourceSpine (μ : Measure ℝ) : Prop where
  dirichlet_limit :
    characteristicInversionDirichletIntegralLimit

/-- Assemble the truncation limit from the Fubini swap and the inner DCT limit. -/
theorem characteristicInversionLimitAssembly_of_sourceSpine
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_spine : CharacteristicInversionSourceSpine μ)
    ⦃a b : ℝ⦄ (hab : a < b) :
    characteristicInversionLimitAssembly μ a b := by
  have hswap :
      (fun T : ℝ => characteristicInversionTruncation μ a b T) =ᶠ[atTop]
      (fun T : ℝ => ∫ x, characteristicInversionInnerKernel a b x T ∂μ) :=
    (eventually_ge_atTop (0 : ℝ)).mono fun T hT =>
      characteristicInversionFubiniSwap_of_integrable_nonneg μ a b T hT
        (characteristicInversionFubiniIntegrable_of_finite μ a b T hab.le)
  have hchange :
      ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x := by
    intro x
    exact characteristicInversionKernelChangeOfVariables_of_translated a b x
  have hdct_hyp : characteristicInversionDCTAtTopHypotheses μ a b :=
    characteristicInversionDCTAtTopHypotheses_of_dirichlet_change μ hab
      h_spine.dirichlet_limit hchange
  have hinner : characteristicInversionDCTInnerLimit μ a b :=
    characteristicInversionDCTInnerLimit_of_atTop μ a b
      hdct_hyp
      (characteristicInversionKernelLimitValue_integral μ hab)
  exact hinner.congr' hswap.symm

/-- Divide the assembled `2π` limit by `2π`. -/
theorem characteristicInversionFormula_of_sourceSpine
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_spine : CharacteristicInversionSourceSpine μ) :
    CharacteristicInversionFormula μ := by
  intro a b hab
  have hlim :=
    (characteristicInversionLimitAssembly_of_sourceSpine μ h_spine hab).const_mul
      ((2 * Real.pi : ℂ)⁻¹)
  have hnonzero : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hscale :
      ((2 * Real.pi : ℂ)⁻¹) *
          ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b) =
        characteristicInversionMass μ a b := by
    calc
      ((2 * Real.pi : ℂ)⁻¹) *
          ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b)
          = (((2 * Real.pi : ℂ)⁻¹) * (2 * Real.pi : ℂ)) *
              characteristicInversionMass μ a b := by
            ring
      _ = 1 * characteristicInversionMass μ a b := by
            rw [inv_mul_cancel₀ hnonzero]
      _ = characteristicInversionMass μ a b := by
            rw [one_mul]
  rw [hscale] at hlim
  simpa [CharacteristicInversionFormula, characteristicInversionLimitAssembly]
    using hlim

/-- Theorem 9.5, exposed at the law level. The remaining source-spine package is
constructed internally from the textbook Dirichlet integral proof. -/
theorem thm_9_5 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    CharacteristicInversionFormula μ :=
  characteristicInversionFormula_of_sourceSpine μ
    ⟨characteristicInversionDirichletIntegralLimit_proof⟩
