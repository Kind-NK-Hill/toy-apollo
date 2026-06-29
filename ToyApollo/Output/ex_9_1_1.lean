import Mathlib
import ToyApollo.Output.thm_7_12
import ToyApollo.Output.def_9_2
import ToyApollo.Output.thm_9_2

/-
TASK ID: ex_9_1_1
TYPE: Example_Proof
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
\textbf{Example 9.1.1 (Moment Generating Function of Poisson Distribution)} \\
Suppose $X$ is a Poisson random variable with mean $\lambda$. The probability mass function is
\[
P(X=k)=\frac{\lambda^k}{k!}e^{-\lambda}, \qquad k=0,1,2,\ldots.
\]
Using the discrete version of the change-of-variable formula (Theorem 7.12), we can calculate the moment generating function as
\[
M_X(t)\coloneqq \mathbb{E}[e^{tX}]
=\sum_{k=0}^{\infty}e^{kt}\frac{\lambda^k}{k!}e^{-\lambda}
=e^{-\lambda}\sum_{k=0}^{\infty}\frac{(\lambda e^t)^k}{k!}
=e^{\lambda e^t-\lambda}.
\]
Thus $M_X(t)$ is defined for all $t$.

The first two moments of $X$ can be obtained by differentiating $M_X(t)$:
\[
\mathbb{E}[X] = M_X'(0)
=\left.e^{-\lambda}e^{\lambda e^t}\lambda e^t\right|_{t=0}
=\lambda,
\]
and
\[
\mathbb{E}[X^2]
=\left.\frac{d^2}{dt^2}M_X(t)\right|_{t=0}
=\left.e^{-\lambda}e^{\lambda e^t}\left((\lambda e^t)^2+\lambda e^t\right)\right|_{t=0}
=\lambda^2+\lambda.
\]
The variance of $X$ is thus $\mathbb{E}[X^2]-\mathbb{E}[X]^2=\lambda$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable abbrev poissonMGFFormula (lam : ℝ) (t : ℝ) : ℝ :=
  Real.exp (lam * Real.exp t - lam)

noncomputable abbrev poissonMGFSeries (lam : NNReal) (t : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp ((k : ℝ) * t) * poissonPMFReal lam k

theorem poissonMGFFormula_zero (lam : ℝ) :
    poissonMGFFormula lam 0 = 1 := by
  simp [poissonMGFFormula]

theorem poissonMGFSeries_eq_formula (lam : NNReal) (t : ℝ) :
    poissonMGFSeries lam t = poissonMGFFormula (lam : ℝ) t := by
  have hseries :
      (∑' k : ℕ, ((lam : ℝ) * Real.exp t) ^ k / k.factorial) =
        Real.exp ((lam : ℝ) * Real.exp t) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp t)).tsum_eq
  unfold poissonMGFSeries poissonMGFFormula
  calc
    (∑' k : ℕ, Real.exp ((k : ℝ) * t) * poissonPMFReal lam k) =
        ∑' k : ℕ,
          Real.exp (-(lam : ℝ)) *
            (((lam : ℝ) * Real.exp t) ^ k / k.factorial) := by
      apply tsum_congr
      intro k
      rw [poissonPMFReal, Real.exp_nat_mul]
      ring
    _ =
        Real.exp (-(lam : ℝ)) *
          (∑' k : ℕ, ((lam : ℝ) * Real.exp t) ^ k / k.factorial) := by
      rw [tsum_mul_left]
    _ = Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp t) := by
      rw [hseries]
    _ = Real.exp ((lam : ℝ) * Real.exp t - (lam : ℝ)) := by
      rw [← Real.exp_add]
      ring_nf

theorem poissonPMF_toReal (lam : NNReal) (n : ℕ) :
    ((poissonPMF lam) n).toReal = poissonPMFReal lam n := by
  symm
  simpa [poissonPMFReal_nonneg] using
    congrArg ENNReal.toReal (poissonPMFReal_ofReal_eq_poissonPMF lam n)

theorem poissonMGFSeries_summable (lam : NNReal) (t : ℝ) :
    Summable (fun k : ℕ => Real.exp ((k : ℝ) * t) * poissonPMFReal lam k) := by
  have hseries :
      Summable (fun k : ℕ => ((lam : ℝ) * Real.exp t) ^ k / k.factorial) :=
    (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp t)).summable
  have hweighted :
      Summable (fun k : ℕ =>
        Real.exp (-(lam : ℝ)) * (((lam : ℝ) * Real.exp t) ^ k / k.factorial)) :=
    hseries.mul_left (Real.exp (-(lam : ℝ)))
  refine hweighted.congr ?_
  intro k
  rw [poissonPMFReal, Real.exp_nat_mul]
  ring_nf

theorem poissonMGF_integrable (lam : NNReal) (t : ℝ) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (poissonMeasure lam) := by
  have hs : Summable (fun k : ℕ =>
      ((poissonPMF lam) k).toReal * ‖Real.exp (t * (k : ℝ))‖) := by
    refine (poissonMGFSeries_summable lam t).congr ?_
    intro k
    rw [poissonPMF_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    ring_nf
  rw [poissonMeasure, ← Measure.sum_smul_dirac ((poissonPMF lam).toMeasure)]
  refine MeasureTheory.integrable_sum_dirac ?_ ?_
  · intro k
    simpa [PMF.toMeasure_apply_singleton] using (poissonPMF lam).apply_ne_top k
  · simpa [PMF.toMeasure_apply_singleton] using hs

theorem poissonMGFIntegral_eq_series (lam : NNReal) (t : ℝ) :
    (∫ k : ℕ, Real.exp (t * (k : ℝ)) ∂poissonMeasure lam) =
      poissonMGFSeries lam t := by
  have hint : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (poissonMeasure lam) :=
    poissonMGF_integrable lam t
  unfold poissonMGFSeries poissonMeasure
  calc
    (∫ k : ℕ, Real.exp (t * (k : ℝ)) ∂(poissonPMF lam).toMeasure) =
        ∑' k : ℕ, ((poissonPMF lam) k).toReal • Real.exp (t * (k : ℝ)) := by
      exact PMF.integral_eq_tsum (poissonPMF lam)
        (fun k : ℕ => Real.exp (t * (k : ℝ))) hint
    _ = ∑' k : ℕ, Real.exp ((k : ℝ) * t) * poissonPMFReal lam k := by
      apply tsum_congr
      intro k
      rw [poissonPMF_toReal]
      simp [smul_eq_mul]
      ring_nf

theorem poissonMGF_eq_series (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
      poissonMGFSeries lam t := by
  simpa [mgf] using poissonMGFIntegral_eq_series lam t

theorem poissonMGF_eq_formula (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
      poissonMGFFormula (lam : ℝ) t := by
  rw [poissonMGF_eq_series, poissonMGFSeries_eq_formula]

theorem poissonRandomVariable_aemeasurable (lam : NNReal) :
    AEMeasurable (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) := by
  exact (MeasurableEmbedding.natCast (α := ℝ)).measurable.aemeasurable

theorem poissonMomentGeneratingFunction_eq_formula (lam : NNReal) (t : ℝ) :
    momentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
        (poissonRandomVariable_aemeasurable lam) t =
      ENNReal.ofReal (poissonMGFFormula (lam : ℝ) t) := by
  have hint : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (poissonMeasure lam) :=
    poissonMGF_integrable lam t
  have hnonneg : 0 ≤ᵐ[poissonMeasure lam] fun k : ℕ => Real.exp (t * (k : ℝ)) :=
    Filter.Eventually.of_forall fun _ => Real.exp_nonneg _
  rw [momentGeneratingFunction]
  calc
    (∫⁻ k : ℕ, ENNReal.ofReal (Real.exp (t * (k : ℝ))) ∂poissonMeasure lam) =
        ENNReal.ofReal
          (∫ k : ℕ, Real.exp (t * (k : ℝ)) ∂poissonMeasure lam) := by
      exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (poissonMGFFormula (lam : ℝ) t) := by
      rw [poissonMGFIntegral_eq_series, poissonMGFSeries_eq_formula]

theorem poissonHasMomentGeneratingFunction (lam : NNReal) :
    HasMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
      (poissonRandomVariable_aemeasurable lam) := by
  refine ⟨1, by norm_num, ?_⟩
  intro t _ht
  rw [poissonMomentGeneratingFunction_eq_formula]
  exact ENNReal.ofReal_lt_top

theorem poissonFiniteMomentGeneratingFunction_eq_formula (lam : NNReal) (t : ℝ) :
    finiteMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
        (poissonRandomVariable_aemeasurable lam) t =
      poissonMGFFormula (lam : ℝ) t := by
  calc
    finiteMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
        (poissonRandomVariable_aemeasurable lam) t =
        mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t := by
      exact thm_9_2_finiteMomentGeneratingFunction_eq_mgf_of_integrable
        (poissonRandomVariable_aemeasurable lam) (poissonMGF_integrable lam t)
    _ = poissonMGFFormula (lam : ℝ) t := poissonMGF_eq_formula lam t

theorem poissonMGFFormula_hasDerivAt (lam t : ℝ) :
    HasDerivAt (poissonMGFFormula lam)
      (Real.exp (lam * Real.exp t - lam) * (lam * Real.exp t)) t := by
  have h_mul : HasDerivAt (fun s : ℝ => lam * Real.exp s) (lam * Real.exp t) t := by
    simpa using (Real.hasDerivAt_exp t).const_mul lam
  have h_inner : HasDerivAt (fun s : ℝ => lam * Real.exp s - lam) (lam * Real.exp t) t := by
    simpa using h_mul.sub_const lam
  unfold poissonMGFFormula
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_inner.exp

theorem poissonMGFFormula_deriv (lam t : ℝ) :
    deriv (poissonMGFFormula lam) t =
      Real.exp (lam * Real.exp t - lam) * (lam * Real.exp t) := by
  exact (poissonMGFFormula_hasDerivAt lam t).deriv

theorem poissonMGFFormula_deriv_zero (lam : ℝ) :
    deriv (poissonMGFFormula lam) 0 = lam := by
  simpa using (poissonMGFFormula_hasDerivAt lam 0).deriv

theorem poissonMGFFormula_second_deriv_zero (lam : ℝ) :
    iteratedDeriv 2 (poissonMGFFormula lam) 0 = lam ^ 2 + lam := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have h_eq : deriv (poissonMGFFormula lam) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ => Real.exp (lam * Real.exp t - lam) * (lam * Real.exp t)) := by
    exact Filter.Eventually.of_forall (fun t => poissonMGFFormula_deriv lam t)
  rw [h_eq.deriv_eq]
  have h_inner0 : HasDerivAt (fun t : ℝ => lam * Real.exp t - lam) lam 0 := by
    have h_mul : HasDerivAt (fun t : ℝ => lam * Real.exp t) (lam * Real.exp 0) 0 := by
      simpa using (Real.hasDerivAt_exp 0).const_mul lam
    simpa using h_mul.sub_const lam
  have h_exp0 : HasDerivAt (fun t : ℝ => Real.exp (lam * Real.exp t - lam)) lam 0 := by
    simpa using h_inner0.exp
  have h_mul0 : HasDerivAt (fun t : ℝ => lam * Real.exp t) lam 0 := by
    simpa using (Real.hasDerivAt_exp 0).const_mul lam
  have h_prod := h_exp0.mul h_mul0
  convert h_prod.deriv using 1
  simp [pow_two]

theorem poissonMGFFormula_variance_value (lam : ℝ) :
    (lam ^ 2 + lam) - lam ^ 2 = lam := by
  ring

theorem poissonMGFFormula_first_two_moments (lam : NNReal) :
    deriv (poissonMGFFormula (lam : ℝ)) 0 = (lam : ℝ) ∧
      iteratedDeriv 2 (poissonMGFFormula (lam : ℝ)) 0 = (lam : ℝ) ^ 2 + (lam : ℝ) ∧
        ((lam : ℝ) ^ 2 + (lam : ℝ)) - (lam : ℝ) ^ 2 = (lam : ℝ) := by
  exact
    ⟨poissonMGFFormula_deriv_zero (lam : ℝ),
      poissonMGFFormula_second_deriv_zero (lam : ℝ),
      poissonMGFFormula_variance_value (lam : ℝ)⟩

theorem poissonMGF_moment_recovery (lam : NNReal) (n : ℕ) :
    rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) n =
      iteratedDeriv n
        (finiteMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
          (poissonRandomVariable_aemeasurable lam)) 0 := by
  exact (thm_9_2 (poissonRandomVariable_aemeasurable lam)
    (poissonHasMomentGeneratingFunction lam) n).2

theorem poissonMean_eq_lambda (lam : NNReal) :
    rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1 = (lam : ℝ) := by
  rw [poissonMGF_moment_recovery (lam := lam) (n := 1)]
  have hfun :
      finiteMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
        (poissonRandomVariable_aemeasurable lam) = poissonMGFFormula (lam : ℝ) := by
    funext t
    exact poissonFiniteMomentGeneratingFunction_eq_formula lam t
  rw [hfun]
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    poissonMGFFormula_deriv_zero (lam : ℝ)

theorem poissonSecondMoment_eq (lam : NNReal) :
    rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2 =
      (lam : ℝ) ^ 2 + (lam : ℝ) := by
  rw [poissonMGF_moment_recovery (lam := lam) (n := 2)]
  have hfun :
      finiteMomentGeneratingFunction (poissonMeasure lam) (fun k : ℕ => (k : ℝ))
        (poissonRandomVariable_aemeasurable lam) = poissonMGFFormula (lam : ℝ) := by
    funext t
    exact poissonFiniteMomentGeneratingFunction_eq_formula lam t
  rw [hfun]
  exact poissonMGFFormula_second_deriv_zero (lam : ℝ)

theorem poissonVarianceFromMoments_eq_lambda (lam : NNReal) :
    rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2 -
        (rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1) ^ 2 =
      (lam : ℝ) := by
  rw [poissonSecondMoment_eq, poissonMean_eq_lambda]
  ring

theorem ex_9_1_1 (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
        Real.exp ((lam : ℝ) * Real.exp t - (lam : ℝ)) ∧
      rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1 = (lam : ℝ) ∧
        rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2 =
            (lam : ℝ) ^ 2 + (lam : ℝ) ∧
          rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2 -
              (rthMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1) ^ 2 =
            (lam : ℝ) := by
  exact
    ⟨by simpa [poissonMGFFormula] using poissonMGF_eq_formula lam t,
      poissonMean_eq_lambda lam,
      poissonSecondMoment_eq lam,
      poissonVarianceFromMoments_eq_lambda lam⟩
