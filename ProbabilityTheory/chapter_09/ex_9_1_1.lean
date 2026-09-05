/-
TASK ID: ex_9_1_1
TYPE: Example_Proof
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_09.def_9_2
import ProbabilityTheory.chapter_09.thm_9_2




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
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  refine hs.congr ?_
  intro k
  rw [poissonPMF_toReal, poissonPMFReal]

theorem poissonMGFIntegral_eq_series (lam : NNReal) (t : ℝ) :
    (∫ k : ℕ, Real.exp (t * (k : ℝ)) ∂poissonMeasure lam) =
      poissonMGFSeries lam t := by
  have hint : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (poissonMeasure lam) :=
    poissonMGF_integrable lam t
  unfold poissonMGFSeries
  calc
    (∫ k : ℕ, Real.exp (t * (k : ℝ)) ∂poissonMeasure lam) =
        ∑' k : ℕ,
          (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ k / k.factorial) •
            Real.exp (t * (k : ℝ)) := by
      exact ProbabilityTheory.integral_poissonMeasure lam
        (fun k : ℕ => Real.exp (t * (k : ℝ)))
    _ = ∑' k : ℕ, Real.exp ((k : ℝ) * t) * poissonPMFReal lam k := by
      apply tsum_congr
      intro k
      rw [poissonPMFReal]
      simp only [smul_eq_mul]
      ring_nf

theorem poissonMGF_eq_series (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
      poissonMGFSeries lam t := by
  simpa [mgf] using poissonMGFIntegral_eq_series lam t

theorem poissonMGF_eq_formula (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
      poissonMGFFormula (lam : ℝ) t := by
  rw [poissonMGF_eq_series, poissonMGFSeries_eq_formula]

theorem poissonRandomVariable_measurable :
    Measurable (fun k : ℕ => (k : ℝ)) :=
  (MeasurableEmbedding.natCast (α := ℝ)).measurable

theorem poissonRandomVariable_aemeasurable (lam : NNReal) :
    AEMeasurable (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) :=
  poissonRandomVariable_measurable.aemeasurable

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
  change deriv
    ((fun t : ℝ => Real.exp (lam * Real.exp t - lam)) *
      (fun t : ℝ => lam * Real.exp t)) 0 =
    lam ^ 2 + lam
  simpa [pow_two] using h_prod.deriv

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

theorem poissonFiniteAbsMoment (lam : NNReal) (n : ℕ) :
    FiniteAbsMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) n :=
  thm_9_2_finiteAbsMoment poissonRandomVariable_measurable
    (poissonRandomVariable_aemeasurable lam)
    (poissonHasMomentGeneratingFunction lam) n

theorem poissonMGF_moment_recovery (lam : NNReal) (n : ℕ) :
    generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) n
        (poissonFiniteAbsMoment lam n) =
      iteratedDeriv n
        (mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam)) 0 := by
  exact (thm_9_2 poissonRandomVariable_measurable
    (poissonRandomVariable_aemeasurable lam)
    (poissonHasMomentGeneratingFunction lam) n).2

theorem poissonMean_eq_lambda (lam : NNReal) :
    generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1
        (poissonFiniteAbsMoment lam 1) = (lam : ℝ) := by
  rw [poissonMGF_moment_recovery (lam := lam) (n := 1)]
  have hfun :
      mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) =
        poissonMGFFormula (lam : ℝ) := by
    funext t
    exact poissonMGF_eq_formula lam t
  rw [hfun]
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    poissonMGFFormula_deriv_zero (lam : ℝ)

theorem poissonSecondMoment_eq (lam : NNReal) :
    generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2
        (poissonFiniteAbsMoment lam 2) =
      (lam : ℝ) ^ 2 + (lam : ℝ) := by
  rw [poissonMGF_moment_recovery (lam := lam) (n := 2)]
  have hfun :
      mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) =
        poissonMGFFormula (lam : ℝ) := by
    funext t
    exact poissonMGF_eq_formula lam t
  rw [hfun]
  exact poissonMGFFormula_second_deriv_zero (lam : ℝ)

theorem poissonVarianceFromMoments_eq_lambda (lam : NNReal) :
    generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2
          (poissonFiniteAbsMoment lam 2) -
        (generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1
          (poissonFiniteAbsMoment lam 1)) ^ 2 =
      (lam : ℝ) := by
  rw [poissonSecondMoment_eq, poissonMean_eq_lambda]
  ring

theorem ex_9_1_1 (lam : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) t =
        Real.exp ((lam : ℝ) * Real.exp t - (lam : ℝ)) ∧
      generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1
          (poissonFiniteAbsMoment lam 1) = (lam : ℝ) ∧
        generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2
            (poissonFiniteAbsMoment lam 2) =
            (lam : ℝ) ^ 2 + (lam : ℝ) ∧
          generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 2
                (poissonFiniteAbsMoment lam 2) -
              (generalMoment (poissonMeasure lam) (fun k : ℕ => (k : ℝ)) 1
                (poissonFiniteAbsMoment lam 1)) ^ 2 =
            (lam : ℝ) := by
  exact
    ⟨by simpa [poissonMGFFormula] using poissonMGF_eq_formula lam t,
      poissonMean_eq_lambda lam,
      poissonSecondMoment_eq lam,
      poissonVarianceFromMoments_eq_lambda lam⟩
