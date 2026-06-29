/-
TASK ID: ex_5_2_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_5_4

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable def gaussianPdf (σ x : ℝ) : ℝ :=
  (1 / (Real.sqrt (2 * Real.pi) * σ)) * Real.exp (-(x ^ 2) / (2 * σ ^ 2))

noncomputable def zeroCorrJointGaussianPdf (σ1 σ2 x1 x2 : ℝ) : ℝ :=
  gaussianPdf σ1 x1 * gaussianPdf σ2 x2

theorem zeroCorrJointGaussianPdf_factorizes (σ1 σ2 x1 x2 : ℝ) :
    zeroCorrJointGaussianPdf σ1 σ2 x1 x2 =
      gaussianPdf σ1 x1 * gaussianPdf σ2 x2 := by
  rfl

theorem ex_5_2_1 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X1 X2 : Ω → ℝ) (hX1 : Measurable X1) (hX2 : Measurable X2)
    (σ1 σ2 : ℝ)
    (jointDensity : ℝ → ℝ → ℝ) (marginal1 marginal2 : ℝ → ℝ)
    (hJointGaussian :
      ∀ x1 x2 : ℝ,
        jointDensity x1 x2 = zeroCorrJointGaussianPdf σ1 σ2 x1 x2)
    (hMarginal1 :
      ∀ x : ℝ, marginal1 x = gaussianPdf σ1 x)
    (hMarginal2 :
      ∀ x : ℝ, marginal2 x = gaussianPdf σ2 x)
    (hCdfFactorization :
      ∀ x y : ℝ,
        jointCDF μ X1 X2 x y = marginalCDF μ X1 x * marginalCDF μ X2 y) :
    (∀ x1 x2 : ℝ, jointDensity x1 x2 = marginal1 x1 * marginal2 x2) ∧
      ProbabilityTheory.IndepFun X1 X2 μ := by
  refine ⟨?_, ?_⟩
  · intro x1 x2
    rw [hJointGaussian, hMarginal1, hMarginal2]
    exact zeroCorrJointGaussianPdf_factorizes σ1 σ2 x1 x2
  · exact (thm_5_4 μ X1 X2 hX1 hX2).2 hCdfFactorization

section Counterexample

def signFun : Bool → ℝ := fun b => if b then 1 else -1

noncomputable def signMeasure : Measure Bool :=
  (PMF.bernoulli (1 / 2) (by norm_num : (1 : ℝ≥0) / 2 ≤ 1)).toMeasure

noncomputable instance : IsProbabilityMeasure signMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

noncomputable def gaussianMeasure : Measure ℝ := ProbabilityTheory.gaussianReal 0 1

noncomputable instance : IsProbabilityMeasure gaussianMeasure := by
  dsimp [gaussianMeasure]
  infer_instance

noncomputable def counterMeasure : Measure (ℝ × Bool) :=
  gaussianMeasure.prod signMeasure

noncomputable instance : IsProbabilityMeasure counterMeasure := by
  dsimp [counterMeasure]
  infer_instance

def counterX : ℝ × Bool → ℝ := Prod.fst

def counterU : ℝ × Bool → ℝ := signFun ∘ Prod.snd

def counterY : ℝ × Bool → ℝ := fun ω => counterU ω * counterX ω

lemma counterU_measurable : Measurable counterU := by
  have hsign : Measurable signFun := measurable_of_finite signFun
  simpa [counterU] using hsign.comp measurable_snd

lemma counterY_measurable : Measurable counterY := by
  simpa [counterY] using counterU_measurable.mul measurable_fst

lemma signMeasure_true : signMeasure {true} = (1 / 2 : ℝ≥0∞) := by
  simp [signMeasure, PMF.bernoulli_apply]

lemma signMeasure_false : signMeasure {false} = (1 / 2 : ℝ≥0∞) := by
  simp [signMeasure, PMF.bernoulli_apply]

lemma counterX_hasLaw : ProbabilityTheory.HasLaw counterX gaussianMeasure counterMeasure := by
  simpa [counterX, counterMeasure, gaussianMeasure] using
    (MeasureTheory.measurePreserving_fst (μ := gaussianMeasure) (ν := signMeasure)).hasLaw

lemma counterX_indep_counterBool :
    ProbabilityTheory.IndepFun counterX Prod.snd counterMeasure := by
  simpa [counterX, counterMeasure] using
    (ProbabilityTheory.indepFun_prod (μ := gaussianMeasure) (ν := signMeasure)
      (X := id) (Y := id) measurable_id measurable_id)

lemma counterX_indep_counterU :
    ProbabilityTheory.IndepFun counterX counterU counterMeasure := by
  have hsign : Measurable signFun := measurable_of_finite signFun
  simpa [counterU] using
    counterX_indep_counterBool.comp measurable_id hsign

lemma counterY_map_eq : counterMeasure.map counterY = gaussianMeasure := by
  ext s hs
  have hsneg : MeasurableSet ((fun x : ℝ => -x) ⁻¹' s) := by
    simpa using measurable_neg hs
  have hsplit :
      counterY ⁻¹' s =
        (s ×ˢ ({true} : Set Bool)) ∪ (((fun x : ℝ => -x) ⁻¹' s) ×ˢ ({false} : Set Bool)) := by
    ext ω
    rcases ω with ⟨x, b⟩
    by_cases hb : b = true
    · subst hb
      simp [counterY, counterU, signFun, counterX]
    · have hb' : b = false := by cases b <;> simp_all
      subst hb'
      simp [counterY, counterU, signFun, counterX]
  have hmeas₂ : MeasurableSet (((fun x : ℝ => -x) ⁻¹' s) ×ˢ ({false} : Set Bool)) :=
    hsneg.prod (measurableSet_singleton false)
  rw [Measure.map_apply counterY_measurable hs, hsplit]
  have hdisj :
      Disjoint (s ×ˢ ({true} : Set Bool))
        (((fun x : ℝ => -x) ⁻¹' s) ×ˢ ({false} : Set Bool)) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω1 hω2
    have : true = false := by simpa using hω1.2.symm.trans hω2.2
    cases this
  rw [measure_union hdisj hmeas₂]
  simp [counterMeasure]
  have hneg :
      gaussianMeasure (-s) = gaussianMeasure s := by
    simpa [gaussianMeasure, Measure.map_apply measurable_neg hs] using
      congrArg (fun ν : Measure ℝ => ν s) (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := 1))
  rw [signMeasure_true, signMeasure_false, hneg, ← mul_add]
  have hhalf : ((1 / 2 : ℝ≥0∞) + 1 / 2) = 1 := by
    simpa [one_div] using (ENNReal.inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1)
  rw [hhalf, mul_one]

lemma counterY_hasLaw : ProbabilityTheory.HasLaw counterY gaussianMeasure counterMeasure where
  aemeasurable := counterY_measurable.aemeasurable
  map_eq := counterY_map_eq

lemma counterX_hasGaussianLaw : ProbabilityTheory.HasGaussianLaw counterX counterMeasure where
  isGaussian_map := by
    rw [counterX_hasLaw.map_eq, gaussianMeasure]
    infer_instance

lemma counterY_hasGaussianLaw : ProbabilityTheory.HasGaussianLaw counterY counterMeasure where
  isGaussian_map := by
    rw [counterY_hasLaw.map_eq, gaussianMeasure]
    infer_instance

lemma counterU_values (ω : ℝ × Bool) : counterU ω = 1 ∨ counterU ω = -1 := by
  rcases ω with ⟨x, b⟩
  cases b <;> simp [counterU, signFun]

lemma counterU_preimage_one :
    counterU ⁻¹' ({1} : Set ℝ) = Prod.snd ⁻¹' ({true} : Set Bool) := by
  ext ω
  rcases ω with ⟨x, b⟩
  cases b <;> norm_num [counterU, signFun]

lemma counterU_preimage_negOne :
    counterU ⁻¹' ({-1} : Set ℝ) = Prod.snd ⁻¹' ({false} : Set Bool) := by
  ext ω
  rcases ω with ⟨x, b⟩
  cases b <;> norm_num [counterU, signFun]

lemma counterU_measure_one : counterMeasure (counterU ⁻¹' ({1} : Set ℝ)) = (1 / 2 : ℝ≥0∞) := by
  rw [counterU_preimage_one, ← Measure.map_apply measurable_snd (measurableSet_singleton true)]
  simp [counterMeasure, signMeasure_true]

lemma counterU_measure_negOne : counterMeasure (counterU ⁻¹' ({-1} : Set ℝ)) = (1 / 2 : ℝ≥0∞) := by
  rw [counterU_preimage_negOne, ← Measure.map_apply measurable_snd (measurableSet_singleton false)]
  simp [counterMeasure, signMeasure_false]

lemma signFun_integrable : Integrable signFun signMeasure := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (show AEStronglyMeasurable signFun signMeasure from
      (measurable_of_finite signFun).aestronglyMeasurable) ?_
  filter_upwards with b
  cases b <;> simp [signFun]

lemma integral_signFun_signMeasure : ∫ b, signFun b ∂signMeasure = 0 := by
  rw [signMeasure, PMF.integral_eq_sum]
  norm_num [signFun, PMF.bernoulli_apply]

lemma counterU_integrable : Integrable counterU counterMeasure := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    counterU_measurable.aestronglyMeasurable ?_
  filter_upwards with ω
  rcases counterU_values ω with hω | hω <;> simp [hω]

lemma counterU_integral : ∫ ω, counterU ω ∂counterMeasure = 0 := by
  have hsndLaw : ProbabilityTheory.HasLaw Prod.snd signMeasure counterMeasure := by
    simpa [counterMeasure] using
      (MeasureTheory.measurePreserving_snd (μ := gaussianMeasure) (ν := signMeasure)).hasLaw
  calc
    ∫ ω, counterU ω ∂counterMeasure = ∫ b, signFun b ∂signMeasure := by
      simpa [counterU] using
        hsndLaw.integral_comp signFun_integrable.aestronglyMeasurable
    _ = 0 := integral_signFun_signMeasure

lemma counterX_integral : ∫ ω, counterX ω ∂counterMeasure = 0 := by
  rw [counterX_hasLaw.integral_eq]
  simp [gaussianMeasure]

lemma counterY_integral : ∫ ω, counterY ω ∂counterMeasure = 0 := by
  rw [counterY_hasLaw.integral_eq]
  simp [gaussianMeasure]

lemma counterU_indep_counterXsq :
    ProbabilityTheory.IndepFun counterU (fun ω => counterX ω ^ 2) counterMeasure := by
  have hpow : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  simpa [counterU] using counterX_indep_counterU.symm.comp measurable_id hpow

lemma counterXsq_integrable : Integrable (fun ω => counterX ω ^ 2) counterMeasure := by
  simpa using counterX_hasGaussianLaw.memLp_two.integrable_sq

lemma counterUXsq_integral : ∫ ω, counterU ω * counterX ω ^ 2 ∂counterMeasure = 0 := by
  calc
    ∫ ω, counterU ω * counterX ω ^ 2 ∂counterMeasure =
      (∫ ω, counterU ω ∂counterMeasure) * (∫ ω, counterX ω ^ 2 ∂counterMeasure) := by
        exact counterU_indep_counterXsq.integral_mul_eq_mul_integral
          counterU_integrable.aestronglyMeasurable counterXsq_integrable.aestronglyMeasurable
    _ = 0 := by rw [counterU_integral, zero_mul]

lemma counter_cov_zero : cov[counterX, counterY; counterMeasure] = 0 := by
  have hX2 : MemLp counterX 2 counterMeasure := counterX_hasGaussianLaw.memLp_two
  have hY2 : MemLp counterY 2 counterMeasure := counterY_hasGaussianLaw.memLp_two
  rw [ProbabilityTheory.covariance_eq_sub hX2 hY2]
  have hXY : ∫ ω, counterX ω * counterY ω ∂counterMeasure = 0 := by
    calc
      ∫ ω, counterX ω * counterY ω ∂counterMeasure =
          ∫ ω, counterU ω * counterX ω ^ 2 ∂counterMeasure := by
            congr with ω
            ring_nf
            simp [counterY, counterU, counterX, signFun, pow_two]
      _ = 0 := counterUXsq_integral
  rw [show ∫ x, (counterX * counterY) x ∂counterMeasure = 0 by simpa using hXY,
    counterX_integral, counterY_integral]
  ring

def counterSum : ℝ × Bool → ℝ := fun ω => counterX ω + counterY ω

lemma counterSum_zero_preimage :
    counterSum ⁻¹' ({0} : Set ℝ) =
      (({0} : Set ℝ) ×ˢ ({true} : Set Bool)) ∪ ((Set.univ : Set ℝ) ×ˢ ({false} : Set Bool)) := by
  ext ω
  rcases ω with ⟨x, b⟩
  cases b <;> simp [counterSum, counterY, counterU, counterX, signFun]

lemma counterSum_zero_mass :
    counterMeasure.map counterSum ({0} : Set ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (by
      simpa [counterSum] using measurable_fst.add counterY_measurable)
    (measurableSet_singleton 0), counterSum_zero_preimage]
  have hmeas₂ : MeasurableSet (((Set.univ : Set ℝ)) ×ˢ ({false} : Set Bool)) := by measurability
  have hdisj :
      Disjoint ((({0} : Set ℝ) ×ˢ ({true} : Set Bool)))
        (((Set.univ : Set ℝ)) ×ˢ ({false} : Set Bool)) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω1 hω2
    have : true = false := by simpa using hω1.2.symm.trans hω2.2
    cases this
  have hAtomZero : counterMeasure ((({0} : Set ℝ) ×ˢ ({true} : Set Bool))) = 0 := by
    haveI : NoAtoms gaussianMeasure := by
      simpa [gaussianMeasure] using
        (ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero)
    have hNoAtoms : NoAtoms (gaussianMeasure.prod signMeasure) := by infer_instance
    simpa [counterMeasure, Set.singleton_prod_singleton] using hNoAtoms.measure_singleton (0, true)
  rw [measure_union hdisj hmeas₂, hAtomZero]
  simp [counterMeasure, signMeasure_false]

lemma counter_not_jointlyGaussian :
    ¬ ProbabilityTheory.HasGaussianLaw (fun ω => (counterX ω, counterY ω)) counterMeasure := by
  intro hJoint
  let Z : (ℝ × Bool) → ℝ := fun ω => counterX ω + counterY ω
  let ν : Measure ℝ := counterMeasure.map Z
  let m : ℝ := ν[id]
  let v : ℝ≥0 := Var[id; ν].toNNReal
  have hZ : ProbabilityTheory.HasGaussianLaw Z counterMeasure := by
    simpa [Z] using hJoint.fun_add
  have hAtom :
      ν ({0} : Set ℝ) = (1 / 2 : ℝ≥0∞) := by
    simpa [ν, Z] using counterSum_zero_mass
  have hGaussAt0 :
      ν ({0} : Set ℝ) = ProbabilityTheory.gaussianReal m v ({0} : Set ℝ) := by
    simpa [ν, m, v] using congrArg (fun ρ : Measure ℝ => ρ ({0} : Set ℝ))
      (ProbabilityTheory.IsGaussian.eq_gaussianReal ν hZ.isGaussian_map)
  rw [hAtom] at hGaussAt0
  by_cases hv : v = 0
  · by_cases hm : m = 0
    · have hOne : ProbabilityTheory.gaussianReal m v ({0} : Set ℝ) = 1 := by
        rw [hv, ProbabilityTheory.gaussianReal_zero_var]
        simp [hm]
      rw [hOne] at hGaussAt0
      norm_num at hGaussAt0
    · have hZero : ProbabilityTheory.gaussianReal m v ({0} : Set ℝ) = 0 := by
        rw [hv, ProbabilityTheory.gaussianReal_zero_var]
        simp [hm]
      rw [hZero] at hGaussAt0
      norm_num at hGaussAt0
  · have hNoAtoms : NoAtoms (ProbabilityTheory.gaussianReal m v) :=
      ProbabilityTheory.noAtoms_gaussianReal (μ := m) (v := v) hv
    have hZero : ProbabilityTheory.gaussianReal m v ({0} : Set ℝ) = 0 := by
      simpa using hNoAtoms.measure_singleton 0
    rw [hZero] at hGaussAt0
    norm_num at hGaussAt0

theorem gaussianMarginal_counterexample_shape :
    ProbabilityTheory.IndepFun counterX counterU counterMeasure ∧
      (counterY = fun ω => counterU ω * counterX ω) ∧
      (∀ ω : ℝ × Bool, counterU ω = 1 ∨ counterU ω = -1) ∧
      counterMeasure (counterU ⁻¹' ({1} : Set ℝ)) = (1 / 2 : ℝ≥0∞) ∧
      counterMeasure (counterU ⁻¹' ({-1} : Set ℝ)) = (1 / 2 : ℝ≥0∞) ∧
      ProbabilityTheory.HasLaw counterX gaussianMeasure counterMeasure ∧
      ProbabilityTheory.HasLaw counterY gaussianMeasure counterMeasure ∧
      cov[counterX, counterY; counterMeasure] = 0 ∧
      ¬ ProbabilityTheory.HasGaussianLaw (fun ω => (counterX ω, counterY ω)) counterMeasure ∧
      ¬ ProbabilityTheory.IndepFun counterX counterY counterMeasure := by
  refine ⟨counterX_indep_counterU, rfl, counterU_values, counterU_measure_one,
    counterU_measure_negOne, counterX_hasLaw, counterY_hasLaw, counter_cov_zero,
    counter_not_jointlyGaussian, ?_⟩
  intro hIndep
  exact counter_not_jointlyGaussian (hIndep.hasGaussianLaw counterX_hasGaussianLaw counterY_hasGaussianLaw)

end Counterexample
