/-
TASK ID: prob_14_10
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.prob_14_8
import ProbabilityTheory.chapter_14.def_14_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology
open scoped Polynomial

noncomputable section

 
def prob_14_10_momentOfLaw (P : ProbabilityMeasure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂(P : Measure ℝ)

 
def prob_14_10_momentConvergence
    (laws : ℕ → ProbabilityMeasure ℝ) (targetLaw : ProbabilityMeasure ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Tendsto (fun n : ℕ => prob_14_10_momentOfLaw (laws n) k) atTop
      (𝓝 (prob_14_10_momentOfLaw targetLaw k))



def prob_14_10_clippedPower
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => ((Set.projIcc (-c) c (by linarith) x : ℝ) ^ k))
    (by fun_prop)
    (c ^ k)
    (by
      intro x
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_le.mpr (Set.projIcc (-c) c (by linarith) x).property) k)

theorem prob_14_10_clippedPower_eq_pow
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) {x : ℝ} (hx : |x| ≤ c) :
    prob_14_10_clippedPower c hc k x = x ^ k := by
  have hxIcc : x ∈ Icc (-c) c := abs_le.mp hx
  simp [prob_14_10_clippedPower, Set.projIcc_of_mem (by linarith) hxIcc]

theorem prob_14_10_integral_clippedPower_eq_moment
    (P : ProbabilityMeasure ℝ) (c : ℝ) (hc : 0 ≤ c) (k : ℕ)
    (hP : (P : Measure ℝ) {x : ℝ | |x| ≤ c} = 1) :
    ∫ x, prob_14_10_clippedPower c hc k x ∂(P : Measure ℝ) =
      prob_14_10_momentOfLaw P k := by
  unfold prob_14_10_momentOfLaw
  refine integral_congr_ae ?_
  have hsmeas : MeasurableSet {x : ℝ | |x| ≤ c} := by
    exact continuous_abs.measurable measurableSet_Iic
  have hmem : {x : ℝ | |x| ≤ c} ∈ ae (P : Measure ℝ) := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hsmeas).2 hP
  filter_upwards [hmem] with x hx
  exact prob_14_10_clippedPower_eq_pow c hc k hx



structure prob_14_10_BoundedMomentSetup where
  laws : ℕ → ProbabilityMeasure ℝ
  targetLaw : ProbabilityMeasure ℝ
  c : ℝ
  c_nonneg : 0 ≤ c
  uniformly_bounded :
    ∀ n : ℕ, (laws n : Measure ℝ) {x : ℝ | |x| ≤ c} = 1
  target_bounded :
    (targetLaw : Measure ℝ) {x : ℝ | |x| ≤ c} = 1

theorem prob_14_10_integrable_pow_of_bounded
    (P : ProbabilityMeasure ℝ) (c : ℝ) (hc : 0 ≤ c) (k : ℕ)
    (hP : (P : Measure ℝ) {x : ℝ | |x| ≤ c} = 1) :
    Integrable (fun x : ℝ => x ^ k) (P : Measure ℝ) := by
  let h : BoundedContinuousFunction ℝ ℝ :=
    prob_14_10_clippedPower c hc k
  have h_int : Integrable (fun x : ℝ => h x) (P : Measure ℝ) :=
    h.integrable (P : Measure ℝ)
  refine h_int.congr ?_
  have hsmeas : MeasurableSet {x : ℝ | |x| ≤ c} := by
    exact continuous_abs.measurable measurableSet_Iic
  have hmem : {x : ℝ | |x| ≤ c} ∈ ae (P : Measure ℝ) := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hsmeas).2 hP
  filter_upwards [hmem] with x hx
  exact prob_14_10_clippedPower_eq_pow c hc k hx

theorem prob_14_10_integrable_polynomial_of_bounded
    (P : ProbabilityMeasure ℝ) (c : ℝ) (hc : 0 ≤ c) (p : ℝ[X])
    (hP : (P : Measure ℝ) {x : ℝ | |x| ≤ c} = 1) :
    Integrable (fun x : ℝ => p.eval x) (P : Measure ℝ) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    have hfun :
        (fun x : ℝ => (p + q).eval x) =
          ((fun x : ℝ => p.eval x) + fun x : ℝ => q.eval x) := by
      funext x
      simp [Polynomial.eval_add]
    rw [hfun]
    exact hp.add hq
  · intro k a
    have hpow := prob_14_10_integrable_pow_of_bounded P c hc k hP
    simpa [Polynomial.eval_monomial] using hpow.const_mul a

theorem prob_14_10_polynomial_integral_tendsto
    (S : prob_14_10_BoundedMomentSetup)
    (hMom : prob_14_10_momentConvergence S.laws S.targetLaw)
    (p : ℝ[X]) :
    Tendsto (fun n : ℕ => ∫ x, p.eval x ∂(S.laws n : Measure ℝ)) atTop
      (𝓝 (∫ x, p.eval x ∂(S.targetLaw : Measure ℝ))) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    have hp_int_source :
        ∀ n : ℕ, Integrable (fun x : ℝ => p.eval x) (S.laws n : Measure ℝ) :=
      fun n => prob_14_10_integrable_polynomial_of_bounded
        (S.laws n) S.c S.c_nonneg p (S.uniformly_bounded n)
    have hq_int_source :
        ∀ n : ℕ, Integrable (fun x : ℝ => q.eval x) (S.laws n : Measure ℝ) :=
      fun n => prob_14_10_integrable_polynomial_of_bounded
        (S.laws n) S.c S.c_nonneg q (S.uniformly_bounded n)
    have hp_int_target :
        Integrable (fun x : ℝ => p.eval x) (S.targetLaw : Measure ℝ) :=
      prob_14_10_integrable_polynomial_of_bounded
        S.targetLaw S.c S.c_nonneg p S.target_bounded
    have hq_int_target :
        Integrable (fun x : ℝ => q.eval x) (S.targetLaw : Measure ℝ) :=
      prob_14_10_integrable_polynomial_of_bounded
        S.targetLaw S.c S.c_nonneg q S.target_bounded
    convert hp.add hq using 1
    · ext n
      rw [← integral_add (hp_int_source n) (hq_int_source n)]
      simp [Polynomial.eval_add]
    · rw [← integral_add hp_int_target hq_int_target]
      simp [Polynomial.eval_add]
  · intro k a
    by_cases hk : k = 0
    · subst hk
      have hconst :
          (fun n : ℕ => ∫ x, (Polynomial.monomial 0 a).eval x ∂(S.laws n : Measure ℝ)) =
            fun _ : ℕ => a := by
        funext n
        simp
      have htarget :
          (∫ x, (Polynomial.monomial 0 a).eval x ∂(S.targetLaw : Measure ℝ)) = a := by
        simp
      rw [hconst, htarget]
      exact tendsto_const_nhds
    · have hkpos : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)
      have hm := hMom k hkpos
      convert hm.const_mul a using 1
      · ext n
        simp [prob_14_10_momentOfLaw, Polynomial.eval_monomial, integral_const_mul]
      · simp [prob_14_10_momentOfLaw, Polynomial.eval_monomial, integral_const_mul]

theorem prob_14_10_integral_error_le_of_support
    (P : ProbabilityMeasure ℝ) (c : ℝ) (η : ℝ)
    {f g : ℝ → ℝ}
    (hf : Integrable f (P : Measure ℝ))
    (hg : Integrable g (P : Measure ℝ))
    (hP : (P : Measure ℝ) {x : ℝ | |x| ≤ c} = 1)
    (hbound : ∀ x : ℝ, |x| ≤ c → ‖f x - g x‖ ≤ η) :
    ‖(∫ x, f x ∂(P : Measure ℝ)) - ∫ x, g x ∂(P : Measure ℝ)‖ ≤ η := by
  have hsmeas : MeasurableSet {x : ℝ | |x| ≤ c} := by
    exact continuous_abs.measurable measurableSet_Iic
  have hmem : {x : ℝ | |x| ≤ c} ∈ ae (P : Measure ℝ) := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hsmeas).2 hP
  have hae : ∀ᵐ x ∂(P : Measure ℝ), ‖f x - g x‖ ≤ η := by
    filter_upwards [hmem] with x hx
    exact hbound x hx
  calc
    ‖(∫ x, f x ∂(P : Measure ℝ)) - ∫ x, g x ∂(P : Measure ℝ)‖ =
        ‖∫ x, f x - g x ∂(P : Measure ℝ)‖ := by
          rw [integral_sub hf hg]
    _ ≤ η * (P : Measure ℝ).real univ :=
        norm_integral_le_of_norm_le_const hae
    _ = η := by simp

theorem prob_14_10_integral_tendsto_of_uniform_polynomial_approx
    (S : prob_14_10_BoundedMomentSetup)
    (hMom : prob_14_10_momentConvergence S.laws S.targetLaw)
    {f : ℝ → ℝ}
    (hf_source : ∀ n : ℕ, Integrable f (S.laws n : Measure ℝ))
    (hf_target : Integrable f (S.targetLaw : Measure ℝ))
    (happrox :
      ∀ η : ℝ, 0 < η →
        ∃ p : ℝ[X], ∀ x : ℝ, |x| ≤ S.c → ‖p.eval x - f x‖ < η) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(S.laws n : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(S.targetLaw : Measure ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε / 4
  have hη : 0 < η := by positivity
  rcases happrox η hη with ⟨p, hp_approx⟩
  have hp_tendsto := prob_14_10_polynomial_integral_tendsto S hMom p
  have hp_eventually :=
    (Metric.tendsto_nhds.mp hp_tendsto) η hη
  filter_upwards [hp_eventually] with n hn
  have hp_source_int :
      Integrable (fun x : ℝ => p.eval x) (S.laws n : Measure ℝ) :=
    prob_14_10_integrable_polynomial_of_bounded
      (S.laws n) S.c S.c_nonneg p (S.uniformly_bounded n)
  have hp_target_int :
      Integrable (fun x : ℝ => p.eval x) (S.targetLaw : Measure ℝ) :=
    prob_14_10_integrable_polynomial_of_bounded
      S.targetLaw S.c S.c_nonneg p S.target_bounded
  have hsource_err :
      ‖(∫ x, f x ∂(S.laws n : Measure ℝ)) -
          ∫ x, p.eval x ∂(S.laws n : Measure ℝ)‖ ≤ η := by
    refine prob_14_10_integral_error_le_of_support
      (S.laws n) S.c η (hf_source n) hp_source_int
      (S.uniformly_bounded n) ?_
    intro x hx
    have h := hp_approx x hx
    have hnorm :
        ‖f x - p.eval x‖ = ‖p.eval x - f x‖ := by
      rw [← norm_neg, neg_sub]
    rw [hnorm]
    exact h.le
  have htarget_err :
      ‖(∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)) -
          ∫ x, f x ∂(S.targetLaw : Measure ℝ)‖ ≤ η := by
    refine prob_14_10_integral_error_le_of_support
      S.targetLaw S.c η hp_target_int hf_target S.target_bounded ?_
    intro x hx
    exact (hp_approx x hx).le
  have hpoly :
      ‖(∫ x, p.eval x ∂(S.laws n : Measure ℝ)) -
          ∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)‖ < η := by
    simpa [Real.dist_eq, Real.norm_eq_abs] using hn
  rw [Real.dist_eq]
  calc
    |(∫ x, f x ∂(S.laws n : Measure ℝ)) -
        ∫ x, f x ∂(S.targetLaw : Measure ℝ)| =
        |((∫ x, f x ∂(S.laws n : Measure ℝ)) -
            ∫ x, p.eval x ∂(S.laws n : Measure ℝ)) +
          ((∫ x, p.eval x ∂(S.laws n : Measure ℝ)) -
            ∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)) +
          ((∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)) -
            ∫ x, f x ∂(S.targetLaw : Measure ℝ))| := by ring_nf
    _ ≤ ‖(∫ x, f x ∂(S.laws n : Measure ℝ)) -
          ∫ x, p.eval x ∂(S.laws n : Measure ℝ)‖ +
        ‖(∫ x, p.eval x ∂(S.laws n : Measure ℝ)) -
          ∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)‖ +
        ‖(∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)) -
          ∫ x, f x ∂(S.targetLaw : Measure ℝ)‖ := by
          simpa [Real.norm_eq_abs] using abs_add_three
            ((∫ x, f x ∂(S.laws n : Measure ℝ)) -
              ∫ x, p.eval x ∂(S.laws n : Measure ℝ))
            ((∫ x, p.eval x ∂(S.laws n : Measure ℝ)) -
              ∫ x, p.eval x ∂(S.targetLaw : Measure ℝ))
            ((∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)) -
              ∫ x, f x ∂(S.targetLaw : Measure ℝ))
    _ < η + η + η := by
      have h12 :
          ‖(∫ x, f x ∂(S.laws n : Measure ℝ)) -
              ∫ x, p.eval x ∂(S.laws n : Measure ℝ)‖ +
            ‖(∫ x, p.eval x ∂(S.laws n : Measure ℝ)) -
              ∫ x, p.eval x ∂(S.targetLaw : Measure ℝ)‖ < η + η :=
        add_lt_add_of_le_of_lt hsource_err hpoly
      exact add_lt_add_of_lt_of_le h12 htarget_err
    _ < ε := by
      dsimp [η]
      nlinarith [hε]

theorem prob_14_10_integrable_exp_of_bounded
    (P : ProbabilityMeasure ℝ) (c : ℝ) (_hc : 0 ≤ c) (t : ℝ)
    (hP : (P : Measure ℝ) {x : ℝ | |x| ≤ c} = 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (P : Measure ℝ) := by
  have hsmeas : MeasurableSet {x : ℝ | |x| ≤ c} := by
    exact continuous_abs.measurable measurableSet_Iic
  have hmem : {x : ℝ | |x| ≤ c} ∈ ae (P : Measure ℝ) := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hsmeas).2 hP
  refine Integrable.of_bound (by fun_prop) (Real.exp (|t| * c)) ?_
  filter_upwards [hmem] with x hx
  have htx_abs : |t * x| ≤ |t| * c := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have htx : t * x ≤ |t| * c :=
    (le_abs_self (t * x)).trans htx_abs
  have hexp := (Real.exp_le_exp).2 htx
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hexp

theorem prob_14_10_exp_uniform_polynomial_approx
    (c t η : ℝ) (hη : 0 < η) :
    ∃ p : ℝ[X], ∀ x : ℝ, |x| ≤ c →
      ‖p.eval x - Real.exp (t * x)‖ < η := by
  let K : Set ℝ := Set.Icc (-c) c
  have hclose :
      ∃ g : polynomialFunctions K,
        ∀ y : K, ‖(g : C(K, ℝ)) y - Real.exp (t * (y : ℝ))‖ < η := by
    exact ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (polynomialFunctions K) (polynomialFunctions_separatesPoints K)
      (fun y : K => Real.exp (t * (y : ℝ))) (by fun_prop) η hη
  rcases hclose with ⟨g, hgclose⟩
  have hgmem : (g : C(K, ℝ)) ∈ Set.range (Polynomial.toContinuousMapOnAlgHom K) := by
    have hgmem0 : (g : C(K, ℝ)) ∈ (polynomialFunctions K : Set C(K, ℝ)) :=
      SetLike.coe_mem g
    simpa [polynomialFunctions_coe] using hgmem0
  rcases hgmem with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro x hx
  have hxK : x ∈ K := abs_le.mp hx
  have h := hgclose ⟨x, hxK⟩
  rw [← hp] at h
  simpa [K, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] using h

theorem prob_14_10_mgf_converges_from_moments
    (S : prob_14_10_BoundedMomentSetup)
    (hMom : prob_14_10_momentConvergence S.laws S.targetLaw)
    (t : ℝ) :
    Tendsto (fun n : ℕ => prob_14_8_mgfOfLaw (S.laws n) t) atTop
      (𝓝 (prob_14_8_mgfOfLaw S.targetLaw t)) := by
  simpa [prob_14_8_mgfOfLaw, chapter14_mgfOfLaw,
    ProbabilityTheory.mgf] using
    prob_14_10_integral_tendsto_of_uniform_polynomial_approx
      S hMom
      (fun n => prob_14_10_integrable_exp_of_bounded
        (S.laws n) S.c S.c_nonneg t (S.uniformly_bounded n))
      (prob_14_10_integrable_exp_of_bounded
        S.targetLaw S.c S.c_nonneg t S.target_bounded)
      (prob_14_10_exp_uniform_polynomial_approx S.c t)



def prob_14_10_moments_to_mgf_setup
    (S : prob_14_10_BoundedMomentSetup)
    (hMom : prob_14_10_momentConvergence S.laws S.targetLaw) :
    {T : prob_14_8_MgfConvergenceSetup // T.laws = S.laws ∧ T.targetLaw = S.targetLaw} := by
  refine ⟨{
    laws := S.laws
    targetLaw := S.targetLaw
    δ := 1
    δ_pos := by norm_num
    mgf_defined := ?_
    target_mgf_defined := ?_
    mgf_converges := ?_
  }, rfl, rfl⟩
  · intro n t _ht
    exact prob_14_10_integrable_exp_of_bounded
      (S.laws n) S.c S.c_nonneg t (S.uniformly_bounded n)
  · intro t _ht
    exact prob_14_10_integrable_exp_of_bounded
      S.targetLaw S.c S.c_nonneg t S.target_bounded
  · intro t _ht
    exact prob_14_10_mgf_converges_from_moments S hMom t



theorem prob_14_10_weak_convergence_to_moments_under_boundedness
    (S : prob_14_10_BoundedMomentSetup)
    (hD : def_14_1 S.laws S.targetLaw) :
    prob_14_10_momentConvergence S.laws S.targetLaw := by
  intro k _hk
  let h : BoundedContinuousFunction ℝ ℝ :=
    prob_14_10_clippedPower S.c S.c_nonneg k
  have hWeak := hD h
  have hsource_eq :
      (fun n : ℕ => prob_14_10_momentOfLaw (S.laws n) k) =
        (fun n : ℕ => ∫ x, h x ∂(S.laws n : Measure ℝ)) := by
    funext n
    exact (prob_14_10_integral_clippedPower_eq_moment
      (S.laws n) S.c S.c_nonneg k (S.uniformly_bounded n)).symm
  have htarget_eq :
      prob_14_10_momentOfLaw S.targetLaw k =
        ∫ x, h x ∂(S.targetLaw : Measure ℝ) := by
    exact (prob_14_10_integral_clippedPower_eq_moment
      S.targetLaw S.c S.c_nonneg k S.target_bounded).symm
  rw [hsource_eq, htarget_eq]
  exact hWeak



theorem prob_14_10_distribution_to_moments
    (S : prob_14_10_BoundedMomentSetup)
    (hD : def_14_1 S.laws S.targetLaw) :
    prob_14_10_momentConvergence S.laws S.targetLaw :=
  prob_14_10_weak_convergence_to_moments_under_boundedness S hD



theorem prob_14_10_moments_to_distribution
    (S : prob_14_10_BoundedMomentSetup)
    (hMom : prob_14_10_momentConvergence S.laws S.targetLaw) :
    def_14_1 S.laws S.targetLaw := by
  rcases prob_14_10_moments_to_mgf_setup S hMom with ⟨T, hT_laws, hT_target⟩
  have hTendsto :
      Tendsto S.laws atTop (𝓝 S.targetLaw) :=
    by
      have h := (prob_14_8 T).2
      rw [hT_laws, hT_target] at h
      exact h
  exact (def_14_1_iff_tendsto).2 hTendsto



theorem prob_14_10
    (S : prob_14_10_BoundedMomentSetup) :
    def_14_1 S.laws S.targetLaw ↔
      prob_14_10_momentConvergence S.laws S.targetLaw := by
  constructor
  · exact prob_14_10_distribution_to_moments S
  · exact prob_14_10_moments_to_distribution S
