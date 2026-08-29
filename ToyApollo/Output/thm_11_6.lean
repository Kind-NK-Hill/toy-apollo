/-
TASK ID: thm_11_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter11-weak-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_10_2
import ToyApollo.Output.thm_11_5
import ToyApollo.Output.thm_2_2

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

private noncomputable def thm_11_6_truncate (R x : ℝ) : ℝ :=
  if R ≤ |x| then 0 else x

private noncomputable def thm_11_6_tailNorm (R x : ℝ) : ℝ :=
  if R ≤ |x| then |x| else 0

private lemma thm_11_6_exists_small_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, (∫ ω, thm_11_6_tailNorm (N : ℝ) (Y ω) ∂P) < η := by
  have htail :
      Tendsto
        (fun N : ℕ => ∫ ω in {ω | (N : ℝ) ≤ |Y ω|}, |Y ω| ∂P)
        atTop (nhds 0) := by
    convert hY.norm.tendsto_setIntegral_nhds_zero;
    rotate_left
    exact ℕ;
    exact atTop;
    exact fun N => {ω | (N : ℝ) ≤ |Y ω|};
    refine' ⟨fun h => fun _ => h, fun h => h _⟩;
    convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _;
    · rw [show (⋂ N : ℕ, {ω : Ω | (N : ℝ) ≤ |Y ω|}) = ∅ from
          Set.eq_empty_iff_forall_notMem.2 fun ω hω => by
            rcases exists_nat_gt (|Y ω|) with ⟨N, hN⟩
            exact not_lt_of_ge (Set.mem_iInter.1 hω N) hN]
      norm_num
    · infer_instance
    · intro N
      exact hY.1.norm.aemeasurable.nullMeasurable measurableSet_Ici
    · intro N M hNM
      exact Set.setOf_subset_setOf.2 fun ω hω => le_trans (mod_cast hNM) hω
    · exact ⟨0, ne_of_lt (MeasureTheory.measure_lt_top _ _)⟩
  rcases (htail.eventually (Iio_mem_nhds hη)).exists with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hS : NullMeasurableSet {ω | (N : ℝ) ≤ |Y ω|} P :=
    hY.1.norm.aemeasurable.nullMeasurable measurableSet_Ici
  calc
    (∫ ω, thm_11_6_tailNorm (N : ℝ) (Y ω) ∂P)
        = ∫ ω, ({ω | (N : ℝ) ≤ |Y ω|} : Set Ω).indicator
            (fun ω => |Y ω|) ω ∂P := by
            apply integral_congr_ae
            filter_upwards with ω
            simp [thm_11_6_tailNorm, Set.indicator]
    _ = ∫ ω in {ω | (N : ℝ) ≤ |Y ω|}, |Y ω| ∂P := integral_indicator₀ hS
    _ < η := hN

theorem thm_11_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (m : ℝ)
    (hInt : Integrable (X 0) P)
    (hMeas : ∀ i, Measurable (X i))
    (hindep : def_5_10_randomVariables P X)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : P[X 0] = m) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
  have hindep' : iIndepFun X P := by
    simpa [def_5_10_randomVariables] using hindep
  have hInt_all : ∀ i, Integrable (X i) P := fun i =>
    (hident i).integrable_iff.2 hInt
  refine ⟨fun n => by
    unfold thm_11_5_sampleMean
    exact measurable_const.mul
      (Finset.measurable_sum Finset.univ (fun i _hi => hMeas i.1)),
    measurable_const, ?_⟩
  intro ε hε
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    by_cases hbtop : b = ⊤
    · subst b
      filter_upwards with n
      exact (lt_top_iff_ne_top.2 (measure_ne_top P _))
    have hbReal : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop
    let c : ℝ := b.toReal / 4
    have hc : 0 < c := by
      dsimp [c]
      positivity
    let η : ℝ := min (ε / 8) ((ε / 4) * c)
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by positivity) (mul_pos (by positivity) hc)
    rcases thm_11_6_exists_small_tail P (X 0) hInt hη with ⟨N, htail⟩
    let R : ℝ := N
    let φ : ℝ → ℝ := thm_11_6_truncate R
    let ψ : ℝ → ℝ := thm_11_6_tailNorm R
    let Z : ℕ → Ω → ℝ := fun i => φ ∘ X i
    let W : ℕ → Ω → ℝ := fun i => ψ ∘ X i
    let q : ℝ := P[W 0]
    have hcut : MeasurableSet {x : ℝ | R ≤ |x|} := by
      exact measurableSet_Ici.preimage continuous_abs.measurable
    have hφ : Measurable φ := by
      dsimp [φ, thm_11_6_truncate]
      exact Measurable.piecewise hcut measurable_const measurable_id
    have hψ : Measurable ψ := by
      dsimp [ψ, thm_11_6_tailNorm]
      exact Measurable.piecewise hcut continuous_abs.measurable measurable_const
    have hZ_measurable : ∀ i, Measurable (Z i) := by
      intro i
      exact hφ.comp (hMeas i)
    have hZ_meas : ∀ i, AEStronglyMeasurable (Z i) P := by
      intro i
      exact (hZ_measurable i).aestronglyMeasurable
    have hW_meas : ∀ i, AEStronglyMeasurable (W i) P := by
      intro i
      exact (hψ.comp_aemeasurable (hInt_all i).aemeasurable).aestronglyMeasurable
    have hZ_mem : ∀ i, MemLp (Z i) 2 P := by
      intro i
      refine MemLp.of_bound (hZ_meas i) R ?_
      filter_upwards with ω
      by_cases hω : R ≤ |X i ω|
      · simp [Z, φ, Function.comp_apply, thm_11_6_truncate, hω, R]
      · have hlt : |X i ω| < R := lt_of_not_ge hω
        simpa [Z, φ, Function.comp_apply, thm_11_6_truncate, hω, Real.norm_eq_abs]
          using hlt.le
    have hZ_int : ∀ i, Integrable (Z i) P := fun i =>
      (hZ_mem i).integrable (by norm_num)
    have hW_int : ∀ i, Integrable (W i) P := by
      intro i
      refine Integrable.mono' (hInt_all i).norm (hW_meas i) ?_
      filter_upwards with ω
      by_cases hω : R ≤ |X i ω|
      · simp [W, ψ, Function.comp_apply, thm_11_6_tailNorm, hω]
      · simp [W, ψ, Function.comp_apply, thm_11_6_tailNorm, hω]
    have hZ_ident : ∀ i, IdentDistrib (Z i) (Z 0) P P := by
      intro i
      simpa [Z, Function.comp_apply] using (hident i).comp hφ
    have hW_ident : ∀ i, IdentDistrib (W i) (W 0) P P := by
      intro i
      simpa [W, Function.comp_apply] using (hident i).comp hψ
    have hZ_uncorr : Pairwise fun i j => Uncorrelated P (Z i) (Z j) := by
      intro i j hij
      have hzij : Z i ⟂ᵢ[P] Z j := by
        simpa [Z, Function.comp_apply] using (hindep'.indepFun hij).comp hφ hφ
      unfold Uncorrelated
      exact hzij.integral_mul_eq_mul_integral (hZ_meas i) (hZ_meas j)
    have hZ_mean : ∀ i, P[Z i] = P[Z 0] := by
      intro i
      exact (hZ_ident i).integral_eq
    have hZ_var :
        ∀ i,
          _root_.variance P (Z i)
              (FiniteAbsMoment.of_memLp (hZ_measurable i) (hZ_mem i)) =
            _root_.variance P (Z 0)
              (FiniteAbsMoment.of_memLp (hZ_measurable 0) (hZ_mem 0)) := by
      intro i
      unfold _root_.variance rthCentralMoment
      rw [ProbabilityTheory.centralMoment_two_eq_variance
          (hZ_mem i).aemeasurable,
        ProbabilityTheory.centralMoment_two_eq_variance
          (hZ_mem 0).aemeasurable]
      exact (hZ_ident i).variance_eq
    have hZ_prob :
        ConvergesInProbability P
          (fun n => thm_11_5_sampleMean Z n) (fun _ => P[Z 0]) :=
      thm_11_5 P Z P[Z 0]
        (_root_.variance P (Z 0)
          (FiniteAbsMoment.of_memLp (hZ_measurable 0) (hZ_mem 0)))
        hZ_measurable hZ_mem hZ_uncorr hZ_mean hZ_var
    have hW_mean : ∀ i, P[W i] = q := by
      intro i
      dsimp [q]
      exact (hW_ident i).integral_eq
    have hq_tail :
        q = ∫ ω, thm_11_6_tailNorm (N : ℝ) (X 0 ω) ∂P := by
      rfl
    have hq_lt : q < η := by
      rw [hq_tail]
      exact htail
    have hq_eps : q < ε / 8 :=
      lt_of_lt_of_le hq_lt (min_le_left _ _)
    have hq_markov : q < (ε / 4) * c :=
      lt_of_lt_of_le hq_lt (min_le_right _ _)
    have hW_nonneg : ∀ i, 0 ≤ᵐ[P] W i := by
      intro i
      filter_upwards with ω
      by_cases hω : R ≤ |X i ω|
      · simp [W, ψ, Function.comp_apply, thm_11_6_tailNorm, hω]
      · simp [W, ψ, Function.comp_apply, thm_11_6_tailNorm, hω]
    have hq_nonneg : 0 ≤ q := by
      rw [← hW_mean 0]
      exact integral_nonneg_of_ae (hW_nonneg 0)
    have hW_avg_int : ∀ n, Integrable (thm_11_5_sampleMean W n) P := by
      intro n
      have hsum :
          Integrable (fun ω => ∑ i : Fin (n + 1), W i.1 ω) P := by
        exact integrable_finset_sum (Finset.univ : Finset (Fin (n + 1)))
          (fun i _ => hW_int i.1)
      change Integrable
        (fun ω => (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), W i.1 ω) P
      exact hsum.const_mul _
    have hW_avg_nonneg : ∀ n, 0 ≤ᵐ[P] thm_11_5_sampleMean W n := by
      intro n
      filter_upwards [ae_all_iff.2 hW_nonneg] with ω hω
      unfold thm_11_5_sampleMean
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => hω i.1)
    have hW_avg_mean : ∀ n, P[thm_11_5_sampleMean W n] = q := by
      intro n
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      calc
        P[thm_11_5_sampleMean W n]
            = (1 / ((n : ℝ) + 1)) *
                P[fun ω => ∑ i : Fin (n + 1), W i.1 ω] := by
              simp [thm_11_5_sampleMean, integral_const_mul]
        _ = (1 / ((n : ℝ) + 1)) *
              (∑ i : Fin (n + 1), P[W i.1]) := by
              rw [integral_finset_sum]
              exact fun i _ => hW_int i.1
        _ = (1 / ((n : ℝ) + 1)) *
              (∑ _i : Fin (n + 1), q) := by simp [hW_mean]
        _ = q := by
              simp [Finset.sum_const, Fintype.card_fin]
              field_simp [hnpos.ne']
    have htail_event_bound :
        ∀ n,
          P {ω | ε / 4 < thm_11_5_sampleMean W n ω} <
            ENNReal.ofReal c := by
      intro n
      let B : Set Ω := {ω | ε / 4 < thm_11_5_sampleMean W n ω}
      have hBsub :
          B ⊆ {ω | ε / 4 ≤ thm_11_5_sampleMean W n ω} := by
        intro ω hω
        change ε / 4 < thm_11_5_sampleMean W n ω at hω
        exact le_of_lt hω
      have hmarkov :=
        thm_10_3 P (thm_11_5_sampleMean W n)
          (hW_avg_nonneg n) (hW_avg_int n) (show 0 < ε / 4 by positivity)
      have hBreal :
          P.real B ≤ q / (ε / 4) := by
        refine (measureReal_mono (μ := P) hBsub).trans ?_
        simpa [hW_avg_mean n] using hmarkov
      have hBreal_lt : P.real B < c := by
        have hden : 0 < ε / 4 := by positivity
        apply lt_of_le_of_lt hBreal
        exact (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hq_markov)
      have hBeq : P B = ENNReal.ofReal (P.real B) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P B)]
      rw [show {ω | ε / 4 < thm_11_5_sampleMean W n ω} = B from rfl, hBeq]
      exact (ENNReal.ofReal_lt_ofReal_iff hc).2 hBreal_lt
    have hpointwise_tail :
        ∀ i ω, |X i ω - Z i ω| = W i ω := by
      intro i ω
      by_cases hω : R ≤ |X i ω|
      · simp [Z, W, φ, ψ, Function.comp_apply, thm_11_6_truncate,
          thm_11_6_tailNorm, hω]
      · simp [Z, W, φ, ψ, Function.comp_apply, thm_11_6_truncate,
          thm_11_6_tailNorm, hω]
    have havg_tail :
        ∀ n ω,
          |thm_11_5_sampleMean X n ω - thm_11_5_sampleMean Z n ω| ≤
            thm_11_5_sampleMean W n ω := by
      intro n ω
      have hscale : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      unfold thm_11_5_sampleMean
      calc
        |(1 / ((n : ℝ) + 1)) * (∑ i : Fin (n + 1), X i.1 ω) -
            (1 / ((n : ℝ) + 1)) * (∑ i : Fin (n + 1), Z i.1 ω)|
            = (1 / ((n : ℝ) + 1)) *
                |∑ i : Fin (n + 1), (X i.1 ω - Z i.1 ω)| := by
                  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
                    abs_of_nonneg hscale]
        _ ≤ (1 / ((n : ℝ) + 1)) *
              (∑ i : Fin (n + 1), |X i.1 ω - Z i.1 ω|) := by
                exact mul_le_mul_of_nonneg_left
                  (Finset.abs_sum_le_sum_abs _ _) hscale
        _ = (1 / ((n : ℝ) + 1)) *
              (∑ i : Fin (n + 1), W i.1 ω) := by
                congr 1
                apply Finset.sum_congr rfl
                intro i _
                exact hpointwise_tail i.1 ω
    have hbias : |m - P[Z 0]| ≤ q := by
      calc
        |m - P[Z 0]| = |P[fun ω => X 0 ω - Z 0 ω]| := by
          rw [integral_sub hInt (hZ_int 0), hmean]
        _ ≤ ∫ ω, ‖X 0 ω - Z 0 ω‖ ∂P :=
          by
            simpa [Real.norm_eq_abs] using
              (norm_integral_le_integral_norm
                (μ := P) (fun ω => X 0 ω - Z 0 ω))
        _ = P[W 0] := by
          apply integral_congr_ae
          filter_upwards with ω
          simpa [Real.norm_eq_abs] using hpointwise_tail 0 ω
        _ = q := hW_mean 0
    have hsubset :
        ∀ n,
          deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ => m) n ε ⊆
            deviationEvent (fun n => thm_11_5_sampleMean Z n)
                (fun _ => P[Z 0]) n (ε / 2) ∪
              {ω | ε / 4 < thm_11_5_sampleMean W n ω} := by
      intro n ω hω
      by_cases hZω :
          ε / 2 < |thm_11_5_sampleMean Z n ω - P[Z 0]|
      · exact Or.inl hZω
      · right
        have hZω' :
            |thm_11_5_sampleMean Z n ω - P[Z 0]| ≤ ε / 2 :=
          le_of_not_gt hZω
        have htriangle :
            |thm_11_5_sampleMean X n ω - m| ≤
              |thm_11_5_sampleMean X n ω - thm_11_5_sampleMean Z n ω| +
                |thm_11_5_sampleMean Z n ω - P[Z 0]| +
                  |P[Z 0] - m| := by
          calc
            |thm_11_5_sampleMean X n ω - m|
                = |(thm_11_5_sampleMean X n ω - thm_11_5_sampleMean Z n ω) +
                    (thm_11_5_sampleMean Z n ω - P[Z 0]) +
                    (P[Z 0] - m)| := by ring_nf
            _ ≤ |thm_11_5_sampleMean X n ω - thm_11_5_sampleMean Z n ω| +
                  |thm_11_5_sampleMean Z n ω - P[Z 0]| +
                  |P[Z 0] - m| := by
                    exact
                      (abs_add_le
                          ((thm_11_5_sampleMean X n ω -
                            thm_11_5_sampleMean Z n ω) +
                            (thm_11_5_sampleMean Z n ω - P[Z 0]))
                          (P[Z 0] - m)).trans
                        (add_le_add
                          (abs_add_le
                            (thm_11_5_sampleMean X n ω -
                              thm_11_5_sampleMean Z n ω)
                            (thm_11_5_sampleMean Z n ω - P[Z 0]))
                          le_rfl)
        have htailω := havg_tail n ω
        have hbias' : |P[Z 0] - m| ≤ q := by simpa [abs_sub_comm] using hbias
        dsimp [deviationEvent] at hω
        have hupper :
            |thm_11_5_sampleMean X n ω - m| ≤
              thm_11_5_sampleMean W n ω + ε / 2 + q := by
          exact htriangle.trans
            (add_le_add (add_le_add htailω hZω') hbias')
        have hsum :
            ε < thm_11_5_sampleMean W n ω + ε / 2 + q :=
          lt_of_lt_of_le hω hupper
        have hWlarge : 3 * ε / 8 < thm_11_5_sampleMean W n ω := by
          linarith [hq_eps]
        exact lt_trans (by linarith [hε] : ε / 4 < 3 * ε / 8) hWlarge
    have hZ_eventually :
        ∀ᶠ n : ℕ in atTop,
          P (deviationEvent (fun n => thm_11_5_sampleMean Z n)
              (fun _ => P[Z 0]) n (ε / 2)) < ENNReal.ofReal c := by
      have hconv := hZ_prob.2.2 (ε / 2) (by positivity)
      exact (tendsto_order.1 hconv).2 (ENNReal.ofReal c) (ENNReal.ofReal_pos.2 hc)
    have hsum_lt : ENNReal.ofReal c + ENNReal.ofReal c < b := by
      rw [← ENNReal.ofReal_add (le_of_lt hc) (le_of_lt hc)]
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbtop]
      dsimp [c]
      linarith
    filter_upwards [hZ_eventually] with n hn
    calc
      P (deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ => m) n ε)
          ≤ P (deviationEvent (fun n => thm_11_5_sampleMean Z n)
                (fun _ => P[Z 0]) n (ε / 2) ∪
              {ω | ε / 4 < thm_11_5_sampleMean W n ω}) :=
            measure_mono (hsubset n)
      _ ≤ P (deviationEvent (fun n => thm_11_5_sampleMean Z n)
              (fun _ => P[Z 0]) n (ε / 2)) +
            P {ω | ε / 4 < thm_11_5_sampleMean W n ω} :=
          measure_union_le _ _
      _ < ENNReal.ofReal c + ENNReal.ofReal c :=
          ENNReal.add_lt_add hn (htail_event_bound n)
      _ < b := hsum_lt
