/-
TASK ID: prob_13_10_relaxed_optional_stopping_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_13_10_independent_count_support
import ToyApollo.Output.thm_13_18

open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

def prob_13_10_relaxed_conditional_increment_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧
    ∀ n : ℕ, ∀ᵐ ω ∂P,
      P[fun ω => |X (n + 1) ω - X n ω| | 𝓕n n] ω ≤ c

def prob_13_10_incrementAbsTerm {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (k : ℕ) : Ω → ℝ :=
  fun ω =>
    Set.indicator {ω | k + 1 ≤ T ω}
      (fun ω => |X (k + 1) ω - X k ω|) ω

def prob_13_10_incrementAbsSeries {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) : Ω → ℝ :=
  fun ω => ∑' k : ℕ, prob_13_10_incrementAbsTerm X T k ω

theorem prob_13_10_incrementAbsTerm_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (k : ℕ) (ω : Ω) :
    0 ≤ prob_13_10_incrementAbsTerm X T k ω :=
  Set.indicator_nonneg
    (fun η _hη => abs_nonneg (X (k + 1) η - X k η)) ω

theorem prob_13_10_incrementAbsTerm_pointwise_summable {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (ω : Ω) :
    Summable (fun k : ℕ => prob_13_10_incrementAbsTerm X T k ω) := by
  refine summable_of_ne_finset_zero (s := Finset.range (T ω)) ?_
  intro k hk
  have hkge : T ω ≤ k := by
    exact Nat.le_of_not_gt (fun hlt => hk (Finset.mem_range.mpr hlt))
  have hnotlt : ¬ k < T ω := Nat.not_lt.mpr hkge
  simp [prob_13_10_incrementAbsTerm, hnotlt]

theorem prob_13_10_incrementAbsSeries_eq_finite_sum {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (ω : Ω) :
    prob_13_10_incrementAbsSeries X T ω =
      ∑ k ∈ Finset.range (T ω), |X (k + 1) ω - X k ω| := by
  rw [prob_13_10_incrementAbsSeries]
  rw [tsum_eq_sum (s := Finset.range (T ω))]
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < T ω := Finset.mem_range.mp hk
    have hsucc : k + 1 ≤ T ω := Nat.succ_le_iff.mpr hklt
    simp [prob_13_10_incrementAbsTerm, hklt]
  · intro k hk
    have hkge : T ω ≤ k := by
      exact Nat.le_of_not_gt (fun hlt => hk (Finset.mem_range.mpr hlt))
    have hnotlt : ¬ k < T ω := Nat.not_lt.mpr hkge
    simp [prob_13_10_incrementAbsTerm, hnotlt]

theorem prob_13_10_telescoping_abs_sum_bound {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ m : ℕ,
      |X m ω| ≤
        |X 0 ω| + ∑ k ∈ Finset.range m, |X (k + 1) ω - X k ω| := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hStep :
          |X (m + 1) ω| ≤ |X m ω| + |X (m + 1) ω - X m ω| := by
        have hDecomp :
            X (m + 1) ω = X m ω + (X (m + 1) ω - X m ω) := by
          ring
        calc
          |X (m + 1) ω|
              = |X m ω + (X (m + 1) ω - X m ω)| := by
                exact congrArg abs hDecomp
          _ ≤ |X m ω| + |X (m + 1) ω - X m ω| :=
                abs_add_le (X m ω) (X (m + 1) ω - X m ω)
      calc
        |X (m + 1) ω|
            ≤ |X m ω| + |X (m + 1) ω - X m ω| := hStep
        _ ≤ (|X 0 ω| +
              ∑ k ∈ Finset.range m, |X (k + 1) ω - X k ω|) +
              |X (m + 1) ω - X m ω| := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right ih |X (m + 1) ω - X m ω|
        _ = |X 0 ω| +
              ∑ k ∈ Finset.range (m + 1), |X (k + 1) ω - X k ω| := by
            simp [Finset.sum_range_succ, add_assoc]

theorem prob_13_10_stoppedProcess_abs_le_initial_add_incrementSeries {Ω : Type*}
    [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (n : ℕ) (ω : Ω) :
    |def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω| ≤
      |X 0 ω| + prob_13_10_incrementAbsSeries X T ω := by
  let j : ℕ := def_13_9_stoppedIndex (fun ω => (T ω : WithTop ℕ)) n ω
  have hStopped :
      def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω =
        X j ω := by
    rfl
  have hjle : j ≤ T ω := by
    simp [j, def_13_9_stoppedIndex]
  have htel := prob_13_10_telescoping_abs_sum_bound X ω j
  have hsum_le :
      (∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω|) ≤
        ∑ k ∈ Finset.range (T ω), |X (k + 1) ω - X k ω| := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.range_subset.mpr
        (fun k hk => Finset.mem_range.mpr (hk.trans_le hjle))
    · intro k _hkT _hknj
      exact abs_nonneg (X (k + 1) ω - X k ω)
  calc
    |def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω|
        = |X j ω| := by rw [hStopped]
    _ ≤ |X 0 ω| + ∑ k ∈ Finset.range j, |X (k + 1) ω - X k ω| := htel
    _ ≤ |X 0 ω| + ∑ k ∈ Finset.range (T ω), |X (k + 1) ω - X k ω| := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hsum_le |X 0 ω|
    _ = |X 0 ω| + prob_13_10_incrementAbsSeries X T ω := by
          rw [prob_13_10_incrementAbsSeries_eq_finite_sum]

theorem prob_13_10_incrementAbsTerm_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (k : ℕ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ))) :
    Integrable (prob_13_10_incrementAbsTerm X T k) P := by
  let E : Set Ω := {ω | k + 1 ≤ T ω}
  let Δ : Ω → ℝ := fun ω => |X (k + 1) ω - X k ω|
  have hfil := def_13_7_isFiltration hM
  have hE_sub : @MeasurableSet Ω (𝓕n k) E := by
    have hActive := thm_13_17_activeEvent_measurable
      (𝓕n := 𝓕n) (T := fun ω => (T ω : WithTop ℕ)) hT k
    simpa [E, thm_13_17_activeEvent, Nat.succ_le_iff] using hActive
  have hE : MeasurableSet E := hfil.1 k E hE_sub
  have hΔInt : Integrable Δ P := by
    dsimp [Δ]
    simpa [thm_13_17_rawIncrement] using
      (thm_13_17_rawIncrement_integrable
        (P := P) (𝓕n := 𝓕n) (X := X) hM k).norm
  simpa [prob_13_10_incrementAbsTerm, E, Δ] using hΔInt.indicator hE

theorem prob_13_10_expected_increment_on_tail_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c) :
    ∀ k : ℕ,
      ∫ ω,
        Set.indicator {ω | k + 1 ≤ T ω}
          (fun ω => |X (k + 1) ω - X k ω|) ω ∂P ≤
        c * prob_13_10_tailMass P T (k + 1) := by
  intro k
  let E : Set Ω := {ω | k + 1 ≤ T ω}
  let Δ : Ω → ℝ := fun ω => |X (k + 1) ω - X k ω|
  have hfil := def_13_7_isFiltration hM
  have hE_sub : @MeasurableSet Ω (𝓕n k) E := by
    have hActive := thm_13_17_activeEvent_measurable
      (𝓕n := 𝓕n) (T := fun ω => (T ω : WithTop ℕ)) hT k
    simpa [E, thm_13_17_activeEvent, Nat.succ_le_iff] using hActive
  have hE : MeasurableSet E := hfil.1 k E hE_sub
  have hΔInt : Integrable Δ P := by
    dsimp [Δ]
    simpa [thm_13_17_rawIncrement] using
      (thm_13_17_rawIncrement_integrable
        (P := P) (𝓕n := 𝓕n) (X := X) hM k).norm
  have hCondInt : Integrable (P[Δ | 𝓕n k]) P := integrable_condExp
  have hSetEq :
      ∫ ω in E, Δ ω ∂P =
        ∫ ω in E, P[Δ | 𝓕n k] ω ∂P := by
    symm
    exact setIntegral_condExp (hfil.1 k) hΔInt hE_sub
  have hBoundΔ : P[Δ | 𝓕n k] ≤ᶠ[ae P] fun _ => c := by
    simpa [Δ] using hBound.2 k
  have hMono :
      ∫ ω in E, P[Δ | 𝓕n k] ω ∂P ≤ ∫ ω in E, c ∂P := by
    exact setIntegral_mono_ae
      hCondInt.integrableOn (integrable_const c).integrableOn hBoundΔ
  calc
    ∫ ω, Set.indicator E Δ ω ∂P
        = ∫ ω in E, Δ ω ∂P := by
          rw [integral_indicator hE]
    _ = ∫ ω in E, P[Δ | 𝓕n k] ω ∂P := hSetEq
    _ ≤ ∫ ω in E, c ∂P := hMono
    _ = P.real E * c := by
          simp [smul_eq_mul]
    _ = c * prob_13_10_tailMass P T (k + 1) := by
          simp [prob_13_10_tailMass, E, Measure.real_def, mul_comm]

theorem prob_13_10_incrementAbsTerm_integral_summable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    Summable (fun k : ℕ =>
      ∫ ω, prob_13_10_incrementAbsTerm X T k ω ∂P) := by
  have hc : 0 ≤ c := hBound.1
  have hMajor :
      Summable (fun k : ℕ => c * prob_13_10_tailMass P T (k + 1)) :=
    (prob_13_10_tail_mass_summable P T hTIntegrable).mul_left c
  refine hMajor.of_nonneg_of_le ?_ ?_
  · intro k
    exact integral_nonneg (fun ω =>
      Set.indicator_nonneg
        (fun η _hη => abs_nonneg (X (k + 1) η - X k η)) ω)
  · intro k
    simpa [prob_13_10_incrementAbsTerm] using
      prob_13_10_expected_increment_on_tail_bound
        (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
        hM hT hSigmaFinite hBound k

theorem prob_13_10_incrementAbsSeries_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    Integrable (prob_13_10_incrementAbsSeries X T) P := by
  let g : ℕ → Ω → ℝ := fun k => prob_13_10_incrementAbsTerm X T k
  have hgInt : ∀ k : ℕ, Integrable (g k) P := by
    intro k
    exact prob_13_10_incrementAbsTerm_integrable
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) k hM hT
  have hgNonneg : ∀ k : ℕ, 0 ≤ᵐ[P] g k := by
    intro k
    exact ae_of_all P (fun ω =>
      prob_13_10_incrementAbsTerm_nonneg X T k ω)
  have hsumInt :
      Summable (fun k : ℕ => ∫ ω, g k ω ∂P) := by
    simpa [g] using
      prob_13_10_incrementAbsTerm_integral_summable
        (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
        hM hT hSigmaFinite hBound hTIntegrable
  have hpartial :
      ∀ n : ℕ,
        AEStronglyMeasurable (fun ω => ∑ k ∈ Finset.range n, g k ω) P := by
    intro n
    have hfun :
        AEStronglyMeasurable (∑ k ∈ Finset.range n, g k) P :=
      Finset.aestronglyMeasurable_sum (Finset.range n)
        (fun k _hk => (hgInt k).aestronglyMeasurable)
    exact hfun.congr (ae_of_all P (fun ω => by simp))
  have hlim :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, g k ω)
          atTop (𝓝 (prob_13_10_incrementAbsSeries X T ω)) := by
    filter_upwards with ω
    simpa [prob_13_10_incrementAbsSeries, g] using
      (prob_13_10_incrementAbsTerm_pointwise_summable X T ω).hasSum.tendsto_sum_nat
  have hsm :
      AEStronglyMeasurable (prob_13_10_incrementAbsSeries X T) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hpartial hlim
  have hOfRealSeries :
      (fun ω =>
        ENNReal.ofReal ‖prob_13_10_incrementAbsSeries X T ω‖)
        =ᵐ[P]
      (fun ω => ∑' k : ℕ, ENNReal.ofReal (g k ω)) := by
    filter_upwards with ω
    have hnonneg : ∀ k : ℕ, 0 ≤ g k ω := by
      intro k
      exact prob_13_10_incrementAbsTerm_nonneg X T k ω
    have hsumm : Summable (fun k : ℕ => g k ω) := by
      simpa [g] using prob_13_10_incrementAbsTerm_pointwise_summable X T ω
    have hseries_nonneg :
        0 ≤ prob_13_10_incrementAbsSeries X T ω := by
      simpa [prob_13_10_incrementAbsSeries, g] using
        tsum_nonneg (g := fun k : ℕ => g k ω) hnonneg
    rw [Real.norm_of_nonneg hseries_nonneg]
    simpa [prob_13_10_incrementAbsSeries, g] using
      ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm
  have hlin_eq :
      ∫⁻ ω, ENNReal.ofReal ‖prob_13_10_incrementAbsSeries X T ω‖ ∂P =
        ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P := by
    rw [lintegral_congr_ae hOfRealSeries]
    rw [lintegral_tsum]
    intro k
    exact (hgInt k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hlin_term :
      ∀ k : ℕ,
        ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P =
          ENNReal.ofReal (∫ ω, g k ω ∂P) := by
    intro k
    exact (ofReal_integral_eq_lintegral_ofReal (hgInt k) (hgNonneg k)).symm
  have hlin_finite :
      ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P < ⊤ := by
    calc
      ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P
          = ∑' k : ℕ, ENNReal.ofReal (∫ ω, g k ω ∂P) := by
            apply tsum_congr
            intro k
            exact hlin_term k
      _ = ENNReal.ofReal (∑' k : ℕ, ∫ ω, g k ω ∂P) := by
            symm
            exact ENNReal.ofReal_tsum_of_nonneg
              (fun k => integral_nonneg_of_ae (hgNonneg k)) hsumInt
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hsm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [hlin_eq]
  exact hlin_finite

theorem prob_13_10_relaxed_stoppedProcess_domination {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    ∃ G : Ω → ℝ,
      Integrable G P ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P,
          |def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω| ≤ G ω := by
  refine ⟨fun ω => |X 0 ω| + prob_13_10_incrementAbsSeries X T ω, ?_, ?_⟩
  · exact (def_13_7_integrable hM 0).norm.add
      (prob_13_10_incrementAbsSeries_integrable
        (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
        hM hT hSigmaFinite hBound hTIntegrable)
  · intro n
    exact ae_of_all P
      (fun ω =>
        prob_13_10_stoppedProcess_abs_le_initial_add_incrementSeries X T n ω)

theorem prob_13_10_relaxed_stopped_integral_limit_source {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    thm_13_18_stoppedIntegralLimit P X
      (fun ω => (T ω : WithTop ℕ))
      (thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ))) := by
  have hFinite :
      ∀ᵐ ω ∂P, (T ω : WithTop ℕ) < ⊤ := by
    exact ae_of_all P (fun ω => WithTop.coe_lt_top (T ω))
  have hAgree :
      thm_13_18_stoppedValueAgreement P X
        (fun ω => (T ω : WithTop ℕ))
        (thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ))) :=
    thm_13_18_stoppedValueReal_agreement P X
      (fun ω => (T ω : WithTop ℕ))
  have hMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n) P := by
    intro n
    exact (thm_13_17_stoppedProcess_integrable hM hT n).aestronglyMeasurable
  have hDomination :
      ∃ G : Ω → ℝ,
        Integrable G P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P,
            |def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω| ≤ G ω :=
    prob_13_10_relaxed_stoppedProcess_domination
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
      hM hT hSigmaFinite hBound hTIntegrable
  exact thm_13_18_stoppedIntegralLimit_of_integrableDomination
    hFinite hAgree hMeas hDomination

theorem prob_13_10_relaxed_increment_optional_stopping_source {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → ℕ} {c : ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    ∫ ω, thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ)) ω ∂P =
      ∫ ω, X 0 ω ∂P := by
  have hConst :
      ∀ n : ℕ,
        ∫ ω, def_13_9_stoppedProcess X (fun ω => (T ω : WithTop ℕ)) n ω ∂P =
          ∫ ω, X 0 ω ∂P :=
    thm_13_17_expectation_constant hM hT hSigmaFinite
  have hLimit :
      thm_13_18_stoppedIntegralLimit P X
        (fun ω => (T ω : WithTop ℕ))
        (thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ))) :=
    prob_13_10_relaxed_stopped_integral_limit_source
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
      hM hT hSigmaFinite hBound hTIntegrable
  exact thm_13_18_constant_limit_of_stopped_expectations hConst hLimit

theorem prob_13_10_relaxed_stopped_integral_limit {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    thm_13_18_stoppedIntegralLimit P X
      (fun ω => (T ω : WithTop ℕ))
      (thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ))) :=
  prob_13_10_relaxed_stopped_integral_limit_source
    (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
    hM hT hSigmaFinite hBound hTIntegrable

theorem prob_13_10_relaxed_stopped_integral_limit_from_domination {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) (XT : Ω → ℝ)
    (hFinite : ∀ᵐ ω ∂P, T ω < ⊤)
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT)
    (hMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hDomination :
      ∃ G : Ω → ℝ,
        Integrable G P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P,
            |def_13_9_stoppedProcess X T n ω| ≤ G ω) :
    thm_13_18_stoppedIntegralLimit P X T XT := by
  let _parentFiltration := 𝓕n
  exact thm_13_18_stoppedIntegralLimit_of_integrableDomination
    hFinite hAgree hMeas hDomination

theorem prob_13_10_relaxed_increment_optional_stopping_from_domination {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hFinite : ∀ᵐ ω ∂P, T ω < ⊤)
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT)
    (hMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hDomination :
      ∃ G : Ω → ℝ,
        Integrable G P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P,
            |def_13_9_stoppedProcess X T n ω| ≤ G ω) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hConst :
      ∀ n : ℕ,
        ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
          ∫ ω, X 0 ω ∂P :=
    thm_13_17_expectation_constant hM hT hSigmaFinite
  have hLimit : thm_13_18_stoppedIntegralLimit P X T XT :=
    prob_13_10_relaxed_stopped_integral_limit_from_domination
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (XT := XT)
      hFinite hAgree hMeas hDomination
  exact thm_13_18_constant_limit_of_stopped_expectations hConst hLimit

theorem prob_13_10_relaxed_increment_optional_stopping {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → ℕ} {c : ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    ∫ ω, thm_13_18_stoppedValueReal X (fun ω => (T ω : WithTop ℕ)) ω ∂P =
      ∫ ω, X 0 ω ∂P :=
  prob_13_10_relaxed_increment_optional_stopping_source
    (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
    hM hT hSigmaFinite hBound hTIntegrable
