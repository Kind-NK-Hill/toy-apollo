/-
TASK ID: prob_13_10_centered_wald_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.chapter13_stopping_support
import ToyApollo.Output.prob_13_10_independent_count_support
import ToyApollo.Output.prob_13_10_relaxed_optional_stopping_support

open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

def prob_13_10_oneIndexedHistory {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (n : ℕ) : Ω → Fin n → ℝ :=
  chapter13_oneIndexedHistory Y n

@[reducible]
def prob_13_10_oneIndexedNaturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  chapter13_oneIndexedNaturalFiltration Y

def prob_13_10_historyProjection {n m : ℕ} (h : n ≤ m) :
    (Fin m → ℝ) → (Fin n → ℝ) :=
  chapter13_historyProjection h

theorem prob_13_10_historyProjection_measurable {n m : ℕ} (h : n ≤ m) :
    Measurable (prob_13_10_historyProjection h) := by
  simpa [prob_13_10_historyProjection] using
    chapter13_historyProjection_measurable h

theorem prob_13_10_historyProjection_comp {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    prob_13_10_oneIndexedHistory Y n =
      prob_13_10_historyProjection h ∘
        prob_13_10_oneIndexedHistory Y m := by
  simpa [prob_13_10_oneIndexedHistory, prob_13_10_historyProjection] using
    chapter13_historyProjection_comp Y h

theorem prob_13_10_history_measurable_self {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    @Measurable Ω (Fin n → ℝ)
      (prob_13_10_oneIndexedNaturalFiltration Y n) _
      (prob_13_10_oneIndexedHistory Y n) := by
  simpa [prob_13_10_oneIndexedHistory,
    prob_13_10_oneIndexedNaturalFiltration] using
    chapter13_history_measurable_self Y n

theorem prob_13_10_history_measurable_of_le {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    @Measurable Ω (Fin n → ℝ)
      (prob_13_10_oneIndexedNaturalFiltration Y m) _
      (prob_13_10_oneIndexedHistory Y n) := by
  simpa [prob_13_10_oneIndexedHistory,
    prob_13_10_oneIndexedNaturalFiltration] using
    chapter13_history_measurable_of_le Y h

theorem prob_13_10_oneIndexedNaturalFiltration_mono {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    prob_13_10_oneIndexedNaturalFiltration Y n ≤
      prob_13_10_oneIndexedNaturalFiltration Y m := by
  simpa [prob_13_10_oneIndexedNaturalFiltration] using
    chapter13_oneIndexedNaturalFiltration_mono Y h

theorem prob_13_10_oneIndexedNaturalFiltration_sub_ambient {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y n)) (n : ℕ) :
    prob_13_10_oneIndexedNaturalFiltration Y n ≤ 𝓕 := by
  simpa [prob_13_10_oneIndexedNaturalFiltration] using
    chapter13_oneIndexedNaturalFiltration_sub_ambient Y hY n

theorem prob_13_10_oneIndexedNaturalFiltration_isFiltration {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y n)) :
    def_13_6_isFiltration (𝓕 := 𝓕)
      (prob_13_10_oneIndexedNaturalFiltration Y) := by
  simpa [prob_13_10_oneIndexedNaturalFiltration] using
    chapter13_oneIndexedNaturalFiltration_isFiltration Y hY

def prob_13_10_partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => ∑ i ∈ Finset.range n, Y (i + 1) ω

theorem prob_13_10_partialSum_succ {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    prob_13_10_partialSum Y (n + 1) =
      prob_13_10_partialSum Y n + Y (n + 1) := by
  funext ω
  simp [prob_13_10_partialSum, Finset.sum_range_succ]

theorem prob_13_10_sumHistory_measurable (n : ℕ) :
    Measurable (fun z : Fin n → ℝ => ∑ i : Fin n, z i) := by
  classical
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)

theorem prob_13_10_partialSum_adapted {Ω : Type*}
    [MeasurableSpace Ω] (Y : ℕ → Ω → ℝ) :
    def_13_6_adapted (prob_13_10_oneIndexedNaturalFiltration Y)
      (prob_13_10_partialSum Y) := by
  classical
  intro n
  cases n with
  | zero =>
      exact measurable_const
  | succ n =>
      let g : (Fin (n + 1) → ℝ) → ℝ := fun z => ∑ i : Fin (n + 1), z i
      have hg : Measurable g := prob_13_10_sumHistory_measurable (n + 1)
      have hhist :
          Measurable[prob_13_10_oneIndexedNaturalFiltration Y (n + 1)]
            (prob_13_10_oneIndexedHistory Y (n + 1)) :=
        Measurable.of_comap_le le_rfl
      have hcomp :
          Measurable[prob_13_10_oneIndexedNaturalFiltration Y (n + 1)]
            (g ∘ prob_13_10_oneIndexedHistory Y (n + 1)) :=
        hg.comp hhist
      convert hcomp using 1
      funext ω
      simp only [g, Function.comp_apply, prob_13_10_oneIndexedHistory,
        Finset.sum_fin_eq_sum_range, prob_13_10_partialSum]
      apply Finset.sum_congr rfl
      intro x hx
      have hxle : x ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
      simp [chapter13_oneIndexedHistory, hxle]

theorem prob_13_10_partialSum_integrable {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P) :
    ∀ n : ℕ, Integrable (prob_13_10_partialSum Y n) P := by
  intro n
  unfold prob_13_10_partialSum
  exact integrable_finset_sum (Finset.range n) (fun i _ => hYint i)

def prob_13_10_fairIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ,
    P[Y (n + 1) | prob_13_10_oneIndexedNaturalFiltration Y n] =ᵐ[P]
      (0 : Ω → ℝ)

theorem prob_13_10_oneIndexedNaturalFiltration_succ_eq_mathlib
    {Ω : Type*} [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y (i + 1))) (n : ℕ) :
    prob_13_10_oneIndexedNaturalFiltration Y (n + 1) =
      Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n := by
  apply le_antisymm
  · have hhist :
        @Measurable Ω (Fin (n + 1) → ℝ)
          (Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n) _
          (prob_13_10_oneIndexedHistory Y (n + 1)) := by
      exact
        @measurable_pi_lambda Ω (Fin (n + 1)) (fun _ => ℝ)
          (Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n)
          (fun _ => borel ℝ) (prob_13_10_oneIndexedHistory Y (n + 1))
          (fun k => by
            have hle :
                MeasurableSpace.comap (Y (k.1 + 1))
                    (borel ℝ) ≤
                  Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n := by
              change MeasurableSpace.comap
                    ((fun i : ℕ => Y (i + 1)) k.1) (borel ℝ) ≤
                (⨆ j ≤ n,
                  MeasurableSpace.comap
                    ((fun i : ℕ => Y (i + 1)) j) (borel ℝ))
              exact le_iSup_of_le k.1
                (le_iSup_of_le (Nat.le_of_lt_succ k.2) le_rfl)
            exact Measurable.of_comap_le hle)
    exact hhist.comap_le
  · change (⨆ j ≤ n,
        MeasurableSpace.comap ((fun i : ℕ => Y (i + 1)) j) (borel ℝ)) ≤
      prob_13_10_oneIndexedNaturalFiltration Y (n + 1)
    refine iSup₂_le ?_
    intro j hj
    have hcoord :
        @Measurable Ω ℝ
          (prob_13_10_oneIndexedNaturalFiltration Y (n + 1)) _
          (Y (j + 1)) := by
      have hhist :
          @Measurable Ω (Fin (n + 1) → ℝ)
            (prob_13_10_oneIndexedNaturalFiltration Y (n + 1)) _
            (prob_13_10_oneIndexedHistory Y (n + 1)) :=
        prob_13_10_history_measurable_self Y (n + 1)
      have hcoord' :
          @Measurable Ω ℝ
            (prob_13_10_oneIndexedNaturalFiltration Y (n + 1)) _
            ((fun z : Fin (n + 1) → ℝ =>
                z ⟨j, Nat.lt_succ_of_le hj⟩) ∘
              prob_13_10_oneIndexedHistory Y (n + 1)) :=
        (measurable_pi_apply ⟨j, Nat.lt_succ_of_le hj⟩).comp hhist
      simpa [prob_13_10_oneIndexedHistory, Function.comp_apply] using hcoord'
    exact hcoord.comap_le

theorem prob_13_10_fairIncrement_of_iIndep_zeroMean {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ}
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y i))
    (hiid : ProbabilityTheory.iIndepFun (fun i : ℕ => Y (i + 1)) P)
    (hzero : ∀ i : ℕ, ∫ ω, Y (i + 1) ω ∂P = 0) :
    prob_13_10_fairIncrement P Y := by
  intro n
  cases n with
  | zero =>
      change P[Y 1 | ⊥] =ᵐ[P] (0 : Ω → ℝ)
      rw [condExp_bot (μ := P) (f := Y 1), hzero 0]
      exact Filter.Eventually.of_forall fun _ => rfl
  | succ n =>
      have heq :=
        prob_13_10_oneIndexedNaturalFiltration_succ_eq_mathlib Y
          (fun i => hYsm (i + 1)) n
      rw [heq]
      exact
        (ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
          (μ := P) (f := fun i : ℕ => Y (i + 1))
          (fun i => hYsm (i + 1)) hiid (Nat.lt_succ_self n)).trans
          (by
            rw [hzero (n + 1)]
            exact Filter.Eventually.of_forall fun _ => rfl)

theorem prob_13_10_partialSum_oneStepCondition {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕)
        (prob_13_10_oneIndexedNaturalFiltration Y))
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)))
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P)
    (hfair : prob_13_10_fairIncrement P Y) :
    def_13_7_oneStepCondition P
      (prob_13_10_oneIndexedNaturalFiltration Y)
      (prob_13_10_partialSum Y) := by
  intro n
  have hS_succ :
      prob_13_10_partialSum Y (n + 1) =
        prob_13_10_partialSum Y n + Y (n + 1) :=
    prob_13_10_partialSum_succ Y n
  have hS_int :
      Integrable (prob_13_10_partialSum Y n) P :=
    prob_13_10_partialSum_integrable hYint n
  have hY_next_int : Integrable (Y (n + 1)) P := hYint n
  have hS_meas :
      Measurable[prob_13_10_oneIndexedNaturalFiltration Y n]
        (prob_13_10_partialSum Y n) :=
    prob_13_10_partialSum_adapted Y n
  haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
  have hS_cond :
      P[prob_13_10_partialSum Y n |
          prob_13_10_oneIndexedNaturalFiltration Y n] =
        prob_13_10_partialSum Y n :=
    condExp_of_stronglyMeasurable (hfiltration.1 n)
      hS_meas.stronglyMeasurable hS_int
  have hS_cond_ae :
      P[prob_13_10_partialSum Y n |
          prob_13_10_oneIndexedNaturalFiltration Y n] =ᵐ[P]
        prob_13_10_partialSum Y n := by
    rw [hS_cond]
  calc
    P[prob_13_10_partialSum Y (n + 1) |
        prob_13_10_oneIndexedNaturalFiltration Y n]
        =ᵐ[P] P[prob_13_10_partialSum Y n + Y (n + 1) |
          prob_13_10_oneIndexedNaturalFiltration Y n] := by
          rw [hS_succ]
    _ =ᵐ[P]
        P[prob_13_10_partialSum Y n |
          prob_13_10_oneIndexedNaturalFiltration Y n] +
          P[Y (n + 1) |
            prob_13_10_oneIndexedNaturalFiltration Y n] :=
        condExp_add hS_int hY_next_int _
    _ =ᵐ[P] prob_13_10_partialSum Y n + (0 : Ω → ℝ) :=
        hS_cond_ae.add (hfair n)
    _ =ᵐ[P] prob_13_10_partialSum Y n := by
        simp

theorem prob_13_10_partialSum_martingale_of_iid_zeroMean {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ}
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y i))
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P)
    (hiid : ProbabilityTheory.iIndepFun (fun i : ℕ => Y (i + 1)) P)
    (hzero : ∀ i : ℕ, ∫ ω, Y (i + 1) ω ∂P = 0) :
    def_13_7 P (prob_13_10_oneIndexedNaturalFiltration Y)
      (prob_13_10_partialSum Y) := by
  have hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕)
        (prob_13_10_oneIndexedNaturalFiltration Y) :=
    prob_13_10_oneIndexedNaturalFiltration_isFiltration Y
      (fun n => (hYsm n).measurable)
  have hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)) := by
    intro n
    infer_instance
  have hfair : prob_13_10_fairIncrement P Y :=
    prob_13_10_fairIncrement_of_iIndep_zeroMean hYsm hiid hzero
  exact ⟨hfiltration, prob_13_10_partialSum_integrable hYint,
    prob_13_10_partialSum_adapted Y,
    prob_13_10_partialSum_oneStepCondition
      hfiltration hSigmaFinite hYint hfair⟩

def prob_13_10_iid_sequence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ProbabilityTheory.iIndepFun X P ∧
    ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P

def prob_13_10_centeredIncrements {Ω : Type*}
    (X : ℕ → Ω → ℝ) (μ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => X n ω - μ

def prob_13_10_centeredWalk {Ω : Type*}
    (X : ℕ → Ω → ℝ) (μ : ℝ) : ℕ → Ω → ℝ :=
  prob_13_10_partialSum (prob_13_10_centeredIncrements X μ)

def prob_13_10_natural_filtration {Ω : Type*}
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  F = prob_13_10_oneIndexedNaturalFiltration (prob_13_10_centeredIncrements X μ)

theorem prob_13_10_centeredIncrements_iIndep {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.iIndepFun
      (fun i : ℕ => prob_13_10_centeredIncrements X μ (i + 1)) P := by
  have hShift :
      ProbabilityTheory.iIndepFun (fun i : ℕ => X (i + 1)) P :=
    hIndep.precomp Nat.succ_injective
  have hCentered :=
    hShift.comp (fun _ => fun x : ℝ => x - μ)
      (fun _ => (show Measurable (fun x : ℝ => x - μ) from
        measurable_id.sub measurable_const))
  simpa [prob_13_10_centeredIncrements, Function.comp_def] using hCentered

theorem prob_13_10_centeredIncrements_integrable {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hX1Integrable : Integrable (X 1) P)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) :
    ∀ i : ℕ, Integrable (prob_13_10_centeredIncrements X μ (i + 1)) P := by
  intro i
  exact (prob_13_10_integrable_from_identDistrib
    (P := P) (X := X) hX1Integrable hIdent (i + 1)).sub
      (integrable_const μ)

theorem prob_13_10_centeredIncrements_zero_mean {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hX1Integrable : Integrable (X 1) P)
    (hMeanOne : ∫ ω, X 1 ω ∂P = μ)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) :
    ∀ i : ℕ, ∫ ω, prob_13_10_centeredIncrements X μ (i + 1) ω ∂P = 0 := by
  intro i
  have hXiInt :
      Integrable (X (i + 1)) P :=
    prob_13_10_integrable_from_identDistrib
      (P := P) (X := X) hX1Integrable hIdent (i + 1)
  have hMean :
      ∫ ω, X (i + 1) ω ∂P = μ :=
    prob_13_10_mean_from_identDistrib
      (P := P) (X := X) (μ := μ) hMeanOne hIdent (i + 1)
  change ∫ ω, X (i + 1) ω - μ ∂P = 0
  rw [integral_sub hXiInt (integrable_const μ), hMean]
  simp

theorem prob_13_10_centered_iid_random_walk_martingale {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hXStrong : ∀ k : ℕ, StronglyMeasurable (X k))
    (hX1Integrable : Integrable (X 1) P)
    (hMeanOne : ∫ ω, X 1 ω ∂P = μ)
    (hIID : prob_13_10_iid_sequence P X) :
    def_13_7 P
      (prob_13_10_oneIndexedNaturalFiltration
        (prob_13_10_centeredIncrements X μ))
      (prob_13_10_centeredWalk X μ) := by
  have hYsm :
      ∀ i : ℕ, StronglyMeasurable
        (prob_13_10_centeredIncrements X μ i) := by
    intro i
    exact (hXStrong i).sub stronglyMeasurable_const
  have hYint :
      ∀ i : ℕ, Integrable
        (prob_13_10_centeredIncrements X μ (i + 1)) P :=
    prob_13_10_centeredIncrements_integrable
      (P := P) X μ hX1Integrable hIID.2
  have hYind :
      ProbabilityTheory.iIndepFun
        (fun i : ℕ => prob_13_10_centeredIncrements X μ (i + 1)) P :=
    prob_13_10_centeredIncrements_iIndep X μ hIID.1
  have hYzero :
      ∀ i : ℕ, ∫ ω,
        prob_13_10_centeredIncrements X μ (i + 1) ω ∂P = 0 :=
    prob_13_10_centeredIncrements_zero_mean
      (P := P) X μ hX1Integrable hMeanOne hIID.2
  simpa [prob_13_10_centeredWalk] using
    prob_13_10_partialSum_martingale_of_iid_zeroMean (P := P)
      (Y := prob_13_10_centeredIncrements X μ)
      hYsm hYint hYind hYzero

theorem prob_13_10_centered_abs_increment_condExp {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hXStrong : ∀ k : ℕ, StronglyMeasurable (X k))
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ∀ n : ℕ,
      P[fun ω =>
          |prob_13_10_centeredIncrements X μ (n + 1) ω| |
        prob_13_10_oneIndexedNaturalFiltration
          (prob_13_10_centeredIncrements X μ) n] =ᵐ[P]
        fun _ => ∫ ω,
          |prob_13_10_centeredIncrements X μ (n + 1) ω| ∂P := by
  let Y := prob_13_10_centeredIncrements X μ
  have hYsm : ∀ i : ℕ, StronglyMeasurable (Y i) := by
    intro i
    exact (hXStrong i).sub stronglyMeasurable_const
  have hYind :
      ProbabilityTheory.iIndepFun (fun i : ℕ => Y (i + 1)) P :=
    prob_13_10_centeredIncrements_iIndep X μ hIndep
  intro n
  cases n with
  | zero =>
      change P[fun ω => |Y 1 ω| | ⊥] =ᵐ[P]
        fun _ => ∫ ω, |Y 1 ω| ∂P
      rw [condExp_bot (μ := P) (f := fun ω => |Y 1 ω|)]
  | succ n =>
      have heq :=
        prob_13_10_oneIndexedNaturalFiltration_succ_eq_mathlib Y
          (fun i => hYsm (i + 1)) n
      rw [heq]
      let Z : ℕ → Ω → ℝ := fun i ω => Y (i + 1) ω
      have hBaseIndep :
          ProbabilityTheory.Indep
            (MeasurableSpace.comap (Z (n + 1)) (borel ℝ))
            (Filtration.natural Z (fun i => hYsm (i + 1)) n) P := by
        simpa [Z] using
          (ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt
            (μ := P) (f := Z)
            (fun i => hYsm (i + 1)) hYind (Nat.lt_succ_self n))
      have hAbsLe :
          MeasurableSpace.comap (fun ω => |Z (n + 1) ω|) (borel ℝ) ≤
            MeasurableSpace.comap (Z (n + 1)) (borel ℝ) := by
        have hZ :
            @Measurable Ω ℝ
              (MeasurableSpace.comap (Z (n + 1)) (borel ℝ)) _
              (Z (n + 1)) :=
          Measurable.of_comap_le le_rfl
        exact (measurable_abs.comp hZ).comap_le
      have hAbsIndep :
          ProbabilityTheory.Indep
            (MeasurableSpace.comap (fun ω => |Z (n + 1) ω|) (borel ℝ))
            (Filtration.natural Z (fun i => hYsm (i + 1)) n) P :=
        ProbabilityTheory.indep_of_indep_of_le_left hBaseIndep hAbsLe
      have hAbsMeasLocal :
          @Measurable Ω ℝ
            (MeasurableSpace.comap (fun ω => |Z (n + 1) ω|) (borel ℝ)) _
            (fun ω => |Z (n + 1) ω|) :=
        Measurable.of_comap_le le_rfl
      have hAbsStrong :
          @MeasureTheory.StronglyMeasurable Ω ℝ _
            (MeasurableSpace.comap (fun ω => |Z (n + 1) ω|) (borel ℝ))
            (fun ω => |Z (n + 1) ω|) :=
        hAbsMeasLocal.stronglyMeasurable
      have hAmbient :
          MeasurableSpace.comap (fun ω => |Z (n + 1) ω|) (borel ℝ) ≤
            (inferInstance : MeasurableSpace Ω) :=
        by
          have hAbsAmbient :
              Measurable (fun ω => |Z (n + 1) ω|) := by
            simpa [Z, Real.norm_eq_abs] using
              (hYsm (n + 2)).norm.measurable
          exact hAbsAmbient.comap_le
      exact
        MeasureTheory.condExp_indep_eq
          (μ := P)
          (m₁ := MeasurableSpace.comap
            (fun ω => |Z (n + 1) ω|) (borel ℝ))
          (m₂ := Filtration.natural Z (fun i => hYsm (i + 1)) n)
          hAmbient
          (Filtration.le
            (Filtration.natural Z (fun i => hYsm (i + 1))) n)
          hAbsStrong hAbsIndep

theorem prob_13_10_centered_increment_conditional_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hXStrong : ∀ k : ℕ, StronglyMeasurable (X k))
    (hX1Integrable : Integrable (X 1) P)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ∃ c : ℝ,
      prob_13_10_relaxed_conditional_increment_bound P
        (prob_13_10_oneIndexedNaturalFiltration
          (prob_13_10_centeredIncrements X μ))
        (prob_13_10_centeredWalk X μ)
        c := by
  let Y := prob_13_10_centeredIncrements X μ
  let S := prob_13_10_centeredWalk X μ
  let c : ℝ := ∫ ω, |Y 1 ω| ∂P
  have _hcIntegrable : Integrable (fun ω => |Y 1 ω|) P := by
    simpa [Y, prob_13_10_centeredIncrements, Real.norm_eq_abs] using
      ((hX1Integrable.sub (integrable_const μ)).norm)
  refine ⟨c, ?_, ?_⟩
  · exact integral_nonneg (fun ω => abs_nonneg (Y 1 ω))
  · intro n
    have hCondAbs :=
      prob_13_10_centered_abs_increment_condExp
        (P := P) X μ hXStrong hIndep n
    have hDiff :
        (fun ω => |S (n + 1) ω - S n ω|)
          =ᵐ[P] fun ω => |Y (n + 1) ω| := by
      filter_upwards with ω
      have hStep :
          S (n + 1) ω = S n ω + Y (n + 1) ω := by
        simpa [S, prob_13_10_centeredWalk] using
          congrFun (prob_13_10_partialSum_succ Y n) ω
      rw [hStep]
      simp
    have hCondDiff :
        P[fun ω => |S (n + 1) ω - S n ω| |
          prob_13_10_oneIndexedNaturalFiltration Y n] =ᵐ[P]
        P[fun ω => |Y (n + 1) ω| |
          prob_13_10_oneIndexedNaturalFiltration Y n] :=
      condExp_congr_ae hDiff
    have hIntEq :
        ∫ ω, |Y (n + 1) ω| ∂P = c := by
      have hdist :
          ProbabilityTheory.IdentDistrib
            (fun ω => |Y (n + 1) ω|) (fun ω => |Y 1 ω|) P P := by
        simpa [Y, prob_13_10_centeredIncrements, Function.comp_def] using
          (hIdent (n + 1)).comp
            (measurable_abs.comp (measurable_id.sub measurable_const))
      exact hdist.integral_eq
    filter_upwards [hCondDiff, hCondAbs] with ω h1 h2
    rw [h1, h2, hIntEq]

theorem prob_13_10_centered_stoppedValueReal_eq_stoppedSum {Ω : Type*}
    [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ) :
    thm_13_18_stoppedValueReal
      (prob_13_10_centeredWalk X μ)
      (fun ω => (T ω : WithTop ℕ))
      = prob_13_10_stoppedSum (prob_13_10_centeredIncrements X μ) T := by
  funext ω
  simp [thm_13_18_stoppedValueReal, prob_13_10_centeredWalk,
    prob_13_10_centeredIncrements, prob_13_10_stoppedSum,
    prob_13_10_partialSum]

theorem prob_13_10_centered_stopping_time_stopped_sum_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕n : ℕ → MeasurableSpace Ω) (S : ℕ → Ω → ℝ)
    (T : Ω → ℕ) (c : ℝ)
    (hM : def_13_7 P 𝓕n S)
    (hT : def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)))
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hBound : prob_13_10_relaxed_conditional_increment_bound P 𝓕n S c)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    Integrable
      (thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ))) P := by
  have hFinite :
      ∀ᵐ ω ∂P, (T ω : WithTop ℕ) < ⊤ := by
    exact ae_of_all P (fun ω => WithTop.coe_lt_top (T ω))
  have hAgree :
      thm_13_18_stoppedValueAgreement P S
        (fun ω => (T ω : WithTop ℕ))
        (thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ))) :=
    thm_13_18_stoppedValueReal_agreement P S
      (fun ω => (T ω : WithTop ℕ))
  have hMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (def_13_9_stoppedProcess S (fun ω => (T ω : WithTop ℕ)) n) P := by
    intro n
    exact (thm_13_17_stoppedProcess_integrable hM hT n).aestronglyMeasurable
  have hDomination :
      ∃ G : Ω → ℝ,
        Integrable G P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P,
            |def_13_9_stoppedProcess S (fun ω => (T ω : WithTop ℕ)) n ω| ≤ G ω :=
    prob_13_10_relaxed_stoppedProcess_domination
      (P := P) (𝓕n := 𝓕n) (X := S) (T := T) (c := c)
      hM hT hSigmaFinite hBound hTIntegrable
  rcases hDomination with ⟨G, hGInt, hBoundG⟩
  have hLimit :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n : ℕ =>
            def_13_9_stoppedProcess S (fun ω => (T ω : WithTop ℕ)) n ω)
          atTop
          (𝓝 (thm_13_18_stoppedValueReal S
            (fun ω => (T ω : WithTop ℕ)) ω)) := by
    filter_upwards [hFinite, hAgree] with ω hFiniteω hAgreeω
    exact thm_13_18_stoppedProcess_tendsto_of_agreement S
      (fun ω => (T ω : WithTop ℕ))
      (thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ)))
      hFiniteω hAgreeω
  have hSM :
      AEStronglyMeasurable
        (thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ))) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeas hLimit
  have hNormBound :
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖def_13_9_stoppedProcess S (fun ω => (T ω : WithTop ℕ)) n ω‖
          ≤ G ω := by
    intro n
    filter_upwards [hBoundG n] with ω hω
    simpa [Real.norm_eq_abs] using hω
  exact ⟨hSM,
    hasFiniteIntegral_of_dominated_convergence
      hGInt.hasFiniteIntegral hNormBound hLimit⟩

theorem prob_13_10_centered_stopped_sum_expansion {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ)
    (hStoppedIntegrable : Integrable (prob_13_10_stoppedSum X T) P)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    ∫ ω, prob_13_10_stoppedSum (fun n ω => X n ω - μ) T ω ∂P =
      ∫ ω, prob_13_10_stoppedSum X T ω ∂P -
        μ * ∫ ω, (T ω : ℝ) ∂P := by
  have hPoint :
      prob_13_10_stoppedSum (fun n ω => X n ω - μ) T
        =ᵐ[P]
      fun ω => prob_13_10_stoppedSum X T ω - μ * (T ω : ℝ) := by
    filter_upwards with ω
    exact prob_13_10_stoppedSum_centered_eq X T μ ω
  calc
    ∫ ω, prob_13_10_stoppedSum (fun n ω => X n ω - μ) T ω ∂P
        = ∫ ω, (prob_13_10_stoppedSum X T ω - μ * (T ω : ℝ)) ∂P := by
          exact integral_congr_ae hPoint
    _ = ∫ ω, prob_13_10_stoppedSum X T ω ∂P -
          ∫ ω, μ * (T ω : ℝ) ∂P := by
          exact integral_sub hStoppedIntegrable (hTIntegrable.const_mul μ)
    _ = ∫ ω, prob_13_10_stoppedSum X T ω ∂P -
          μ * ∫ ω, (T ω : ℝ) ∂P := by
          rw [integral_const_mul]

theorem prob_13_10_stopping_time_wald {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ)
    (hXStrong : ∀ k : ℕ, StronglyMeasurable (X k))
    (hX1Integrable : Integrable (X 1) P)
    (hMeanOne : ∫ ω, X 1 ω ∂P = μ)
    (hIID : prob_13_10_iid_sequence P X)
    (hT :
      def_13_8
        (prob_13_10_oneIndexedNaturalFiltration
          (prob_13_10_centeredIncrements X μ))
        (fun ω => (T ω : WithTop ℕ)))
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    prob_13_10_waldIdentity
      (∫ ω, prob_13_10_stoppedSum X T ω ∂P)
      μ
      (∫ ω, (T ω : ℝ) ∂P) := by
  let 𝓕n : ℕ → MeasurableSpace Ω :=
    prob_13_10_oneIndexedNaturalFiltration (prob_13_10_centeredIncrements X μ)
  let S : ℕ → Ω → ℝ := prob_13_10_centeredWalk X μ
  have hM : def_13_7 P 𝓕n S := by
    simpa [𝓕n, S] using
      prob_13_10_centered_iid_random_walk_martingale
        (P := P) (X := X) (μ := μ)
        hXStrong hX1Integrable hMeanOne hIID
  have hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)) := by
    intro n
    infer_instance
  rcases prob_13_10_centered_increment_conditional_bound
      (P := P) (X := X) (μ := μ)
      hXStrong hX1Integrable hIID.2 hIID.1 with
    ⟨c, hBound⟩
  have hCenteredValueIntegrable :
      Integrable
        (thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ))) P :=
    prob_13_10_centered_stopping_time_stopped_sum_integrable
      (P := P) (𝓕n := 𝓕n) (S := S) (T := T) (c := c)
      hM hT hSigmaFinite hBound hTIntegrable
  have hCenteredStoppedIntegrable :
      Integrable (prob_13_10_stoppedSum
        (prob_13_10_centeredIncrements X μ) T) P := by
    exact hCenteredValueIntegrable.congr
      (ae_of_all P (fun ω =>
        congrFun
          (prob_13_10_centered_stoppedValueReal_eq_stoppedSum X T μ) ω))
  have hStoppedIntegrable : Integrable (prob_13_10_stoppedSum X T) P := by
    have hPoint :
        (fun ω =>
          prob_13_10_stoppedSum
            (prob_13_10_centeredIncrements X μ) T ω +
              μ * (T ω : ℝ))
          =ᵐ[P]
        prob_13_10_stoppedSum X T := by
      filter_upwards with ω
      have hcenter :=
        prob_13_10_stoppedSum_centered_eq X T μ ω
      change
        prob_13_10_stoppedSum (fun n ω => X n ω - μ) T ω +
          μ * (T ω : ℝ) =
        prob_13_10_stoppedSum X T ω
      rw [hcenter]
      ring
    exact
      (hCenteredStoppedIntegrable.add
        (hTIntegrable.const_mul μ)).congr hPoint
  have hExpansion :
      ∫ ω, prob_13_10_stoppedSum
          (prob_13_10_centeredIncrements X μ) T ω ∂P =
        ∫ ω, prob_13_10_stoppedSum X T ω ∂P -
          μ * ∫ ω, (T ω : ℝ) ∂P :=
    prob_13_10_centered_stopped_sum_expansion P X T μ
      hStoppedIntegrable hTIntegrable
  have hCenteredOptional :
      ∫ ω, prob_13_10_stoppedSum
          (prob_13_10_centeredIncrements X μ) T ω ∂P = 0 := by
    have hOptional :
        ∫ ω,
          thm_13_18_stoppedValueReal S (fun ω => (T ω : WithTop ℕ)) ω ∂P =
          ∫ ω, S 0 ω ∂P :=
      prob_13_10_relaxed_increment_optional_stopping
        (P := P) (𝓕n := 𝓕n) (X := S) (T := T) (c := c)
        hM hT hSigmaFinite hBound hTIntegrable
    calc
      ∫ ω, prob_13_10_stoppedSum
          (prob_13_10_centeredIncrements X μ) T ω ∂P
          =
        ∫ ω,
          thm_13_18_stoppedValueReal S
            (fun ω => (T ω : WithTop ℕ)) ω ∂P := by
          exact integral_congr_ae
            (ae_of_all P (fun ω =>
              (congrFun
                (prob_13_10_centered_stoppedValueReal_eq_stoppedSum X T μ)
                ω).symm))
      _ = ∫ ω, S 0 ω ∂P := hOptional
      _ = 0 := by
          simp [S, prob_13_10_centeredWalk, prob_13_10_partialSum]
  unfold prob_13_10_waldIdentity
  linarith
