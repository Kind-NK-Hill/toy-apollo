/-
TASK ID: ex_13_6_2
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_7
import ToyApollo.Output.ex_13_6_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

def ex_13_6_2_partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => ∑ i ∈ Finset.range n, Y (i + 1) ω

@[simp]
theorem ex_13_6_2_partialSum_zero {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    ex_13_6_2_partialSum Y 0 = 0 := by
  funext ω
  simp [ex_13_6_2_partialSum]

theorem ex_13_6_2_partialSum_succ {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    ex_13_6_2_partialSum Y (n + 1) =
      ex_13_6_2_partialSum Y n + Y (n + 1) := by
  funext ω
  simp [ex_13_6_2_partialSum, Finset.sum_range_succ]

abbrev ex_13_6_2_naturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  ex_13_6_1_naturalFiltration Y

theorem ex_13_6_2_sumHistory_measurable (n : ℕ) :
    Measurable (fun z : Fin n → ℝ => ∑ i : Fin n, z i) := by
  classical
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)

theorem ex_13_6_2_partialSum_adapted {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) :
    def_13_6_adapted (ex_13_6_2_naturalFiltration Y)
      (ex_13_6_2_partialSum Y) := by
  classical
  intro n
  cases n with
  | zero =>
      exact measurable_const
  | succ n =>
      let g : (Fin (n + 1) → ℝ) → ℝ := fun z => ∑ i : Fin (n + 1), z i
      have hg : Measurable g := ex_13_6_2_sumHistory_measurable (n + 1)
      have hhist :
          Measurable[ex_13_6_2_naturalFiltration Y (n + 1)]
            (ex_13_6_1_history Y (n + 1)) :=
        Measurable.of_comap_le le_rfl
      have hcomp :
          Measurable[ex_13_6_2_naturalFiltration Y (n + 1)]
            (g ∘ ex_13_6_1_history Y (n + 1)) :=
        hg.comp hhist
      convert hcomp using 1
      funext ω
      simp only [g, Function.comp_apply, ex_13_6_1_history,
        Finset.sum_fin_eq_sum_range, ex_13_6_2_partialSum]
      apply Finset.sum_congr rfl
      intro x hx
      have hxle : x ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
      simp [hxle]

theorem ex_13_6_2_partialSum_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P) :
    ∀ n : ℕ, Integrable (ex_13_6_2_partialSum Y n) P := by
  intro n
  unfold ex_13_6_2_partialSum
  exact integrable_finset_sum (Finset.range n) (fun i _ => hYint i)

def ex_13_6_2_fairIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ,
    P[Y (n + 1) | ex_13_6_2_naturalFiltration Y n] =ᵐ[P]
      (0 : Ω → ℝ)

theorem ex_13_6_2_naturalFiltration_succ_eq_mathlib {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y (i + 1))) (n : ℕ) :
    ex_13_6_2_naturalFiltration Y (n + 1) =
      Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n := by
  apply le_antisymm
  · have hhist :
        @Measurable Ω (Fin (n + 1) → ℝ)
          (Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n) _
          (ex_13_6_1_history Y (n + 1)) := by
      exact
        @measurable_pi_lambda Ω (Fin (n + 1)) (fun _ => ℝ)
          (Filtration.natural (fun i : ℕ => Y (i + 1)) hYsm n)
          (fun _ => borel ℝ) (ex_13_6_1_history Y (n + 1))
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
      ex_13_6_2_naturalFiltration Y (n + 1)
    refine iSup₂_le ?_
    intro j hj
    have hcoord :
        @Measurable Ω ℝ (ex_13_6_2_naturalFiltration Y (n + 1)) _
          (Y (j + 1)) := by
      have hhist :
          @Measurable Ω (Fin (n + 1) → ℝ)
            (ex_13_6_2_naturalFiltration Y (n + 1)) _
            (ex_13_6_1_history Y (n + 1)) :=
        ex_13_6_1_history_measurable_self Y (n + 1)
      have hcoord' :
          @Measurable Ω ℝ (ex_13_6_2_naturalFiltration Y (n + 1)) _
            ((fun z : Fin (n + 1) → ℝ =>
                z ⟨j, Nat.lt_succ_of_le hj⟩) ∘
              ex_13_6_1_history Y (n + 1)) :=
        (measurable_pi_apply ⟨j, Nat.lt_succ_of_le hj⟩).comp hhist
      simpa [ex_13_6_1_history, Function.comp_apply] using hcoord'
    exact hcoord.comap_le

theorem ex_13_6_2_fairIncrement_of_iIndep_zeroMean {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ}
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y i))
    (hiid : iIndepFun (fun i : ℕ => Y (i + 1)) P)
    (hzero : ∀ i : ℕ, ∫ ω, Y (i + 1) ω ∂P = 0) :
    ex_13_6_2_fairIncrement P Y := by
  intro n
  cases n with
  | zero =>
      change P[Y 1 | ⊥] =ᵐ[P] (0 : Ω → ℝ)
      rw [condExp_bot (μ := P) (f := Y 1), hzero 0]
      exact Filter.Eventually.of_forall fun _ => rfl
  | succ n =>
      have heq :=
        ex_13_6_2_naturalFiltration_succ_eq_mathlib Y
          (fun i => hYsm (i + 1)) n
      rw [heq]
      exact
        (iIndepFun.condExp_natural_ae_eq_of_lt
          (μ := P) (f := fun i : ℕ => Y (i + 1))
          (fun i => hYsm (i + 1)) hiid (Nat.lt_succ_self n)).trans
          (by
            rw [hzero (n + 1)]
            exact Filter.Eventually.of_forall fun _ => rfl)

theorem ex_13_6_2_oneStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_2_naturalFiltration Y))
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)))
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P)
    (hfair : ex_13_6_2_fairIncrement P Y) :
    def_13_7_oneStepCondition P (ex_13_6_2_naturalFiltration Y)
      (ex_13_6_2_partialSum Y) := by
  classical
  intro n
  have hS_succ :
      ex_13_6_2_partialSum Y (n + 1) =
        ex_13_6_2_partialSum Y n + Y (n + 1) :=
    ex_13_6_2_partialSum_succ Y n
  have hS_int :
      Integrable (ex_13_6_2_partialSum Y n) P :=
    ex_13_6_2_partialSum_integrable hYint n
  have hY_next_int : Integrable (Y (n + 1)) P := hYint n
  have hS_meas :
      Measurable[ex_13_6_2_naturalFiltration Y n]
        (ex_13_6_2_partialSum Y n) :=
    ex_13_6_2_partialSum_adapted Y n
  haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
  have hS_cond :
      P[ex_13_6_2_partialSum Y n | ex_13_6_2_naturalFiltration Y n] =
        ex_13_6_2_partialSum Y n :=
    condExp_of_stronglyMeasurable (hfiltration.1 n)
      hS_meas.stronglyMeasurable hS_int
  have hS_cond_ae :
      P[ex_13_6_2_partialSum Y n | ex_13_6_2_naturalFiltration Y n] =ᵐ[P]
        ex_13_6_2_partialSum Y n := by
    rw [hS_cond]
  calc
    P[ex_13_6_2_partialSum Y (n + 1) | ex_13_6_2_naturalFiltration Y n]
        =ᵐ[P] P[ex_13_6_2_partialSum Y n + Y (n + 1) |
          ex_13_6_2_naturalFiltration Y n] := by
          rw [hS_succ]
    _ =ᵐ[P]
        P[ex_13_6_2_partialSum Y n | ex_13_6_2_naturalFiltration Y n] +
          P[Y (n + 1) | ex_13_6_2_naturalFiltration Y n] :=
        condExp_add hS_int hY_next_int _
    _ =ᵐ[P] ex_13_6_2_partialSum Y n + (0 : Ω → ℝ) :=
        hS_cond_ae.add (hfair n)
    _ =ᵐ[P] ex_13_6_2_partialSum Y n := by
        simp

theorem ex_13_6_2 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hYsm : ∀ i : ℕ, StronglyMeasurable (Y i))
    (hYint : ∀ i : ℕ, Integrable (Y (i + 1)) P)
    (hiid : iIndepFun (fun i : ℕ => Y (i + 1)) P)
    (hzero : ∀ i : ℕ, ∫ ω, Y (i + 1) ω ∂P = 0) :
    def_13_7 P (ex_13_6_2_naturalFiltration Y)
      (ex_13_6_2_partialSum Y) := by
  have hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_2_naturalFiltration Y) :=
    ex_13_6_1_naturalFiltration_isFiltration Y
      (fun n => (hYsm n).measurable)
  have hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)) := by
    intro n
    infer_instance
  have hfair : ex_13_6_2_fairIncrement P Y :=
    ex_13_6_2_fairIncrement_of_iIndep_zeroMean hYsm hiid hzero
  exact ⟨hfiltration, ex_13_6_2_partialSum_integrable hYint,
    ex_13_6_2_partialSum_adapted Y,
    ex_13_6_2_oneStepCondition hfiltration hSigmaFinite hYint hfair⟩
