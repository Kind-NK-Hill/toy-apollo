/-
TASK ID: ex_7_2_3
TYPE: Example_Proof
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW
open Filter MeasureTheory Set Topology

def dctCounterexampleWindow (n : ℕ) : Set ℝ :=
  Set.Icc (n : ℝ) (n + 1)

noncomputable def dctCounterexampleSeq (n : ℕ) (x : ℝ) : ℝ :=
  (dctCounterexampleWindow n).indicator (fun _ => (1 : ℝ)) x

def dctCounterexampleLimit : ℝ → ℝ := fun _ => 0

structure DominatedConvergenceCounterexample where
  seq : ℕ → ℝ → ℝ
  seq_def : seq = dctCounterexampleSeq
  pointwiseLimit : ℝ → ℝ
  pointwiseLimit_def : pointwiseLimit = dctCounterexampleLimit
  pointwise_tendsto_zero : ∀ x, Tendsto (fun n => seq n x) atTop (nhds (pointwiseLimit x))
  integral_eq_one : ∀ n, ∫ x, seq n x ∂volume = 1
  integrals_tendsto_one : Tendsto (fun n => ∫ x, seq n x ∂volume) atTop (nhds 1)
  limit_integral_eq_zero : ∫ x, pointwiseLimit x ∂volume = 0
  no_integrable_dominator :
    ¬ ∃ Y : ℝ → ℝ, Integrable Y volume ∧ ∀ n x, seq n x ≤ Y x

theorem dctCounterexampleSeq_integral_eq_one (n : ℕ) :
    ∫ x, dctCounterexampleSeq n x ∂volume = 1 := by
  simpa [dctCounterexampleSeq, dctCounterexampleWindow] using
    (integral_indicator_one (μ := volume) (s := dctCounterexampleWindow n) measurableSet_Icc)

theorem dctCounterexampleSeq_eventually_zero (x : ℝ) :
    ∀ᶠ n in atTop, dctCounterexampleSeq n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxlt : x < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hxnot : x ∉ dctCounterexampleWindow n := by
    intro hx
    exact not_lt_of_ge hx.1 hxlt
  rw [dctCounterexampleSeq, Set.indicator_of_notMem hxnot]

theorem dctCounterexampleSeq_tendsto_zero (x : ℝ) :
    Tendsto (fun n => dctCounterexampleSeq n x) atTop (nhds 0) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  exact (dctCounterexampleSeq_eventually_zero x).mono fun n hn => hn.symm

theorem dctCounterexampleIntegrals_tendsto_one :
    Tendsto (fun n => ∫ x, dctCounterexampleSeq n x ∂volume) atTop (nhds 1) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  exact Filter.Eventually.of_forall fun n => (dctCounterexampleSeq_integral_eq_one n).symm

theorem dctCounterexampleLimit_integral_eq_zero :
    ∫ x, dctCounterexampleLimit x ∂volume = 0 := by
  simp [dctCounterexampleLimit]

theorem no_integrable_dctCounterexample_dominator :
    ¬ ∃ Y : ℝ → ℝ, Integrable Y volume ∧ ∀ n x, dctCounterexampleSeq n x ≤ Y x := by
  rintro ⟨Y, hYint, hdom⟩
  have hY_on : Integrable Y (volume.restrict (Set.Ici (0 : ℝ))) :=
    hYint.mono_measure Measure.restrict_le_self
  have hconst_on : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ici (0 : ℝ))) := by
    refine Integrable.mono' hY_on ?_ ?_
    · simpa using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ))
          (volume.restrict (Set.Ici (0 : ℝ))))
    · rw [ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall fun x hx => by
        have hfloor_mem : x ∈ dctCounterexampleWindow ⌊x⌋₊ := by
          constructor
          · exact Nat.floor_le hx
          · exact (Nat.lt_floor_add_one x).le
        have hseq_eq : dctCounterexampleSeq ⌊x⌋₊ x = 1 := by
          rw [dctCounterexampleSeq, Set.indicator_of_mem hfloor_mem]
        have hdom_here := hdom ⌊x⌋₊ x
        simpa [hseq_eq] using hdom_here
  have hconst_on_set : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici (0 : ℝ)) volume := by
    simpa [IntegrableOn] using hconst_on
  have hnot : ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici (0 : ℝ)) volume := by
    rw [integrableOn_const_iff]
    simp
  exact hnot hconst_on_set

noncomputable def ex_7_2_3 : DominatedConvergenceCounterexample where
  seq := dctCounterexampleSeq
  seq_def := rfl
  pointwiseLimit := dctCounterexampleLimit
  pointwiseLimit_def := rfl
  pointwise_tendsto_zero := dctCounterexampleSeq_tendsto_zero
  integral_eq_one := dctCounterexampleSeq_integral_eq_one
  integrals_tendsto_one := dctCounterexampleIntegrals_tendsto_one
  limit_integral_eq_zero := dctCounterexampleLimit_integral_eq_zero
  no_integrable_dominator := no_integrable_dctCounterexample_dominator
