import Mathlib
import ToyApollo.Output.def_10_4

/-
TASK ID: prob_10_9
TYPE: Problem
SOURCE PLAN: chapter10-problems
TASK CONTENT:
\textbf{10.9.} Let $X_n$ be geometrically distributed random variable with pmf
\[
P(X_n=k)=\frac{1}{n}\left(1-\frac{1}{n}\right)^{k-1},
\qquad k=1,2,3,\ldots.
\]
Show that $X_n/n$ converges to the exponential distribution with mean $1$ in distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

/-- The cdf of the exponential distribution with mean one. -/
noncomputable def exponentialMeanOneCdf (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-x)

/-- The source cdf of `X_N / N` when `X_N` is geometric with success
probability `1 / N`.  Lean uses `N = n + 1`.  For `x ≥ 0`,
`floor(N x)` is the largest positive-integer cutoff in the event
`X_N / N ≤ x`, and the geometric finite sum gives
`1 - (1 - 1/N) ^ floor(N x)`. -/
noncomputable def prob_10_9_scaledGeometricCdf (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then
    0
  else
    1 - (1 + (-1 : ℝ) / ((n : ℝ) + 1)) ^ Nat.floor (((n : ℝ) + 1) * x)

private lemma prob_10_9_geom_tail_eq_exp_log (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (1 + (-1 : ℝ) / ((n : ℝ) + 1)) ^
        Nat.floor (((n : ℝ) + 1) * x) =
      Real.exp
        ((Nat.floor (((n : ℝ) + 1) * x) : ℝ) *
          Real.log (1 + (-1 : ℝ) / ((n : ℝ) + 1))) := by
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hNgt : 1 < (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_lt_succ hn
  have hbasepos : 0 < 1 + (-1 : ℝ) / ((n : ℝ) + 1) := by
    have hbase_eq :
        1 + (-1 : ℝ) / ((n : ℝ) + 1) =
          (((n : ℝ) + 1) - 1) / ((n : ℝ) + 1) := by
      field_simp [hNpos.ne']
      ring
    rw [hbase_eq]
    exact div_pos (sub_pos.mpr hNgt) hNpos
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hbasepos]
  ring

private lemma prob_10_9_floor_ratio_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ =>
        (Nat.floor (((n : ℝ) + 1) * x) : ℝ) / ((n : ℝ) + 1))
      atTop (nhds x) := by
  have hN : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop (atTop : Filter ℝ) := by
    simpa using
      (tendsto_atTop_add_const_right (atTop : Filter ℕ) (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hfloor :
      Tendsto (fun y : ℝ => (Nat.floor (x * y) : ℝ) / y)
        atTop (nhds x) :=
    tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := x) hx
  simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor.comp hN

private lemma prob_10_9_log_base_tendsto :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) * Real.log (1 + (-1 : ℝ) / ((n : ℝ) + 1)))
      atTop (nhds (-1 : ℝ)) := by
  have hN : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop (atTop : Filter ℝ) := by
    simpa using
      (tendsto_atTop_add_const_right (atTop : Filter ℕ) (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hlog := (Real.tendsto_mul_log_one_add_div_atTop (-1 : ℝ)).comp hN
  simpa [Function.comp_def] using hlog

private lemma prob_10_9_log_tail_exponent_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ =>
        (Nat.floor (((n : ℝ) + 1) * x) : ℝ) *
          Real.log (1 + (-1 : ℝ) / ((n : ℝ) + 1)))
      atTop (nhds (-x)) := by
  have hmul :=
    (prob_10_9_floor_ratio_tendsto (x := x) hx).mul prob_10_9_log_base_tendsto
  have harg :
      Tendsto
        (fun n : ℕ =>
          (Nat.floor (((n : ℝ) + 1) * x) : ℝ) *
            Real.log (1 + (-1 : ℝ) / ((n : ℝ) + 1)))
        atTop (nhds (x * (-1 : ℝ))) := by
    refine hmul.congr' ?_
    filter_upwards with n
    have hNne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hNne]
  simpa using harg

private lemma prob_10_9_geom_tail_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ =>
        (1 + (-1 : ℝ) / ((n : ℝ) + 1)) ^
          Nat.floor (((n : ℝ) + 1) * x))
      atTop (nhds (Real.exp (-x))) := by
  have harg := prob_10_9_log_tail_exponent_tendsto (x := x) hx
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            ((Nat.floor (((n : ℝ) + 1) * x) : ℝ) *
              Real.log (1 + (-1 : ℝ) / ((n : ℝ) + 1))))
        atTop (nhds (Real.exp (-x))) :=
    (Real.continuous_exp.tendsto (-x)).comp harg
  refine hexp.congr' ?_
  filter_upwards
    [eventually_atTop.2
      ⟨1, fun n hn => (prob_10_9_geom_tail_eq_exp_log n hn x).symm⟩] with n hn
  exact hn

private lemma prob_10_9_scaledGeometricCdf_eq_zero_of_lt_zero {x : ℝ}
    (hx : x < 0) :
    (fun n : ℕ => prob_10_9_scaledGeometricCdf n x) = fun _ : ℕ => 0 := by
  funext n
  simp [prob_10_9_scaledGeometricCdf, hx]

private lemma prob_10_9_scaledGeometricCdf_tendsto_of_nonneg {x : ℝ}
    (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => prob_10_9_scaledGeometricCdf n x)
      atTop (nhds (1 - Real.exp (-x))) := by
  have htail := prob_10_9_geom_tail_tendsto (x := x) hx
  have hcdf :
      Tendsto
        (fun n : ℕ =>
          1 - (1 + (-1 : ℝ) / ((n : ℝ) + 1)) ^
            Nat.floor (((n : ℝ) + 1) * x))
        atTop (nhds (1 - Real.exp (-x))) :=
    tendsto_const_nhds.sub htail
  have hxnot : ¬ x < 0 := not_lt.mpr hx
  simpa [prob_10_9_scaledGeometricCdf, hxnot] using hcdf

/-- Problem 10.9: the cdfs of the scaled geometric variables `X_n / n`
converge to the exponential mean-one cdf. -/
theorem prob_10_9 :
    CdfConvergesInDistribution
      prob_10_9_scaledGeometricCdf exponentialMeanOneCdf := by
  intro x _hcont
  by_cases hxneg : x < 0
  · have hseq := prob_10_9_scaledGeometricCdf_eq_zero_of_lt_zero hxneg
    have hlim :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
          (nhds (exponentialMeanOneCdf x)) := by
      simpa [exponentialMeanOneCdf, hxneg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    simpa [hseq] using hlim
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    have hlim := prob_10_9_scaledGeometricCdf_tendsto_of_nonneg hxnonneg
    have htarget : exponentialMeanOneCdf x = 1 - Real.exp (-x) := by
      simp [exponentialMeanOneCdf, hxneg]
    simpa [htarget] using hlim
