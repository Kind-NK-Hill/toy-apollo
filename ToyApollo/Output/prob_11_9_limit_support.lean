/-
TASK ID: prob_11_9_limit_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_11_9_moment_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

def prob_11_9_asymptoticRegime (boxes k : ℕ → ℕ) (a : ℝ) : Prop :=
  (∀ n : ℕ, 0 < boxes n) ∧
    Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop ∧
    0 < a ∧
    Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ)) atTop (nhds a)

theorem prob_11_9_occupancy_moment_calculation_internal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    Tendsto
      (fun n : ℕ =>
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
          (fun _ : Ω => Real.exp (-a)) 2 n)
      atTop (nhds 0) := by
  classical
  rcases hRegime with ⟨hboxpos, hboxes, _ha, hratio⟩
  let c0 : ℝ := Real.exp (-a)
  let p1 : ℕ → ℝ :=
    fun n : ℕ => (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let p2 : ℕ → ℝ :=
    fun n : ℕ => (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let second : ℕ → ℝ :=
    fun n : ℕ => p1 n / (boxes n : ℝ) +
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) * p2 n
  let centered : ℕ → ℝ :=
    fun n : ℕ => second n - (2 * c0) * p1 n + c0 ^ 2
  have hp1raw :
      Tendsto (fun n : ℕ => (1 - (1 : ℝ) / (boxes n : ℝ)) ^ k n)
        atTop (nhds c0) := by
    simpa [c0] using
      prob_11_9_tendsto_one_sub_const_div_pow
        (boxes := boxes) (k := k) (a := a) (c := (1 : ℝ))
        (by norm_num) hboxes hratio
  have hp1 : Tendsto p1 atTop (nhds c0) := by
    refine hp1raw.congr' ?_
    filter_upwards with n
    have hle : 1 ≤ boxes n := Nat.succ_le_of_lt (hboxpos n)
    have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hboxpos n)
    dsimp [p1]
    congr 1
    have hsub : ((boxes n - 1 : ℕ) : ℝ) = (boxes n : ℝ) - 1 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hp2raw :
      Tendsto (fun n : ℕ => (1 - (2 : ℝ) / (boxes n : ℝ)) ^ k n)
        atTop (nhds (Real.exp (-(2 * a)))) := by
    simpa using
      prob_11_9_tendsto_one_sub_const_div_pow
        (boxes := boxes) (k := k) (a := a) (c := (2 : ℝ))
        (by norm_num) hboxes hratio
  have hp2 : Tendsto p2 atTop (nhds (Real.exp (-(2 * a)))) := by
    refine hp2raw.congr' ?_
    filter_upwards [hboxes.eventually_ge_atTop (2 : ℝ)] with n hge
    have hle : 2 ≤ boxes n := by exact_mod_cast hge
    have hposNat : 0 < boxes n := lt_of_lt_of_le (by norm_num : 0 < 2) hle
    have hbne : (boxes n : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hposNat
    dsimp [p2]
    congr 1
    have hsub : ((boxes n - 2 : ℕ) : ℝ) = (boxes n : ℝ) - 2 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (boxes n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using hboxes.inv_tendsto_atTop
  have hTerm1 :
      Tendsto (fun n : ℕ => p1 n / (boxes n : ℝ)) atTop (nhds 0) := by
    exact hp1.div_atTop hboxes
  have hCoefRaw :
      Tendsto (fun n : ℕ => 1 - (1 : ℝ) / (boxes n : ℝ))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hInv
  have hCoef :
      Tendsto
        (fun n : ℕ => (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)))
        atTop (nhds 1) := by
    refine hCoefRaw.congr' ?_
    filter_upwards with n
    have hle : 1 ≤ boxes n := Nat.succ_le_of_lt (hboxpos n)
    have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hboxpos n)
    have hsub : ((boxes n - 1 : ℕ) : ℝ) = (boxes n : ℝ) - 1 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hsecond :
      Tendsto second atTop (nhds (Real.exp (-(2 * a)))) := by
    dsimp [second]
    simpa using hTerm1.add (hCoef.mul hp2)
  have hlinear :
      Tendsto (fun n : ℕ => (2 * c0) * p1 n)
        atTop (nhds ((2 * c0) * c0)) := by
    simpa using tendsto_const_nhds.mul hp1
  have hcentered :
      Tendsto centered atTop (nhds 0) := by
    have hlim :
        Tendsto centered atTop
          (nhds (Real.exp (-(2 * a)) - (2 * c0) * c0 + c0 ^ 2)) := by
      dsimp [centered]
      exact (hsecond.sub hlinear).add tendsto_const_nhds
    have hexp2 : Real.exp (-(2 * a)) = c0 ^ 2 := by
      dsimp [c0]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    convert hlim using 1
    rw [hexp2]
    ring
  have hMomentEq :
      ∀ n : ℕ,
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
            (fun _ : Ω => Real.exp (-a)) 2 n =
          ENNReal.ofReal (centered n) := by
    intro n
    simpa [centered, second, p1, p2, c0] using
      (prob_11_9_meanDeviationMoment_eq_formula P boxes k X
        (c := Real.exp (-a)) hModel (hboxpos n) (hX n))
  have hEnn : Tendsto (fun n : ℕ => ENNReal.ofReal (centered n))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hcentered
  exact hEnn.congr' (Eventually.of_forall (fun n => (hMomentEq n).symm))
