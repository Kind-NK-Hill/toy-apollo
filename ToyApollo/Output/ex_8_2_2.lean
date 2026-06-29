/-
TASK ID: ex_8_2_2
TYPE: Example_Proof
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory intervalIntegral Filter

noncomputable section

def ex822Integrand (x y : ℝ) : ℝ :=
  (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2

lemma ex822_denom_ne_zero_x {x y : ℝ} (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  nlinarith [sq_nonneg x, hy2]

lemma ex822_denom_ne_zero_y {x y : ℝ} (hx : x ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith [hx2, sq_nonneg y]

lemma ex822_hasDerivAt_x (y x : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun u : ℝ => -u / (u ^ 2 + y ^ 2)) (ex822Integrand x y) x := by
  have hnum : HasDerivAt (fun u : ℝ => -u) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hden : HasDerivAt (fun u : ℝ => u ^ 2 + y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  have hneq : x ^ 2 + y ^ 2 ≠ 0 := ex822_denom_ne_zero_x hy
  convert hnum.div hden hneq using 1
  · unfold ex822Integrand
    field_simp [hneq]
    ring_nf

lemma ex822_hasDerivAt_y (x y : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => u / (x ^ 2 + u ^ 2)) (ex822Integrand x y) y := by
  have hnum : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
  have hden : HasDerivAt (fun u : ℝ => x ^ 2 + u ^ 2) (2 * y) y := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id y).pow 2 |>.const_add (x ^ 2)
  have hneq : x ^ 2 + y ^ 2 ≠ 0 := ex822_denom_ne_zero_y hx
  convert hnum.div hden hneq using 1
  · unfold ex822Integrand
    field_simp [hneq]
    ring_nf

lemma ex822_continuous_x (y : ℝ) (hy : y ≠ 0) :
    Continuous fun x : ℝ => ex822Integrand x y := by
  have hnum : Continuous fun x : ℝ => x ^ 2 - y ^ 2 := by
    continuity
  have hden : Continuous fun x : ℝ => (x ^ 2 + y ^ 2) ^ 2 := by
    continuity
  have hden0 : ∀ x : ℝ, (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    intro x
    exact pow_ne_zero 2 (ex822_denom_ne_zero_x hy)
  exact hnum.div hden hden0

lemma ex822_continuous_y (x : ℝ) (hx : x ≠ 0) :
    Continuous fun y : ℝ => ex822Integrand x y := by
  have hnum : Continuous fun y : ℝ => x ^ 2 - y ^ 2 := by
    continuity
  have hden : Continuous fun y : ℝ => (x ^ 2 + y ^ 2) ^ 2 := by
    continuity
  have hden0 : ∀ y : ℝ, (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    intro y
    exact pow_ne_zero 2 (ex822_denom_ne_zero_y hx)
  exact hnum.div hden hden0

lemma ex822_inner_x (y : ℝ) (hy : y ≠ 0) :
    ∫ x in (0 : ℝ)..1, ex822Integrand x y = -(1 / (1 + y ^ 2)) := by
  have hint : IntervalIntegrable (fun x : ℝ => ex822Integrand x y) volume 0 1 :=
    (ex822_continuous_x y hy).intervalIntegrable 0 1
  have hmain :
      ∫ x in (0 : ℝ)..1, ex822Integrand x y =
        (-1 / (1 ^ 2 + y ^ 2)) - (-0 / (0 ^ 2 + y ^ 2)) := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => ex822_hasDerivAt_x y x hy) hint)
  have hy2 : y ^ 2 ≠ 0 := by exact pow_ne_zero 2 hy
  calc
    ∫ x in (0 : ℝ)..1, ex822Integrand x y
        = (-1 / (1 ^ 2 + y ^ 2)) - (-0 / (0 ^ 2 + y ^ 2)) := hmain
    _ = -(1 / (1 + y ^ 2)) := by
      have hy2' : (0 : ℝ) ^ 2 + y ^ 2 ≠ 0 := by simpa using ex822_denom_ne_zero_x hy (x := 0)
      field_simp [hy2, hy2']
      ring

lemma ex822_inner_y (x : ℝ) (hx : x ≠ 0) :
    ∫ y in (0 : ℝ)..1, ex822Integrand x y = 1 / (1 + x ^ 2) := by
  have hint : IntervalIntegrable (fun y : ℝ => ex822Integrand x y) volume 0 1 :=
    (ex822_continuous_y x hx).intervalIntegrable 0 1
  have hmain :
      ∫ y in (0 : ℝ)..1, ex822Integrand x y =
        (1 / (x ^ 2 + 1 ^ 2)) - (0 / (x ^ 2 + 0 ^ 2)) := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => ex822_hasDerivAt_y x y hx) hint)
  have hx2 : x ^ 2 ≠ 0 := by exact pow_ne_zero 2 hx
  calc
    ∫ y in (0 : ℝ)..1, ex822Integrand x y
        = (1 / (x ^ 2 + 1 ^ 2)) - (0 / (x ^ 2 + 0 ^ 2)) := hmain
    _ = 1 / (1 + x ^ 2) := by
      have hx2' : x ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by simpa using ex822_denom_ne_zero_y hx (y := 0)
      field_simp [hx2, hx2']
      ring

lemma ex822_outer_x_formula {ε : ℝ} (hε : 0 < ε) :
    ∫ y in ε..1, (∫ x in (0 : ℝ)..1, ex822Integrand x y) = Real.arctan ε - Real.pi / 4 := by
  have hEq :
      Set.EqOn (fun y : ℝ => ∫ x in (0 : ℝ)..1, ex822Integrand x y)
        (fun y : ℝ => -(1 / (1 + y ^ 2))) (Set.uIcc ε 1) := by
    intro y hy
    have hmin : 0 < min ε 1 := by
      refine lt_min hε ?_
      norm_num
    have hypos : 0 < y := lt_of_lt_of_le hmin hy.1
    exact ex822_inner_x y (by linarith)
  rw [intervalIntegral.integral_congr hEq]
  calc
    ∫ y in ε..1, -(1 / (1 + y ^ 2)) = -∫ y in ε..1, (1 + y ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_neg]
      congr with y
      field_simp
    _ = -(Real.arctan 1 - Real.arctan ε) := by
      rw [integral_inv_one_add_sq]
    _ = Real.arctan ε - Real.pi / 4 := by
      rw [Real.arctan_one]
      ring_nf

lemma ex822_outer_y_formula {ε : ℝ} (hε : 0 < ε) :
    ∫ x in ε..1, (∫ y in (0 : ℝ)..1, ex822Integrand x y) = Real.pi / 4 - Real.arctan ε := by
  have hEq :
      Set.EqOn (fun x : ℝ => ∫ y in (0 : ℝ)..1, ex822Integrand x y)
        (fun x : ℝ => 1 / (1 + x ^ 2)) (Set.uIcc ε 1) := by
    intro x hx
    have hmin : 0 < min ε 1 := by
      refine lt_min hε ?_
      norm_num
    have hxpos : 0 < x := lt_of_lt_of_le hmin hx.1
    exact ex822_inner_y x (by linarith)
  rw [intervalIntegral.integral_congr hEq]
  calc
    ∫ x in ε..1, 1 / (1 + x ^ 2) = ∫ x in ε..1, (1 + x ^ 2)⁻¹ := by
      congr with x
      field_simp
    _ = Real.arctan 1 - Real.arctan ε := integral_inv_one_add_sq
    _ = Real.pi / 4 - Real.arctan ε := by rw [Real.arctan_one]

theorem ex_8_2_2 :
    Filter.Tendsto (fun ε : ℝ => ∫ y in ε..1, ∫ x in (0 : ℝ)..1, ex822Integrand x y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-(Real.pi / 4))) ∧
      Filter.Tendsto (fun ε : ℝ => ∫ x in ε..1, ∫ y in (0 : ℝ)..1, ex822Integrand x y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.pi / 4)) := by
  refine ⟨?_, ?_⟩
  · have hEq :
        (fun ε : ℝ => ∫ y in ε..1, ∫ x in (0 : ℝ)..1, ex822Integrand x y) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun ε : ℝ => Real.arctan ε - Real.pi / 4) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ex822_outer_x_formula hε
    have hBase :
        Filter.Tendsto (fun ε : ℝ => Real.arctan ε - Real.pi / 4)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-(Real.pi / 4))) := by
      simpa [Real.arctan_zero] using
        (((Real.continuous_arctan.continuousAt).tendsto.sub_const (Real.pi / 4)).mono_left inf_le_left :
          Filter.Tendsto (fun ε : ℝ => Real.arctan ε - Real.pi / 4)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.arctan 0 - Real.pi / 4)))
    exact hBase.congr' hEq.symm
  · have hEq :
        (fun ε : ℝ => ∫ x in ε..1, ∫ y in (0 : ℝ)..1, ex822Integrand x y) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun ε : ℝ => Real.pi / 4 - Real.arctan ε) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ex822_outer_y_formula hε
    have hBase :
        Filter.Tendsto (fun ε : ℝ => Real.pi / 4 - Real.arctan ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.pi / 4)) := by
      simpa [Real.arctan_zero] using
        (((tendsto_const_nhds.sub (Real.continuous_arctan.continuousAt.tendsto)).mono_left inf_le_left) :
          Filter.Tendsto (fun ε : ℝ => Real.pi / 4 - Real.arctan ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.pi / 4 - Real.arctan 0)))
    exact hBase.congr' hEq.symm
