import Mathlib
import ToyApollo.Output.def_1_2
import ToyApollo.Output.rs_stieltjes_step_support

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

/-- Problem 1.8(a): evaluation of the Riemann--Stieltjes integral against the
floor-function integrator on `[0,10]`. -/
theorem prob_1_8a :
    ∃ h : RSIntegrable (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10,
      rsIntegral (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 h = 385 := by
  simpa using rsIntegral_floor_square_0_10

private theorem sourceHypotheses_sqrt_id_0_2 :
    DarbouxRS.SourceHypotheses (0 : ℝ) 2 Real.sqrt (fun x : ℝ => x) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · refine ⟨Real.sqrt 2, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.2
  · refine ⟨0, ?_⟩
    rintro y ⟨x, _hx, rfl⟩
    exact Real.sqrt_nonneg x
  · intro x _hx y _hy hxy
    exact hxy

private theorem intervalIntegral_sqrt_0_2 :
    ∫ x in (0 : ℝ)..2, Real.sqrt x ∂(volume : Measure ℝ) =
      (4 * Real.sqrt 2) / 3 := by
  rw [show (fun x : ℝ => Real.sqrt x) = fun x : ℝ => x ^ ((1 : ℝ) / 2) by
    funext x
    rw [Real.sqrt_eq_rpow]]
  rw [integral_rpow (a := (0 : ℝ)) (b := 2) (r := (1 : ℝ) / 2)
    (Or.inl (by norm_num))]
  norm_num
  have hpow : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
    have hExp : ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) := by norm_num
    rw [hExp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [← Real.sqrt_eq_rpow]
  rw [hpow]
  ring

private theorem setIntegral_Icc_sqrt_volume_0_2 :
    ∫ x in Icc (0 : ℝ) 2, Real.sqrt x ∂(volume : Measure ℝ) =
      (4 * Real.sqrt 2) / 3 := by
  calc
    ∫ x in Icc (0 : ℝ) 2, Real.sqrt x ∂(volume : Measure ℝ) =
        ∫ x in (0 : ℝ)..2, Real.sqrt x ∂(volume : Measure ℝ) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
          exact (setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))).symm
    _ = (4 * Real.sqrt 2) / 3 := intervalIntegral_sqrt_0_2

private theorem integrableOn_Icc_sqrt_volume_0_2 :
    IntegrableOn Real.sqrt (Icc (0 : ℝ) 2) (volume : Measure ℝ) := by
  exact Real.continuous_sqrt.continuousOn.integrableOn_Icc

private theorem integrableOn_Icc_sqrt_stieltjes_id_0_2 :
    IntegrableOn Real.sqrt (Icc (0 : ℝ) 2) StieltjesFunction.id.measure := by
  rw [← Real.volume_eq_stieltjes_id]
  exact integrableOn_Icc_sqrt_volume_0_2

private theorem setIntegral_Icc_sqrt_stieltjes_id_0_2 :
    ∫ x in Icc (0 : ℝ) 2, Real.sqrt x ∂StieltjesFunction.id.measure =
      (4 * Real.sqrt 2) / 3 := by
  rw [← Real.volume_eq_stieltjes_id]
  exact setIntegral_Icc_sqrt_volume_0_2

namespace Prob18Identity

open DarbouxRS

/- Checked Nat views are confined to the finite-sum calculations below.  The
active partition, cell, and tag APIs remain `Fin`-native. -/
private def pointAtNat {a b : ℝ} (P : Partition a b) (i : ℕ) : ℝ :=
  if hi : i ≤ P.n then P.pts ⟨i, Nat.lt_succ_iff.mpr hi⟩ else b

private def upperStepAtNat {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < P.n then upperStep P f ⟨i, hi⟩ else 0

private def lowerStepAtNat {a b : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < P.n then lowerStep P f ⟨i, hi⟩ else 0

private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i ≤ P.n) :
    pointAtNat P i = P.pts ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  simp [pointAtNat, hi]

private lemma pointAtNat_zero {a b : ℝ} (P : Partition a b) : pointAtNat P 0 = a := by
  rw [pointAtNat_eq P (Nat.zero_le P.n)]
  simpa using P.pts_start

private lemma pointAtNat_end {a b : ℝ} (P : Partition a b) : pointAtNat P P.n = b := by
  rw [pointAtNat_eq P le_rfl]
  convert P.pts_end using 1
  congr 1

private lemma upperSum_eq_range {a b : ℝ} (P : Partition a b) (f α : ℝ → ℝ) :
    upperSum P f α = ∑ i ∈ Finset.range P.n,
      upperStepAtNat P f i * (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
  unfold upperSum
  calc
    (∑ i : Fin P.n,
        upperStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n,
          upperStepAtNat P f i.val *
            (α (pointAtNat P (i.val + 1)) - α (pointAtNat P i.val)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [upperStepAtNat, dif_pos i.isLt,
        pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
        pointAtNat_eq P (Nat.le_of_lt i.isLt)]
      rfl
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i => upperStepAtNat P f i *
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) P.n

private lemma lowerSum_eq_range {a b : ℝ} (P : Partition a b) (f α : ℝ → ℝ) :
    lowerSum P f α = ∑ i ∈ Finset.range P.n,
      lowerStepAtNat P f i * (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
  unfold lowerSum
  calc
    (∑ i : Fin P.n,
        lowerStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i : Fin P.n,
          lowerStepAtNat P f i.val *
            (α (pointAtNat P (i.val + 1)) - α (pointAtNat P i.val)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [lowerStepAtNat, dif_pos i.isLt,
        pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
        pointAtNat_eq P (Nat.le_of_lt i.isLt)]
      rfl
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun i => lowerStepAtNat P f i *
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) P.n

private lemma gapAtNat_le_mesh {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i < P.n) : pointAtNat P (i + 1) - pointAtNat P i ≤ P.mesh := by
  rw [pointAtNat_eq P (Nat.succ_le_of_lt hi), pointAtNat_eq P (Nat.le_of_lt hi)]
  simpa using DarbouxRS.partition_length_le_mesh P (⟨i, hi⟩ : Fin P.n)

private lemma pointAtNat_mem_Icc {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i ≤ P.n) : pointAtNat P i ∈ Icc a b := by
  rw [pointAtNat_eq P hi]
  exact partition_pts_mem_Icc_core P

private lemma pointAtNat_lt_succ {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i < P.n) : pointAtNat P i < pointAtNat P (i + 1) := by
  rw [pointAtNat_eq P (Nat.le_of_lt hi), pointAtNat_eq P (Nat.succ_le_of_lt hi)]
  apply P.strict_mono
  simp

private def sqrtPrimitive (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x * Real.sqrt x

private lemma sqrtPrimitive_sub_bounds {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.sqrt u * (v - u) ≤ sqrtPrimitive v - sqrtPrimitive u ∧
      sqrtPrimitive v - sqrtPrimitive u ≤ Real.sqrt v * (v - u) := by
  have hv : 0 ≤ v := le_trans hu huv
  let a : ℝ := Real.sqrt u
  let b : ℝ := Real.sqrt v
  have ha0 : 0 ≤ a := by dsimp [a]; exact Real.sqrt_nonneg u
  have hb0 : 0 ≤ b := by dsimp [b]; exact Real.sqrt_nonneg v
  have hab : a ≤ b := by dsimp [a, b]; exact Real.sqrt_le_sqrt huv
  have hu_eq : u = a ^ 2 := by
    dsimp [a]
    rw [Real.sq_sqrt hu]
  have hv_eq : v = b ^ 2 := by
    dsimp [b]
    rw [Real.sq_sqrt hv]
  have hF :
      sqrtPrimitive v - sqrtPrimitive u = (2 / 3 : ℝ) * (b ^ 3 - a ^ 3) := by
    dsimp [sqrtPrimitive]
    change (2 / 3 : ℝ) * v * b - (2 / 3 : ℝ) * u * a =
      (2 / 3 : ℝ) * (b ^ 3 - a ^ 3)
    rw [hu_eq, hv_eq]
    ring_nf
  have hLeft :
      Real.sqrt u * (v - u) = a * (b ^ 2 - a ^ 2) := by
    change a * (v - u) = a * (b ^ 2 - a ^ 2)
    rw [hu_eq, hv_eq]
  have hRight :
      Real.sqrt v * (v - u) = b * (b ^ 2 - a ^ 2) := by
    change b * (v - u) = b * (b ^ 2 - a ^ 2)
    rw [hu_eq, hv_eq]
  constructor
  · rw [hF, hLeft]
    have hpoly : 0 ≤ (b - a) ^ 2 * (2 * b + a) := by positivity
    nlinarith
  · rw [hF, hRight]
    have hpoly : 0 ≤ (b - a) ^ 2 * (b + 2 * a) := by positivity
    nlinarith

private lemma upperStep_sqrt_eq_right {P : Partition (0 : ℝ) 2} {i : ℕ}
    (hi : i < P.n) :
    upperStepAtNat P Real.sqrt i = Real.sqrt (pointAtNat P (i + 1)) := by
  let iFin : Fin P.n := ⟨i, hi⟩
  rw [upperStepAtNat, dif_pos hi,
    pointAtNat_eq P (Nat.succ_le_of_lt hi)]
  have hnonempty : (Real.sqrt '' subinterval P iFin).Nonempty := by
    refine ⟨Real.sqrt (P.pts iFin.succ), ?_⟩
    exact ⟨P.pts iFin.succ,
      ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩, rfl⟩
  have habove : BddAbove (Real.sqrt '' subinterval P iFin) := by
    refine ⟨Real.sqrt (P.pts iFin.succ), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.2
  unfold upperStep
  refine le_antisymm ?_ ?_
  · refine csSup_le hnonempty ?_
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.2
  · exact le_csSup habove
      ⟨P.pts iFin.succ,
        ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩, rfl⟩

private lemma lowerStep_sqrt_eq_left {P : Partition (0 : ℝ) 2} {i : ℕ}
    (hi : i < P.n) :
    lowerStepAtNat P Real.sqrt i = Real.sqrt (pointAtNat P i) := by
  let iFin : Fin P.n := ⟨i, hi⟩
  rw [lowerStepAtNat, dif_pos hi,
    pointAtNat_eq P (Nat.le_of_lt hi)]
  have hnonempty : (Real.sqrt '' subinterval P iFin).Nonempty := by
    refine ⟨Real.sqrt (P.pts iFin.castSucc), ?_⟩
    exact ⟨P.pts iFin.castSucc,
      ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩, rfl⟩
  have hbelow : BddBelow (Real.sqrt '' subinterval P iFin) := by
    refine ⟨Real.sqrt (P.pts iFin.castSucc), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.1
  unfold lowerStep
  refine le_antisymm ?_ ?_
  · exact csInf_le hbelow
      ⟨P.pts iFin.castSucc,
        ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩, rfl⟩
  · refine le_csInf hnonempty ?_
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.1

private lemma sqrtPrimitive_total_0_2 :
    sqrtPrimitive 2 - sqrtPrimitive 0 = (4 * Real.sqrt 2) / 3 := by
  dsimp [sqrtPrimitive]
  norm_num
  ring

private lemma lowerSum_sqrt_id_le_total (P : Partition (0 : ℝ) 2) :
    lowerSum P Real.sqrt (fun x : ℝ => x) ≤ sqrtPrimitive 2 - sqrtPrimitive 0 := by
  rw [lowerSum_eq_range]
  calc
    ∑ i ∈ Finset.range P.n,
        lowerStepAtNat P Real.sqrt i * ((fun x : ℝ => x) (pointAtNat P (i + 1)) -
          (fun x : ℝ => x) (pointAtNat P i))
        =
        ∑ i ∈ Finset.range P.n,
          Real.sqrt (pointAtNat P i) *
            (pointAtNat P (i + 1) - pointAtNat P i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [lowerStep_sqrt_eq_left (P := P) (i := i) (Finset.mem_range.mp hi)]
    _ ≤
        ∑ i ∈ Finset.range P.n,
          (sqrtPrimitive (pointAtNat P (i + 1)) -
            sqrtPrimitive (pointAtNat P i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_lt : i < P.n := Finset.mem_range.mp hi
          have hpi_nonneg : 0 ≤ pointAtNat P i :=
            (pointAtNat_mem_Icc P (Nat.le_of_lt hi_lt)).1
          have hmono : pointAtNat P i ≤ pointAtNat P (i + 1) :=
            le_of_lt (pointAtNat_lt_succ P hi_lt)
          exact (sqrtPrimitive_sub_bounds hpi_nonneg hmono).1
    _ = sqrtPrimitive 2 - sqrtPrimitive 0 := by
          simpa [pointAtNat_zero P, pointAtNat_end P] using
            (Finset.sum_range_sub (fun j => sqrtPrimitive (pointAtNat P j)) P.n)

private lemma total_le_upperSum_sqrt_id (P : Partition (0 : ℝ) 2) :
    sqrtPrimitive 2 - sqrtPrimitive 0 ≤ upperSum P Real.sqrt (fun x : ℝ => x) := by
  rw [upperSum_eq_range]
  calc
    sqrtPrimitive 2 - sqrtPrimitive 0 =
        ∑ i ∈ Finset.range P.n,
          (sqrtPrimitive (pointAtNat P (i + 1)) -
            sqrtPrimitive (pointAtNat P i)) := by
          simpa [pointAtNat_zero P, pointAtNat_end P] using
            (Finset.sum_range_sub (fun j => sqrtPrimitive (pointAtNat P j)) P.n).symm
    _ ≤
        ∑ i ∈ Finset.range P.n,
          Real.sqrt (pointAtNat P (i + 1)) *
            (pointAtNat P (i + 1) - pointAtNat P i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_lt : i < P.n := Finset.mem_range.mp hi
          have hpi_nonneg : 0 ≤ pointAtNat P i :=
            (pointAtNat_mem_Icc P (Nat.le_of_lt hi_lt)).1
          have hmono : pointAtNat P i ≤ pointAtNat P (i + 1) :=
            le_of_lt (pointAtNat_lt_succ P hi_lt)
          exact (sqrtPrimitive_sub_bounds hpi_nonneg hmono).2
    _ =
        ∑ i ∈ Finset.range P.n,
          upperStepAtNat P Real.sqrt i *
            ((fun x : ℝ => x) (pointAtNat P (i + 1)) -
              (fun x : ℝ => x) (pointAtNat P i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [upperStep_sqrt_eq_right (P := P) (i := i) (Finset.mem_range.mp hi)]

private lemma upper_lower_gap_sqrt_id_le (P : Partition (0 : ℝ) 2) :
    upperSum P Real.sqrt (fun x : ℝ => x) -
      lowerSum P Real.sqrt (fun x : ℝ => x) ≤ Real.sqrt 2 * P.mesh := by
  rw [upperSum_eq_range, lowerSum_eq_range]
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ i ∈ Finset.range P.n,
        (upperStepAtNat P Real.sqrt i *
            ((fun x : ℝ => x) (pointAtNat P (i + 1)) -
              (fun x : ℝ => x) (pointAtNat P i)) -
          lowerStepAtNat P Real.sqrt i *
            ((fun x : ℝ => x) (pointAtNat P (i + 1)) -
              (fun x : ℝ => x) (pointAtNat P i)))
        =
        ∑ i ∈ Finset.range P.n,
          ((Real.sqrt (pointAtNat P (i + 1)) - Real.sqrt (pointAtNat P i)) *
            (pointAtNat P (i + 1) - pointAtNat P i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [upperStep_sqrt_eq_right (P := P) (i := i) (Finset.mem_range.mp hi),
            lowerStep_sqrt_eq_left (P := P) (i := i) (Finset.mem_range.mp hi)]
          ring
    _ ≤
        ∑ i ∈ Finset.range P.n,
          ((Real.sqrt (pointAtNat P (i + 1)) - Real.sqrt (pointAtNat P i)) *
            P.mesh) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_lt : i < P.n := Finset.mem_range.mp hi
          have hsqrt_nonneg :
              0 ≤ Real.sqrt (pointAtNat P (i + 1)) -
                Real.sqrt (pointAtNat P i) := by
            exact sub_nonneg.mpr
              (Real.sqrt_le_sqrt (le_of_lt (pointAtNat_lt_succ P hi_lt)))
          exact mul_le_mul_of_nonneg_left (gapAtNat_le_mesh P hi_lt) hsqrt_nonneg
    _ = (∑ i ∈ Finset.range P.n,
          (Real.sqrt (pointAtNat P (i + 1)) - Real.sqrt (pointAtNat P i))) *
            P.mesh := by
          rw [Finset.sum_mul]
    _ = Real.sqrt 2 * P.mesh := by
          rw [Finset.sum_range_sub (fun j => Real.sqrt (pointAtNat P j)) P.n]
          simp [pointAtNat_zero P, pointAtNat_end P]

private lemma sqrt_two_mul_delta_lt {eps : ℝ} (heps : 0 < eps) :
    Real.sqrt 2 * (eps / (Real.sqrt 2 + 1)) < eps := by
  have hden_pos : 0 < Real.sqrt 2 + 1 := by positivity
  have hratio : Real.sqrt 2 / (Real.sqrt 2 + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith [Real.sqrt_nonneg (2 : ℝ)]
  have hmul := mul_lt_mul_of_pos_left hratio heps
  have hrewrite :
      eps * (Real.sqrt 2 / (Real.sqrt 2 + 1)) =
        Real.sqrt 2 * (eps / (Real.sqrt 2 + 1)) := by ring
  rwa [hrewrite, mul_one] at hmul

private theorem upperLowerCommonLimit_sqrt_id_0_2 :
    rsUpperLowerCommonLimit (0 : ℝ) 2 Real.sqrt (fun x : ℝ => x)
      ((4 * Real.sqrt 2) / 3) := by
  refine ⟨sourceHypotheses_sqrt_id_0_2, ?_⟩
  intro eps heps
  let δ : ℝ := eps / (Real.sqrt 2 + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hgap_le := upper_lower_gap_sqrt_id_le P
  have hgap_lt :
      upperSum P Real.sqrt (fun x : ℝ => x) -
        lowerSum P Real.sqrt (fun x : ℝ => x) < eps := by
    have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
    have hmesh_bound : Real.sqrt 2 * P.mesh < Real.sqrt 2 * δ :=
      mul_lt_mul_of_pos_left hmesh hsqrt2_pos
    exact lt_of_le_of_lt hgap_le
      (lt_trans hmesh_bound (by simpa [δ] using sqrt_two_mul_delta_lt heps))
  constructor
  · have htotal_le_upper := total_le_upperSum_sqrt_id P
    have hlower_le_total := lowerSum_sqrt_id_le_total P
    have hnonneg :
        0 ≤ upperSum P Real.sqrt (fun x : ℝ => x) -
          (sqrtPrimitive 2 - sqrtPrimitive 0) := sub_nonneg.mpr htotal_le_upper
    have hle :
        upperSum P Real.sqrt (fun x : ℝ => x) -
            (sqrtPrimitive 2 - sqrtPrimitive 0) ≤
          upperSum P Real.sqrt (fun x : ℝ => x) -
            lowerSum P Real.sqrt (fun x : ℝ => x) := by
      linarith
    have hlt :
        |upperSum P Real.sqrt (fun x : ℝ => x) -
            (sqrtPrimitive 2 - sqrtPrimitive 0)| < eps := by
      rw [abs_of_nonneg hnonneg]
      exact lt_of_le_of_lt hle hgap_lt
    simpa [sqrtPrimitive_total_0_2] using hlt
  · have htotal_le_upper := total_le_upperSum_sqrt_id P
    have hlower_le_total := lowerSum_sqrt_id_le_total P
    have hnonneg :
        0 ≤ (sqrtPrimitive 2 - sqrtPrimitive 0) -
          lowerSum P Real.sqrt (fun x : ℝ => x) := sub_nonneg.mpr hlower_le_total
    have hle :
        (sqrtPrimitive 2 - sqrtPrimitive 0) -
            lowerSum P Real.sqrt (fun x : ℝ => x) ≤
          upperSum P Real.sqrt (fun x : ℝ => x) -
            lowerSum P Real.sqrt (fun x : ℝ => x) := by
      linarith
    have hlt :
        |lowerSum P Real.sqrt (fun x : ℝ => x) -
            (sqrtPrimitive 2 - sqrtPrimitive 0)| < eps := by
      rw [abs_sub_comm, abs_of_nonneg hnonneg]
      exact lt_of_le_of_lt hle hgap_lt
    simpa [sqrtPrimitive_total_0_2] using hlt

/- The former direct tagged-sandwich proof used a second Nat tag interface.
Tagged convergence is now derived from the source upper/lower criterion.
private lemma lowerSum_le_taggedSum_sqrt_id (P : Partition (0 : ℝ) 2)
    (tags : ℕ → ℝ) (htags : tagsInPartition P tags) :
    lowerSum P Real.sqrt (fun x : ℝ => x) ≤
      taggedSum P tags Real.sqrt (fun x : ℝ => x) := by
  unfold lowerSum taggedSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have htag := htags i hi_lt
  have hsqrt : Real.sqrt (P.pts i) ≤ Real.sqrt (tags i) :=
    Real.sqrt_le_sqrt htag.1
  have hinc : 0 ≤ P.pts (i + 1) - P.pts i :=
    sub_nonneg.mpr (le_of_lt (P.strict_mono i hi_lt))
  rw [lowerStep_sqrt_eq_left (P := P) (i := i) hi_lt]
  exact mul_le_mul_of_nonneg_right hsqrt hinc

private lemma taggedSum_le_upperSum_sqrt_id (P : Partition (0 : ℝ) 2)
    (tags : ℕ → ℝ) (htags : tagsInPartition P tags) :
    taggedSum P tags Real.sqrt (fun x : ℝ => x) ≤
      upperSum P Real.sqrt (fun x : ℝ => x) := by
  unfold upperSum taggedSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have htag := htags i hi_lt
  have hsqrt : Real.sqrt (tags i) ≤ Real.sqrt (P.pts (i + 1)) :=
    Real.sqrt_le_sqrt htag.2
  have hinc : 0 ≤ P.pts (i + 1) - P.pts i :=
    sub_nonneg.mpr (le_of_lt (P.strict_mono i hi_lt))
  rw [upperStep_sqrt_eq_right (P := P) (i := i) hi_lt]
  exact mul_le_mul_of_nonneg_right hsqrt hinc

private theorem taggedCommonLimit_sqrt_id_0_2 :
    rsTaggedCommonLimit (0 : ℝ) 2 Real.sqrt (fun x : ℝ => x)
      ((4 * Real.sqrt 2) / 3) := by
  refine ⟨sourceHypotheses_sqrt_id_0_2, ?_⟩
  intro eps heps
  let δ : ℝ := eps / (Real.sqrt 2 + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hgap_le := upper_lower_gap_sqrt_id_le P
  have hgap_lt :
      upperSum P Real.sqrt (fun x : ℝ => x) -
        lowerSum P Real.sqrt (fun x : ℝ => x) < eps := by
    have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
    have hmesh_bound : Real.sqrt 2 * P.mesh < Real.sqrt 2 * δ :=
      mul_lt_mul_of_pos_left hmesh hsqrt2_pos
    exact lt_of_le_of_lt hgap_le
      (lt_trans hmesh_bound (by simpa [δ] using sqrt_two_mul_delta_lt heps))
  have hlower_le_total := lowerSum_sqrt_id_le_total P
  have htotal_le_upper := total_le_upperSum_sqrt_id P
  have hlower_le_tag := lowerSum_le_taggedSum_sqrt_id P tags htags
  have htag_le_upper := taggedSum_le_upperSum_sqrt_id P tags htags
  have hleft_le :
      (sqrtPrimitive 2 - sqrtPrimitive 0) -
          taggedSum P tags Real.sqrt (fun x : ℝ => x) ≤
        upperSum P Real.sqrt (fun x : ℝ => x) -
          lowerSum P Real.sqrt (fun x : ℝ => x) := by
    linarith
  have hright_le :
      taggedSum P tags Real.sqrt (fun x : ℝ => x) -
          (sqrtPrimitive 2 - sqrtPrimitive 0) ≤
        upperSum P Real.sqrt (fun x : ℝ => x) -
          lowerSum P Real.sqrt (fun x : ℝ => x) := by
    linarith
  have hleft_lt :
      (sqrtPrimitive 2 - sqrtPrimitive 0) -
          taggedSum P tags Real.sqrt (fun x : ℝ => x) < eps :=
    lt_of_le_of_lt hleft_le hgap_lt
  have hright_lt :
      taggedSum P tags Real.sqrt (fun x : ℝ => x) -
          (sqrtPrimitive 2 - sqrtPrimitive 0) < eps :=
    lt_of_le_of_lt hright_le hgap_lt
  have habs :
      |taggedSum P tags Real.sqrt (fun x : ℝ => x) -
          (sqrtPrimitive 2 - sqrtPrimitive 0)| < eps := by
    apply abs_lt.mpr
    constructor
    · linarith
    · exact hright_lt
  simpa [sqrtPrimitive_total_0_2] using habs
-/

private theorem taggedCommonLimit_sqrt_id_0_2 :
    rsTaggedCommonLimit (0 : ℝ) 2 Real.sqrt (fun x : ℝ => x)
      ((4 * Real.sqrt 2) / 3) :=
  taggedCommonLimit_of_upperLowerCommonLimit upperLowerCommonLimit_sqrt_id_0_2

end Prob18Identity

/-- The identity-integrator contribution in Problem 1.8(b). -/
theorem prob_1_8_sqrt_id_0_2 :
    ∃ h : RSIntegrable Real.sqrt (fun x : ℝ => x) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => x) 0 2 h =
        (4 * Real.sqrt 2) / 3 := by
  let hW : RSIntegralWitness Real.sqrt (fun x : ℝ => x) 0 2 := {
    value := (4 * Real.sqrt 2) / 3
    source_limit := Prob18Identity.upperLowerCommonLimit_sqrt_id_0_2
  }
  let hRS : RSIntegrable Real.sqrt (fun x : ℝ => x) 0 2 := hW.toRSIntegrable
  refine ⟨hRS, ?_⟩
  exact DarbouxRS.taggedCommonLimit_unique (rsIntegral_spec hRS)
    Prob18Identity.taggedCommonLimit_sqrt_id_0_2

/-- Problem 1.8(b): evaluation of the Riemann--Stieltjes integral against
`floor x + x` on `[0,2]`. -/
theorem prob_1_8b :
    ∃ h : RSIntegrable Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2 h =
        1 + (7 * Real.sqrt 2) / 3 := by
  obtain ⟨hFloor, hFloorVal⟩ := rsIntegral_sqrt_floor_0_2
  obtain ⟨hId, hIdVal⟩ := prob_1_8_sqrt_id_0_2
  refine ⟨rsIntegrable_integrator_add hFloor hId, ?_⟩
  rw [rsIntegral_integrator_add hFloor hId, hFloorVal, hIdVal]
  ring

/-- Combined answer for Problem 1.8. -/
theorem prob_1_8 :
    (∃ h : RSIntegrable (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10,
      rsIntegral (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 h = 385) ∧
    (∃ h : RSIntegrable Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2 h =
        1 + (7 * Real.sqrt 2) / 3) := by
  exact ⟨prob_1_8a, prob_1_8b⟩
