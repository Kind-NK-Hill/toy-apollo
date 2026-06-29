import Mathlib
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.thm_11_5

/-
TASK ID: prob_11_7
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.7.} Let (Xi)\infty

i=1 be a sequence of random variables that may be correlated.

Suppose E [Xi]= \mu and V ar(Xi) \leq K for all i. Show that if there exists a sequence

of real numbers (a\tau)\tau\geq1 such that (i) a\tau \in[ 0, 1] for all \tau, (ii) a\tau decreases to 0 as

\tau increases, and (iii) Cov (Xi,Xi+\tau) \leq a\tau

\sqrt

Va r(Xi) Va r(Xi+\tau) for all i and \tau> 0,

then (Xi)\infty

i=1 converges in probability to \mu.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The covariance-decay hypotheses in Problem 11.7.  The conclusion concerns
sample averages; otherwise the printed OCR text would state a false claim about
the individual variables `X_i` themselves. -/
def prob_11_7_covarianceDecayAssumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ) : Prop :=
  0 ≤ K ∧
    (∀ i : ℕ, MemLp (X i) 2 P) ∧
    (∀ τ : ℕ, 0 ≤ a τ ∧ a τ ≤ 1) ∧
    Tendsto a atTop (nhds 0) ∧
    (∀ i : ℕ, P[X i] = μ) ∧
    (∀ i : ℕ, _root_.variance P (X i) ≤ K) ∧
    (∀ i τ : ℕ, 0 < τ →
      Covariance P (X i) (X (i + τ)) ≤
        a τ * Real.sqrt (_root_.variance P (X i) * _root_.variance P (X (i + τ)))
    )

/-- Support statement for the standard proof of Problem 11.7: the covariance
decay assumptions imply that the variance of the sample average tends to zero,
and the sample averages have mean `μ`. -/
def prob_11_7_sampleMeanVarianceSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  (∀ n : ℕ, MemLp (thm_11_5_sampleMean X n) 2 P) ∧
    (∀ n : ℕ, P[thm_11_5_sampleMean X n] = μ) ∧
    Tendsto (fun n : ℕ => _root_.variance P (thm_11_5_sampleMean X n))
      atTop (nhds 0)

theorem prob_11_7_sampleMean_memLp_of_covarianceDecay {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) :
    ∀ n : ℕ, MemLp (thm_11_5_sampleMean X n) 2 P := by
  rcases hCovDecay with ⟨_hK, hMem, _ha_bound, _ha_lim, _hMean, _hVar, _hCov⟩
  intro n
  have hsum : MemLp (fun ω => ∑ i : Fin (n + 1), X i.1 ω) 2 P := by
    simpa using
      (memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => hMem i.1))
  change MemLp
    (fun ω => (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), X i.1 ω) 2 P
  simpa [one_div] using hsum.const_mul (1 / ((n : ℝ) + 1))

theorem prob_11_7_sampleMean_integral_of_covarianceDecay {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) :
    ∀ n : ℕ, P[thm_11_5_sampleMean X n] = μ := by
  rcases hCovDecay with ⟨_hK, hMem, _ha_bound, _ha_lim, hMean, _hVar, _hCov⟩
  intro n
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  calc
    P[thm_11_5_sampleMean X n]
        = (1 / ((n : ℝ) + 1)) *
            P[fun ω => ∑ i : Fin (n + 1), X i.1 ω] := by
          simp [thm_11_5_sampleMean, integral_const_mul]
    _ = (1 / ((n : ℝ) + 1)) *
          (∑ i : Fin (n + 1), P[X i.1]) := by
          rw [integral_finset_sum]
          exact fun i _hi => (hMem i.1).integrable (by simp)
    _ = (1 / ((n : ℝ) + 1)) *
          (∑ _i : Fin (n + 1), μ) := by
          simp [hMean]
    _ = μ := by
          simp [Finset.sum_const, Fintype.card_fin]
          field_simp [hNpos.ne']

private theorem prob_11_7_local_variance_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    _root_.variance P Y = Var[Y; P] := by
  rw [_root_.variance, rthCentralMoment]
  exact ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := Y) hY.aemeasurable

private lemma prob_11_7_row_natDist_sum_le_two_range
    (N : ℕ) (i : Fin N) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    (∑ j : Fin N, a (Nat.dist i.1 j.1)) ≤
      2 * (∑ τ ∈ Finset.range N, a τ) := by
  classical
  let sL : Finset (Fin N) := Finset.univ.filter (fun j => j.1 ≤ i.1)
  let sR : Finset (Fin N) := Finset.univ.filter (fun j => ¬ j.1 ≤ i.1)
  let fL : Fin N → ℕ := fun j => i.1 - j.1
  let fR : Fin N → ℕ := fun j => j.1 - i.1
  have hsplit :
      (∑ j ∈ sL, a (Nat.dist i.1 j.1)) +
        (∑ j ∈ sR, a (Nat.dist i.1 j.1)) =
          ∑ j : Fin N, a (Nat.dist i.1 j.1) := by
    simpa [sL, sR] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin N)))
        (p := fun j : Fin N => j.1 ≤ i.1)
        (f := fun j : Fin N => a (Nat.dist i.1 j.1)))
  have hinjL : Set.InjOn fL ↑sL := by
    intro x hx y hy hxy
    apply Fin.ext
    have hxle : x.1 ≤ i.1 := by
      simpa [sL] using (Finset.mem_filter.mp hx).2
    have hyle : y.1 ≤ i.1 := by
      simpa [sL] using (Finset.mem_filter.mp hy).2
    dsimp [fL] at hxy
    omega
  have hinjR : Set.InjOn fR ↑sR := by
    intro x hx y hy hxy
    apply Fin.ext
    have hix : i.1 < x.1 := by
      have hnot : ¬ x.1 ≤ i.1 := by
        simpa [sR] using (Finset.mem_filter.mp hx).2
      exact Nat.lt_of_not_ge hnot
    have hiy : i.1 < y.1 := by
      have hnot : ¬ y.1 ≤ i.1 := by
        simpa [sR] using (Finset.mem_filter.mp hy).2
      exact Nat.lt_of_not_ge hnot
    dsimp [fR] at hxy
    omega
  have hleft_dist :
      (∑ j ∈ sL, a (Nat.dist i.1 j.1)) = ∑ j ∈ sL, a (fL j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjle : j.1 ≤ i.1 := by
      simpa [sL] using (Finset.mem_filter.mp hj).2
    rw [Nat.dist_eq_sub_of_le_right hjle]
  have hright_dist :
      (∑ j ∈ sR, a (Nat.dist i.1 j.1)) = ∑ j ∈ sR, a (fR j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hij : i.1 ≤ j.1 := by
      have hnot : ¬ j.1 ≤ i.1 := by
        simpa [sR] using (Finset.mem_filter.mp hj).2
      exact le_of_lt (Nat.lt_of_not_ge hnot)
    rw [Nat.dist_eq_sub_of_le hij]
  have hleft :
      (∑ j ∈ sL, a (Nat.dist i.1 j.1)) ≤ ∑ τ ∈ Finset.range N, a τ := by
    rw [hleft_dist]
    rw [← Finset.sum_image (s := sL) (g := fL) (f := a) hinjL]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro τ hτ
      rcases Finset.mem_image.mp hτ with ⟨j, _hj, rfl⟩
      exact Finset.mem_range.mpr
        (lt_of_le_of_lt (Nat.sub_le i.1 j.1) i.2)
    · intro τ _ _hnot
      exact ha τ
  have hright :
      (∑ j ∈ sR, a (Nat.dist i.1 j.1)) ≤ ∑ τ ∈ Finset.range N, a τ := by
    rw [hright_dist]
    rw [← Finset.sum_image (s := sR) (g := fR) (f := a) hinjR]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro τ hτ
      rcases Finset.mem_image.mp hτ with ⟨j, _hj, rfl⟩
      exact Finset.mem_range.mpr
        (lt_of_le_of_lt (Nat.sub_le j.1 i.1) j.2)
    · intro τ _ _hnot
      exact ha τ
  calc
    (∑ j : Fin N, a (Nat.dist i.1 j.1))
        = (∑ j ∈ sL, a (Nat.dist i.1 j.1)) +
            (∑ j ∈ sR, a (Nat.dist i.1 j.1)) := hsplit.symm
    _ ≤ (∑ τ ∈ Finset.range N, a τ) + (∑ τ ∈ Finset.range N, a τ) :=
      add_le_add hleft hright
    _ = 2 * (∑ τ ∈ Finset.range N, a τ) := by ring

private lemma prob_11_7_double_natDist_sum_le_two_mul
    (N : ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    (∑ i : Fin N, ∑ j : Fin N, a (Nat.dist i.1 j.1)) ≤
      (N : ℝ) * (2 * (∑ τ ∈ Finset.range N, a τ)) := by
  classical
  calc
    (∑ i : Fin N, ∑ j : Fin N, a (Nat.dist i.1 j.1))
        ≤ ∑ _i : Fin N, 2 * (∑ τ ∈ Finset.range N, a τ) := by
          exact Finset.sum_le_sum fun i _hi =>
            prob_11_7_row_natDist_sum_le_two_range N i a ha
    _ = (N : ℝ) * (2 * (∑ τ ∈ Finset.range N, a τ)) := by
          simp [Finset.sum_const, Fintype.card_fin]

private lemma prob_11_7_range_succ_cesaro_tendsto_zero
    (a : ℕ → ℝ) (ha_lim : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => (((n : ℝ) + 1)⁻¹) * (∑ τ ∈ Finset.range (n + 1), a τ))
      atTop (nhds 0) := by
  have h := ha_lim.cesaro.comp (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  ext n
  simp [Nat.cast_add, Nat.cast_one]

theorem prob_11_7_forward_covariance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a)
    (i τ : ℕ) (hτ : 0 < τ) :
    Covariance P (X i) (X (i + τ)) ≤ a τ * K := by
  rcases hCovDecay with ⟨hK, hMem, ha_bound, _ha_lim, _hMean, hVar, hCov⟩
  have hvar_i_nonneg : 0 ≤ _root_.variance P (X i) := by
    rw [prob_11_7_local_variance_eq P (hMem i)]
    exact ProbabilityTheory.variance_nonneg (X i) P
  have hvar_j_nonneg : 0 ≤ _root_.variance P (X (i + τ)) := by
    rw [prob_11_7_local_variance_eq P (hMem (i + τ))]
    exact ProbabilityTheory.variance_nonneg (X (i + τ)) P
  have hprod_le :
      _root_.variance P (X i) * _root_.variance P (X (i + τ)) ≤ K ^ 2 := by
    calc
      _root_.variance P (X i) * _root_.variance P (X (i + τ))
          ≤ K * K :=
            mul_le_mul (hVar i) (hVar (i + τ)) hvar_j_nonneg hK
      _ = K ^ 2 := by ring
  have hsqrt_le :
      Real.sqrt
          (_root_.variance P (X i) * _root_.variance P (X (i + τ))) ≤ K := by
    rw [Real.sqrt_le_iff]
    exact ⟨hK, hprod_le⟩
  exact (hCov i τ hτ).trans (mul_le_mul_of_nonneg_left hsqrt_le (ha_bound τ).1)

theorem prob_11_7_diagonal_covariance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) (i : ℕ) :
    Covariance P (X i) (X i) ≤ K := by
  rcases hCovDecay with ⟨_hK, hMem, _ha_bound, _ha_lim, _hMean, hVar, _hCov⟩
  rw [Covariance, ProbabilityTheory.covariance_self (hMem i).aemeasurable]
  rw [← prob_11_7_local_variance_eq P (hMem i)]
  exact hVar i

theorem prob_11_7_covariance_le_dist {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a)
    (i j : ℕ) (hij : i ≠ j) :
    Covariance P (X i) (X j) ≤ a (Nat.dist i j) * K := by
  by_cases hij_lt : i < j
  · have hτ : 0 < j - i := Nat.sub_pos_of_lt hij_lt
    have hsum : i + (j - i) = j := Nat.add_sub_of_le hij_lt.le
    have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hij_lt.le
    have h :=
      prob_11_7_forward_covariance_le P X μ K a hCovDecay i (j - i) hτ
    simpa [hsum, hdist] using h
  · have hji_lt : j < i := by
      exact Nat.lt_of_le_of_ne (le_of_not_gt hij_lt) hij.symm
    have hτ : 0 < i - j := Nat.sub_pos_of_lt hji_lt
    have hsum : j + (i - j) = i := Nat.add_sub_of_le hji_lt.le
    have hdist : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right hji_lt.le
    have h :=
      prob_11_7_forward_covariance_le P X μ K a hCovDecay j (i - j) hτ
    have hcomm : Covariance P (X i) (X j) = Covariance P (X j) (X i) := by
      simp [Covariance, ProbabilityTheory.covariance_comm]
    rw [hcomm]
    simpa [hsum, hdist] using h

theorem prob_11_7_sampleMean_variance_eq_covariance_sum {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) (n : ℕ) :
    _root_.variance P (thm_11_5_sampleMean X n) =
      (1 / ((n : ℝ) + 1)) ^ 2 *
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          Covariance P (X i.1) (X j.1)) := by
  rcases hCovDecay with ⟨_hK, hMem, _ha_bound, _ha_lim, _hMean, _hVar, _hCov⟩
  let S : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), X i.1 ω
  let c : ℝ := 1 / ((n : ℝ) + 1)
  have hS_mem : MemLp S 2 P := by
    simpa [S] using
      (memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => hMem i.1))
  have hA_mem : MemLp (thm_11_5_sampleMean X n) 2 P := by
    exact
      prob_11_7_sampleMean_memLp_of_covarianceDecay P X μ K a
        ⟨_hK, hMem, _ha_bound, _ha_lim, _hMean, _hVar, _hCov⟩ n
  have hsmul : thm_11_5_sampleMean X n = c • S := by
    ext ω
    simp [thm_11_5_sampleMean, S, c, smul_eq_mul]
  calc
    _root_.variance P (thm_11_5_sampleMean X n)
        = Var[thm_11_5_sampleMean X n; P] :=
          prob_11_7_local_variance_eq P hA_mem
    _ = Var[c • S; P] := by rw [hsmul]
    _ = c ^ 2 * Var[S; P] := by
          exact ProbabilityTheory.variance_smul c S P
    _ = c ^ 2 *
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            Covariance P (X i.1) (X j.1)) := by
          rw [ProbabilityTheory.variance_fun_sum (μ := P)
            (X := fun i : Fin (n + 1) => X i.1) (fun i => hMem i.1)]
          simp [Covariance]
    _ = (1 / ((n : ℝ) + 1)) ^ 2 *
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            Covariance P (X i.1) (X j.1)) := by
          rfl

theorem prob_11_7_covariance_double_sum_le_cesaro_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) (n : ℕ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        Covariance P (X i.1) (X j.1)) ≤
      ((n : ℝ) + 1) * K +
        K * (((n : ℝ) + 1) *
          (2 * (∑ τ ∈ Finset.range (n + 1), a τ))) := by
  classical
  have hCovDecay' := hCovDecay
  rcases hCovDecay with ⟨hK, _hMem, ha_bound, _ha_lim, _hMean, _hVar, _hCov⟩
  have ha_nonneg : ∀ τ : ℕ, 0 ≤ a τ := fun τ => (ha_bound τ).1
  have hrow (i : Fin (n + 1)) :
      (∑ j : Fin (n + 1), Covariance P (X i.1) (X j.1)) ≤
        K + K * (∑ j : Fin (n + 1), a (Nat.dist i.1 j.1)) := by
    let sDiag : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => j = i)
    let sOff : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => ¬ j = i)
    have hsplit :
        (∑ j ∈ sDiag, Covariance P (X i.1) (X j.1)) +
          (∑ j ∈ sOff, Covariance P (X i.1) (X j.1)) =
            ∑ j : Fin (n + 1), Covariance P (X i.1) (X j.1) := by
      simpa [sDiag, sOff] using
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin (n + 1))))
          (p := fun j : Fin (n + 1) => j = i)
          (f := fun j : Fin (n + 1) => Covariance P (X i.1) (X j.1)))
    have hdiag :
        (∑ j ∈ sDiag, Covariance P (X i.1) (X j.1)) ≤ K := by
      rw [Finset.sum_eq_single_of_mem i]
      · exact prob_11_7_diagonal_covariance_le P X μ K a hCovDecay' i.1
      · simp [sDiag]
      · intro j hj hji
        have hji' : j = i := by
          simpa [sDiag] using (Finset.mem_filter.mp hj).2
        exact (hji hji').elim
    have hoff :
        (∑ j ∈ sOff, Covariance P (X i.1) (X j.1)) ≤
          ∑ j ∈ sOff, a (Nat.dist i.1 j.1) * K := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hij : i.1 ≠ j.1 := by
        intro hval
        have hji : j = i := Fin.ext hval.symm
        have hne : ¬ j = i := by
          simpa [sOff] using (Finset.mem_filter.mp hj).2
        exact hne hji
      exact prob_11_7_covariance_le_dist P X μ K a hCovDecay' i.1 j.1 hij
    have hoff_all :
        (∑ j ∈ sOff, a (Nat.dist i.1 j.1) * K) ≤
          K * (∑ j : Fin (n + 1), a (Nat.dist i.1 j.1)) := by
      rw [← Finset.sum_mul]
      have hsubset :
          (∑ j ∈ sOff, a (Nat.dist i.1 j.1)) ≤
            ∑ j : Fin (n + 1), a (Nat.dist i.1 j.1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj
          simp
        · intro j _ _hnot
          exact ha_nonneg (Nat.dist i.1 j.1)
      have hmul := mul_le_mul_of_nonneg_right hsubset hK
      nlinarith
    calc
      (∑ j : Fin (n + 1), Covariance P (X i.1) (X j.1))
          = (∑ j ∈ sDiag, Covariance P (X i.1) (X j.1)) +
              (∑ j ∈ sOff, Covariance P (X i.1) (X j.1)) := hsplit.symm
      _ ≤ K + ∑ j ∈ sOff, a (Nat.dist i.1 j.1) * K :=
            add_le_add hdiag hoff
      _ ≤ K + K * (∑ j : Fin (n + 1), a (Nat.dist i.1 j.1)) :=
            add_le_add (le_refl K) hoff_all
  calc
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        Covariance P (X i.1) (X j.1))
        ≤ ∑ i : Fin (n + 1),
            (K + K * (∑ j : Fin (n + 1), a (Nat.dist i.1 j.1))) := by
          exact Finset.sum_le_sum fun i _hi => hrow i
    _ = ((n : ℝ) + 1) * K +
          K * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            a (Nat.dist i.1 j.1)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Fintype.card_fin,
            Nat.cast_add, Nat.cast_one]
    _ ≤ ((n : ℝ) + 1) * K +
        K * (((n : ℝ) + 1) *
          (2 * (∑ τ ∈ Finset.range (n + 1), a τ))) := by
          refine add_le_add (le_refl (((n : ℝ) + 1) * K)) ?_
          have hdouble :=
            prob_11_7_double_natDist_sum_le_two_mul (n + 1) a ha_nonneg
          have hmul := mul_le_mul_of_nonneg_left hdouble hK
          simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

theorem prob_11_7_sampleMean_variance_tendsto_zero_of_covarianceDecay {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) :
    Tendsto (fun n : ℕ => _root_.variance P (thm_11_5_sampleMean X n))
      atTop (nhds 0) := by
  rcases hCovDecay with ⟨hK, hMem, ha_bound, ha_lim, hMean, hVar, hCov⟩
  let hCovDecay' :
      prob_11_7_covarianceDecayAssumptions P X μ K a :=
    ⟨hK, hMem, ha_bound, ha_lim, hMean, hVar, hCov⟩
  let upper : ℕ → ℝ := fun n =>
    (1 / ((n : ℝ) + 1)) ^ 2 *
      (((n : ℝ) + 1) * K +
        K * (((n : ℝ) + 1) *
          (2 * (∑ τ ∈ Finset.range (n + 1), a τ))))
  have hUpperBound :
      ∀ n : ℕ,
        _root_.variance P (thm_11_5_sampleMean X n) ≤ upper n := by
    intro n
    rw [prob_11_7_sampleMean_variance_eq_covariance_sum P X μ K a hCovDecay' n]
    exact mul_le_mul_of_nonneg_left
      (prob_11_7_covariance_double_sum_le_cesaro_bound P X μ K a hCovDecay' n)
      (sq_nonneg (1 / ((n : ℝ) + 1)))
  have hLowerBound :
      ∀ n : ℕ, 0 ≤ _root_.variance P (thm_11_5_sampleMean X n) := by
    intro n
    have hAvgMem :
        MemLp (thm_11_5_sampleMean X n) 2 P :=
      prob_11_7_sampleMean_memLp_of_covarianceDecay P X μ K a hCovDecay' n
    rw [prob_11_7_local_variance_eq P hAvgMem]
    exact ProbabilityTheory.variance_nonneg (thm_11_5_sampleMean X n) P
  have hInv :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  have hTerm1 :
      Tendsto (fun n : ℕ => K * (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (nhds 0) := by
    simpa using hInv.const_mul K
  have hCesaro :
      Tendsto
        (fun n : ℕ =>
          (((n : ℝ) + 1)⁻¹) * (∑ τ ∈ Finset.range (n + 1), a τ))
        atTop (nhds 0) :=
    prob_11_7_range_succ_cesaro_tendsto_zero a ha_lim
  have hTerm2 :
      Tendsto
        (fun n : ℕ =>
          (2 * K) *
            ((((n : ℝ) + 1)⁻¹) * (∑ τ ∈ Finset.range (n + 1), a τ)))
        atTop (nhds 0) := by
    simpa using hCesaro.const_mul (2 * K)
  have hUpperSimple :
      Tendsto
        (fun n : ℕ =>
          K * (((n : ℝ) + 1)⁻¹ : ℝ) +
            (2 * K) *
              ((((n : ℝ) + 1)⁻¹) * (∑ τ ∈ Finset.range (n + 1), a τ)))
        atTop (nhds 0) := by
    simpa using hTerm1.add hTerm2
  have hUpperTendsto : Tendsto upper atTop (nhds 0) := by
    convert hUpperSimple using 1
    ext n
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    dsimp [upper]
    field_simp [hN]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpperTendsto hLowerBound hUpperBound

theorem prob_11_7_sampleMeanVarianceSupport_of_covarianceDecay {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) :
    prob_11_7_sampleMeanVarianceSupport P X μ :=
  ⟨prob_11_7_sampleMean_memLp_of_covarianceDecay P X μ K a hCovDecay,
    prob_11_7_sampleMean_integral_of_covarianceDecay P X μ K a hCovDecay,
    prob_11_7_sampleMean_variance_tendsto_zero_of_covarianceDecay P X μ K a hCovDecay⟩

/-- Chebyshev turns vanishing variance of the sample averages into convergence
in probability. -/
private theorem prob_11_7_of_variance_support {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hSupport : prob_11_7_sampleMeanVarianceSupport P X μ) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) := by
  rcases hSupport with ⟨hMem, hMean, hVarTendsto⟩
  intro ε hε
  have hvarDivTendsto :
      Tendsto
        (fun n : ℕ => _root_.variance P (thm_11_5_sampleMean X n) / ε ^ 2)
        atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (ε ^ 2)⁻¹) atTop (nhds ((ε ^ 2)⁻¹)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hVarTendsto.mul hconst
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (_root_.variance P (thm_11_5_sampleMean X n) / ε ^ 2))
        atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hvarDivTendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hbound_tendsto (fun n => zero_le _) ?_
  intro n
  let A : Ω → ℝ := thm_11_5_sampleMean X n
  have hChebReal :
      P.real {ω : Ω | ε ≤ |A ω - P[A]|} ≤
        _root_.variance P A / ε ^ 2 := by
    simpa [A] using thm_11_2 P A (hMem n) hε
  have hsubset :
      deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε ⊆
        {ω : Ω | ε ≤ |A ω - P[A]|} := by
    intro ω hω
    have hstrict : ε < |A ω - μ| := by
      simpa [deviationEvent, A] using hω
    have hclosed : ε ≤ |A ω - P[A]| := by
      simpa [A, hMean n] using le_of_lt hstrict
    exact hclosed
  have hmono :
      P (deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε) ≤
        P {ω : Ω | ε ≤ |A ω - P[A]|} :=
    measure_mono hsubset
  have hCheb :
      P {ω : Ω | ε ≤ |A ω - P[A]|} ≤
        ENNReal.ofReal (_root_.variance P A / ε ^ 2) := by
    have hE :
        P {ω : Ω | ε ≤ |A ω - P[A]|} =
          ENNReal.ofReal (P.real {ω : Ω | ε ≤ |A ω - P[A]|}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
    rw [hE]
    exact ENNReal.ofReal_le_ofReal hChebReal
  exact hmono.trans <| by
    simpa [A] using hCheb

/-- Problem 11.7, interpreted according to the standard weak-law statement for
weakly correlated variables: the sample averages converge in probability to
the common mean. -/
theorem prob_11_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ K : ℝ) (a : ℕ → ℝ)
    (hCovDecay : prob_11_7_covarianceDecayAssumptions P X μ K a) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) := by
  exact prob_11_7_of_variance_support P X μ
    (prob_11_7_sampleMeanVarianceSupport_of_covarianceDecay P X μ K a hCovDecay)
