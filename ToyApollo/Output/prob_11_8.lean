import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.prob_11_7

/-
TASK ID: prob_11_8
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.8.} Define a first-order autocorrelation process by X0 = 0 and Xi = \rhoXi- 1 + Ni

for i \geq 1, where \rho is a constant with \vert\rho\vert < 1 and Ni is a Gaussian random variable

N( 0,\sigma 2)Assume that the random variables Ni 's are independent. Show that

(X1 + X2 +\cdot\cdot\cdot+ Xi)/i converges to 0 in probability as i \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The AR(1) assumptions from Problem 11.8, with the Gaussian innovation facts
encoded by their mean/variance and independence consequences. -/
def prob_11_8_ar1Assumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X N : ℕ → Ω → ℝ) (ρ : ℝ) (σ2 : ℝ≥0) : Prop :=
  (∀ ω : Ω, X 0 ω = 0) ∧
    |ρ| < 1 ∧
    (∀ i : ℕ, X (i + 1) = fun ω => ρ * X i ω + N (i + 1) ω) ∧
    (∀ i : ℕ, HasLaw (N i) (gaussianReal 0 σ2) P) ∧
    def_5_10_randomVariables P N

/-- The closed finite-sum form of the AR(1) recursion through time `i`. -/
noncomputable def prob_11_8_ar1Past {Ω : Type*} (N : ℕ → Ω → ℝ)
    (ρ : ℝ) (i : ℕ) : Ω → ℝ :=
  fun ω => ∑ k : Fin i, ρ ^ (i - 1 - k.1) * N (k.1 + 1) ω

/-- The closed finite-sum form satisfies the same AR(1) recursion. -/
theorem prob_11_8_ar1Past_succ {Ω : Type*} (N : ℕ → Ω → ℝ)
    (ρ : ℝ) (i : ℕ) :
    prob_11_8_ar1Past N ρ (i + 1) =
      fun ω => ρ * prob_11_8_ar1Past N ρ i ω + N (i + 1) ω := by
  ext ω
  simp [prob_11_8_ar1Past]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have hpow : ρ ^ (i - k.1) = ρ * ρ ^ (i - 1 - k.1) := by
    have hsucc : i - k.1 = (i - 1 - k.1) + 1 := by omega
    rw [hsucc, pow_succ]
    ring
  rw [hpow]
  ring

/-- The recursively defined process equals its closed finite-sum form. -/
theorem prob_11_8_ar1_unroll {Ω : Type*} (X N : ℕ → Ω → ℝ) (ρ : ℝ)
    (hX0 : ∀ ω : Ω, X 0 ω = 0)
    (hRec : ∀ i : ℕ, X (i + 1) = fun ω => ρ * X i ω + N (i + 1) ω) :
    ∀ i : ℕ, X i = prob_11_8_ar1Past N ρ i := by
  intro i
  induction i with
  | zero =>
      ext ω
      simp [prob_11_8_ar1Past, hX0 ω]
  | succ i ih =>
      rw [hRec i, prob_11_8_ar1Past_succ N ρ i, ih]

/-- Because `X_i` is a finite measurable function of past innovations, it is
independent of every future innovation. -/
theorem prob_11_8_ar1Past_indep_future {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℝ) (ρ : ℝ)
    (hNind : def_5_10_randomVariables P N) (hNae : ∀ i, AEMeasurable (N i) P)
    {i j : ℕ} (hij : i < j) :
    ProbabilityTheory.IndepFun (prob_11_8_ar1Past N ρ i) (N j) P := by
  classical
  dsimp [def_5_10_randomVariables] at hNind
  let S : Finset ℕ := Finset.range (i + 1)
  let T : Finset ℕ := {j}
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hmem
    simp [T] at hmem
    subst x
    simp [S] at hx
    omega
  have hTuple : ProbabilityTheory.IndepFun
      (fun ω (k : S) => N k.1 ω) (fun ω (k : T) => N k.1 ω) P :=
    hNind.indepFun_finset₀ S T hST hNae
  let jj : T := ⟨j, by simp [T]⟩
  let left : (S → ℝ) → ℝ := fun y =>
    ∑ k : Fin i, ρ ^ (i - 1 - k.1) * y ⟨k.1 + 1, by simp [S]⟩
  let right : (T → ℝ) → ℝ := fun y => y jj
  have hLeftMeas : Measurable left := by
    dsimp [left]
    fun_prop
  have hRightMeas : Measurable right := by
    dsimp [right]
    exact measurable_pi_apply jj
  have hcomp := hTuple.comp hLeftMeas hRightMeas
  simpa [left, right, jj, prob_11_8_ar1Past, S, T, Function.comp_def] using hcomp

/-- Local bridge between ToyApollo's central-moment abbreviation and Mathlib's
variance notation. -/
private theorem prob_11_8_local_variance_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    _root_.variance P Y = Var[Y; P] := by
  rw [_root_.variance, rthCentralMoment]
  exact ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := Y) hY.aemeasurable

/-- Gaussian innovations have the second moments used by the AR(1) calculation. -/
theorem prob_11_8_gaussian_innovation_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℝ) (σ2 : ℝ≥0)
    (hLaw : ∀ i : ℕ, HasLaw (N i) (gaussianReal 0 σ2) P) :
    (∀ i : ℕ, MemLp (N i) 2 P) ∧
      (∀ i : ℕ, P[N i] = 0) ∧
      (∀ i : ℕ, _root_.variance P (N i) = (σ2 : ℝ)) := by
  have hNmem : ∀ i : ℕ, MemLp (N i) 2 P := by
    intro i
    have hMapMem : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 σ2) :=
      memLp_id_gaussianReal' (μ := 0) (v := σ2) (p := 2) (by norm_num)
    have hMapMem' : MemLp id (2 : ℝ≥0∞) (Measure.map (N i) P) := by
      simpa [(hLaw i).map_eq] using hMapMem
    simpa [Function.comp_def] using
      (memLp_map_measure_iff hMapMem'.aestronglyMeasurable (hLaw i).aemeasurable).1
        hMapMem'
  refine ⟨hNmem, ?_, ?_⟩
  · intro i
    have hInt := (hLaw i).integral_eq
    simpa using hInt
  · intro i
    calc
      _root_.variance P (N i) = Var[N i; P] := by
        exact prob_11_8_local_variance_eq P (hNmem i)
      _ = Var[id; gaussianReal 0 σ2] := by
        exact (hLaw i).variance_eq
      _ = (σ2 : ℝ) := by
        simp

/-- The stable AR(1) source-facing assumptions instantiate the
covariance-decay interface from Problem 11.7 with the geometric envelope
`|ρ|^τ`. -/
theorem prob_11_8_covarianceDecaySupport_of_ar1Assumptions {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X N : ℕ → Ω → ℝ) (ρ : ℝ) (σ2 : ℝ≥0)
    (hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ∃ K : ℝ, ∃ a : ℕ → ℝ, prob_11_7_covarianceDecayAssumptions P X 0 K a := by
  rcases hAR with
    ⟨hX0, hρ, hRec, hLaw, hNind⟩
  rcases prob_11_8_gaussian_innovation_moments P N σ2 hLaw with
    ⟨hNmem, hNmean, hNvar⟩
  have hUnroll := prob_11_8_ar1_unroll X N ρ hX0 hRec
  have hFutureInd : ∀ i j : ℕ, i < j → ProbabilityTheory.IndepFun (X i) (N j) P := by
    intro i j hij
    rw [hUnroll i]
    exact prob_11_8_ar1Past_indep_future P N ρ hNind
      (fun k => (hLaw k).aemeasurable) hij
  have hXmem : ∀ i : ℕ, MemLp (X i) 2 P := by
    intro i
    induction i with
    | zero =>
        have hX0eq : X 0 = fun _ : Ω => 0 := funext hX0
        simpa [hX0eq] using (memLp_const (0 : ℝ) : MemLp (fun _ : Ω => 0) 2 P)
    | succ i ih =>
        rw [hRec i]
        exact (ih.const_mul ρ).add (hNmem (i + 1))
  have hXmean : ∀ i : ℕ, P[X i] = 0 := by
    intro i
    induction i with
    | zero =>
        have hX0eq : X 0 = fun _ : Ω => 0 := funext hX0
        simp [hX0eq]
    | succ i ih =>
        rw [hRec i]
        have hXiInt : Integrable (X i) P := (hXmem i).integrable (by norm_num)
        have hNiInt : Integrable (N (i + 1)) P := (hNmem (i + 1)).integrable (by norm_num)
        rw [integral_add, integral_const_mul, ih, hNmean (i + 1)]
        · ring
        · exact hXiInt.const_mul ρ
        · exact hNiInt
  have hVarRec : ∀ i : ℕ,
      _root_.variance P (X (i + 1)) =
        ρ ^ 2 * _root_.variance P (X i) + (σ2 : ℝ) := by
    intro i
    have hScaledMem : MemLp (fun ω => ρ * X i ω) 2 P := (hXmem i).const_mul ρ
    have hIndScaled : ProbabilityTheory.IndepFun (fun ω => ρ * X i ω) (N (i + 1)) P := by
      change ProbabilityTheory.IndepFun ((fun x : ℝ => ρ * x) ∘ X i)
        ((fun x : ℝ => x) ∘ N (i + 1)) P
      exact (hFutureInd i (i + 1) (Nat.lt_succ_self i)).comp (by fun_prop) (by fun_prop)
    rw [hRec i]
    calc
      _root_.variance P (fun ω => ρ * X i ω + N (i + 1) ω)
          = Var[fun ω => ρ * X i ω + N (i + 1) ω; P] := by
            exact prob_11_8_local_variance_eq P ((hScaledMem).add (hNmem (i + 1)))
      _ = Var[fun ω => ρ * X i ω; P] + Var[N (i + 1); P] := by
            exact hIndScaled.variance_fun_add hScaledMem (hNmem (i + 1))
      _ = ρ ^ 2 * _root_.variance P (X i) + (σ2 : ℝ) := by
            rw [ProbabilityTheory.variance_const_mul]
            rw [← prob_11_8_local_variance_eq P (hXmem i)]
            rw [← prob_11_8_local_variance_eq P (hNmem (i + 1))]
            rw [hNvar (i + 1)]
  have hρsq_lt : ρ ^ 2 < 1 := by
    exact (sq_lt_one_iff_abs_lt_one ρ).2 hρ
  have hden_pos : 0 < 1 - ρ ^ 2 := sub_pos.mpr hρsq_lt
  let K : ℝ := (σ2 : ℝ) / (1 - ρ ^ 2)
  have hK_nonneg : 0 ≤ K := by
    exact div_nonneg (by exact_mod_cast σ2.2) hden_pos.le
  have hVarBound : ∀ i : ℕ, _root_.variance P (X i) ≤ K := by
    intro i
    induction i with
    | zero =>
        have hX0eq : X 0 = fun _ : Ω => 0 := funext hX0
        rw [hX0eq]
        rw [prob_11_8_local_variance_eq P (memLp_const (0 : ℝ))]
        change Var[(0 : Ω → ℝ); P] ≤ K
        rw [ProbabilityTheory.variance_zero]
        exact hK_nonneg
    | succ i ih =>
        rw [hVarRec i]
        have hmul : ρ ^ 2 * _root_.variance P (X i) ≤ ρ ^ 2 * K :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg ρ)
        have hcalc : ρ ^ 2 * K + (σ2 : ℝ) = K := by
          dsimp [K]
          field_simp [K, hden_pos.ne']
          ring
        nlinarith
  have hVarStep : ∀ i : ℕ, _root_.variance P (X i) ≤ _root_.variance P (X (i + 1)) := by
    intro i
    rw [hVarRec i]
    have hleK := hVarBound i
    have hnonneg : 0 ≤ _root_.variance P (X i) := by
      rw [prob_11_8_local_variance_eq P (hXmem i)]
      exact ProbabilityTheory.variance_nonneg (X i) P
    have hmain : (1 - ρ ^ 2) * _root_.variance P (X i) ≤ (σ2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hleK hden_pos.le
      have hKcalc : (1 - ρ ^ 2) * K = (σ2 : ℝ) := by
        dsimp [K]
        field_simp [K, hden_pos.ne']
      simpa [hKcalc] using hmul
    nlinarith [sq_nonneg ρ]
  have hVarMono : ∀ i τ : ℕ, _root_.variance P (X i) ≤ _root_.variance P (X (i + τ)) := by
    intro i τ
    induction τ with
    | zero => simp
    | succ τ ih =>
        exact ih.trans (by simpa [Nat.add_assoc] using hVarStep (i + τ))
  have hCovRec : ∀ i τ : ℕ,
      Covariance P (X i) (X (i + τ)) =
        ρ ^ τ * _root_.variance P (X i) := by
    intro i τ
    induction τ with
    | zero =>
        rw [Nat.add_zero]
        rw [Covariance, ProbabilityTheory.covariance_self (hXmem i).aemeasurable]
        rw [← prob_11_8_local_variance_eq P (hXmem i)]
        ring
    | succ τ ih =>
        have hIdx : i + Nat.succ τ = (i + τ) + 1 := by omega
        rw [hIdx, hRec (i + τ)]
        have hRightMem : MemLp (X (i + τ)) 2 P := hXmem (i + τ)
        have hNoiseMem : MemLp (N ((i + τ) + 1)) 2 P := hNmem ((i + τ) + 1)
        have hIndNoise : ProbabilityTheory.IndepFun (X i) (N ((i + τ) + 1)) P :=
          hFutureInd i ((i + τ) + 1) (by omega)
        have hCovNoise : Covariance P (X i) (N ((i + τ) + 1)) = 0 := by
          exact hIndNoise.covariance_eq_zero (hXmem i) hNoiseMem
        calc
          Covariance P (X i) (fun ω => ρ * X (i + τ) ω + N ((i + τ) + 1) ω)
              = Covariance P (X i) (fun ω => ρ * X (i + τ) ω) +
                  Covariance P (X i) (N ((i + τ) + 1)) := by
                    rw [Covariance, Covariance]
                    exact ProbabilityTheory.covariance_add_right
                      (hXmem i) (hRightMem.const_mul ρ) hNoiseMem
          _ = ρ * Covariance P (X i) (X (i + τ)) + 0 := by
                    rw [Covariance, ProbabilityTheory.covariance_const_mul_right]
                    change ρ * Covariance P (X i) (X (i + τ)) +
                        Covariance P (X i) (N ((i + τ) + 1)) =
                      ρ * Covariance P (X i) (X (i + τ)) + 0
                    rw [hCovNoise]
          _ = ρ ^ Nat.succ τ * _root_.variance P (X i) := by
                    rw [ih]
                    rw [pow_succ]
                    ring
  refine ⟨K, fun τ : ℕ => |ρ| ^ τ, ?_⟩
  refine ⟨hK_nonneg, hXmem, ?_, ?_, hXmean, hVarBound, ?_⟩
  · intro τ
    exact ⟨pow_nonneg (abs_nonneg ρ) τ,
      pow_le_one₀ (abs_nonneg ρ) (le_of_lt hρ)⟩
  · have hAbsAbs : |(|ρ|)| < 1 := by
      simpa [abs_of_nonneg (abs_nonneg ρ)] using hρ
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hAbsAbs
  · intro i τ hτ
    rw [hCovRec i τ]
    have hvi_nonneg : 0 ≤ _root_.variance P (X i) := by
      rw [prob_11_8_local_variance_eq P (hXmem i)]
      exact ProbabilityTheory.variance_nonneg (X i) P
    have hvj_nonneg : 0 ≤ _root_.variance P (X (i + τ)) := by
      rw [prob_11_8_local_variance_eq P (hXmem (i + τ))]
      exact ProbabilityTheory.variance_nonneg (X (i + τ)) P
    have hpow_le_abs : ρ ^ τ ≤ |ρ| ^ τ := by
      calc
        ρ ^ τ ≤ |ρ ^ τ| := le_abs_self _
        _ = |ρ| ^ τ := by rw [abs_pow]
    have hleft :
        ρ ^ τ * _root_.variance P (X i) ≤
          |ρ| ^ τ * _root_.variance P (X i) :=
      mul_le_mul_of_nonneg_right hpow_le_abs hvi_nonneg
    have hsqrt :
        _root_.variance P (X i) ≤
          Real.sqrt (_root_.variance P (X i) * _root_.variance P (X (i + τ))) := by
      have hmono := hVarMono i τ
      rw [Real.le_sqrt hvi_nonneg (mul_nonneg hvi_nonneg hvj_nonneg)]
      nlinarith
    exact hleft.trans
      (mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (abs_nonneg ρ) τ))

/-- Problem 11.8: the sample averages of the stable first-order
autocorrelation process converge to `0` in probability. -/
theorem prob_11_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X N : ℕ → Ω → ℝ) (ρ : ℝ) (σ2 : ℝ≥0)
    (hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => 0) := by
  rcases prob_11_8_covarianceDecaySupport_of_ar1Assumptions P X N ρ σ2 hAR with
    ⟨K, a, hDecay⟩
  exact prob_11_7 P X 0 K a hDecay
