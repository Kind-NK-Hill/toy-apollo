/-
TASK ID: prob_8_6_basic_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_8_4
import ToyApollo.Output.def_8_5
import ToyApollo.Output.thm_8_6
import ToyApollo.Output.thm_8_7
import Mathlib

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

def Poi (lam : ℝ) (k : ℕ) : ℝ :=
  exp (-lam) * lam ^ k / (k.factorial : ℝ)

def Ber (p : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - p
  else if k = 1 then p
  else 0

noncomputable def bernoulliNatPMF (lam : NNReal) (hlam : lam ≤ 1) : PMF ℕ :=
  (PMF.bernoulli lam hlam).map fun b : Bool => if b then 1 else 0

lemma bernoulliNatPMF_zero (lam : NNReal) (hlam : lam ≤ 1) :
    ((bernoulliNatPMF lam hlam) 0).toReal = 1 - (lam : ℝ) := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  norm_num [PMF.bernoulli_apply, hlam]

lemma bernoulliNatPMF_one (lam : NNReal) (hlam : lam ≤ 1) :
    ((bernoulliNatPMF lam hlam) 1).toReal = (lam : ℝ) := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  norm_num [PMF.bernoulli_apply, hlam]

lemma bernoulliNatPMF_ge_two (lam : NNReal) (hlam : lam ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    ((bernoulliNatPMF lam hlam) n).toReal = 0 := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  simp [PMF.bernoulli_apply, hlam, hne0, hne1]

lemma poissonPMF_toReal (lam : NNReal) (n : ℕ) :
    ((ProbabilityTheory.poissonPMF lam) n).toReal = ProbabilityTheory.poissonPMFReal lam n := by
  symm
  simpa [ProbabilityTheory.poissonPMFReal_nonneg] using
    congrArg ENNReal.toReal (ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF lam n)

lemma bernoulliNatPMF_toReal_eq_Ber (lam : NNReal) (hlam : lam ≤ 1) :
    (fun n => ((bernoulliNatPMF lam hlam) n).toReal) = Ber (lam : ℝ) := by
  funext n
  rcases n with (_ | n)
  · simp [Ber, bernoulliNatPMF_zero, hlam]
  · rcases n with (_ | n)
    · simp [Ber, bernoulliNatPMF_one, hlam]
    · have hge : 2 ≤ n.succ.succ := by omega
      simp [Ber, bernoulliNatPMF_ge_two lam hlam hge]

lemma poissonPMF_toReal_eq_Poi (lam : NNReal) :
    (fun n => ((ProbabilityTheory.poissonPMF lam) n).toReal) = Poi (lam : ℝ) := by
  funext n
  rw [poissonPMF_toReal]
  simp [Poi, ProbabilityTheory.poissonPMFReal, mul_comm, mul_left_comm, mul_assoc]

def Binom (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if k ≤ n then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0

def pmfConv (f g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), f j * g (k - j)

def pmfConvN (f : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => pmfConv f (pmfConvN f n)

lemma one_sub_exp_neg_le (p : ℝ) (hp : 0 ≤ p) :
    1 - exp (-p) ≤ p := by
      linarith [ Real.add_one_le_exp ( -p ) ]

lemma ber_poi_tv_le_sq (p : ℝ) (hp : 0 ≤ p) :
    d_TV (Ber p) (Poi p) ≤ p ^ 2 := by
      unfold d_TV;
      unfold Ber Poi;
      rw [ Summable.tsum_eq_zero_add ];
      · rw [ Summable.tsum_eq_zero_add ] <;> norm_num;
        · -- We'll use the fact that $\sum_{k=2}^{\infty} \frac{p^k}{k!} = e^p - 1 - p$.
          have h_sum : ∑' k : ℕ, (p ^ (k + 2) / (Nat.factorial (k + 2)) : ℝ) = Real.exp p - 1 - p := by
            norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
            rw [ eq_comm, Summable.tsum_eq_zero_add ];
            · rw [ Summable.tsum_eq_zero_add ] <;> norm_num;
              exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| Nat.succ_injective;
            · exact Real.summable_pow_div_factorial p;
          norm_num [ abs_div, abs_mul, abs_of_nonneg, hp, Real.exp_nonneg ];
          norm_num [ mul_div_assoc, tsum_mul_left, h_sum ];
          rw [ abs_of_nonpos, abs_of_nonneg ] <;> nlinarith [ Real.exp_pos p, Real.exp_pos ( -p ), Real.exp_neg p, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos p ) ), Real.add_one_le_exp p, Real.add_one_le_exp ( -p ) ];
        · refine' Summable.abs _;
          exact Summable.sub ( by exact ⟨ _, hasSum_single 0 <| by aesop ⟩ ) ( by exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by exact div_le_div_of_nonneg_right ( mul_le_of_le_one_left ( by positivity ) <| Real.exp_le_one_iff.mpr <| by linarith ) <| by positivity ) <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_pow_div_factorial p );
      · rw [ ← summable_nat_add_iff 2 ];
        simp +zetaDelta at *;
        exact Summable.abs <| by simpa [ mul_div_assoc ] using Summable.mul_left _ <| Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective 2;

lemma binom_eq_conv_ber (n : ℕ) (p : ℝ) :
    Binom n p = pmfConvN (Ber p) n := by
      funext k;
      induction' n with n ih generalizing k <;> simp_all +decide [ Nat.choose_succ_succ, pmfConvN ];
      · unfold Binom; aesop;
      · unfold Binom pmfConv;
        rcases k with ( _ | k ) <;> simp_all +decide [ Finset.sum_range_succ', Nat.choose_succ_succ, mul_assoc, mul_left_comm, pow_succ, Ber ];
        · rw [ ← ih ];
          unfold Binom; norm_num; ring;
        · rw [ ← ih, ← ih ];
          unfold Binom; split_ifs <;> simp_all +decide [ Nat.choose_succ_succ, mul_assoc, mul_comm, mul_left_comm, pow_succ' ] ;
          · rw [ show n - k = n - ( k + 1 ) + 1 by omega ] ; ring;
          · exact Or.inl <| Or.inl <| Nat.choose_eq_zero_of_lt <| by linarith;
          · grind +qlia

lemma poi_eq_conv_poi (n : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    Poi (↑n * p) = pmfConvN (Poi p) n := by
      induction' n with n ih;
      · ext ( _ | k ) <;> simp +decide [ Poi, pmfConvN ];
      · -- By definition of convolution, we have:
        have h_conv : ∀ k : ℕ, pmfConv (Poi p) (Poi (n * p)) k = Poi (p + n * p) k := by
          intro k
          simp [pmfConv, Poi];
          rw [ add_pow ];
          rw [ Finset.mul_sum _ _ _, Finset.sum_div ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_choose ] ; ring;
          · norm_num [ Nat.factorial_ne_zero, sub_eq_add_neg, Real.exp_add ] ; ring;
          · linarith [ Finset.mem_range.mp hx ];
        exact funext fun k => by rw [ show pmfConvN ( Poi p ) ( n + 1 ) = pmfConv ( Poi p ) ( Poi ( n * p ) ) from by aesop ] ; exact h_conv k ▸ by push_cast; ring;

lemma ber_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ Ber p k := by
  unfold Ber; split_ifs <;> linarith;

lemma ber_sum_one (p : ℝ) : HasSum (Ber p) 1 := by
  convert hasSum_ite_eq 0 ( 1 - p ) |> HasSum.add <| hasSum_ite_eq 1 p using 1;
  · ext ( _ | _ | k ) <;> simp +decide [ Ber ];
  · ring

lemma poi_nonneg (p : ℝ) (hp : 0 ≤ p) (k : ℕ) : 0 ≤ Poi p k := by
  exact div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( pow_nonneg hp _ ) ) ( Nat.cast_nonneg _ )

lemma poi_sum_one (p : ℝ) (hp : 0 ≤ p) : HasSum (Poi p) 1 := by
  convert Summable.hasSum _ using 1;
  · unfold Poi;
    rw [ tsum_congr fun n => by rw [ mul_div_assoc ], tsum_mul_left, show ( ∑' n : ℕ, p ^ n / ( n ! : ℝ ) ) = Real.exp p by rw [ Real.exp_eq_exp_ℝ ] ; rw [ NormedSpace.exp_eq_tsum_div ] ] ; norm_num [ Real.exp_neg, Real.exp_ne_zero ];
  · convert Summable.mul_left ( Real.exp ( -p ) ) ( Real.summable_pow_div_factorial p ) using 1;
    exact funext fun n => by unfold Poi; ring;

-- ============================================================================
-- Summability and convolution infrastructure
-- ============================================================================

lemma summable_pmf (f : ℕ → ℝ) (hf : HasSum f 1) : Summable f := hf.summable

lemma summable_abs_sub (f g : ℕ → ℝ) (hf : HasSum f 1) (hg : HasSum g 1) :
    Summable (fun k => |f k - g k|) :=
  (hf.summable.sub hg.summable).abs

lemma pmfConv_summable (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g) :
    Summable (pmfConv f g) := by
      refine' .of_norm _;
      exact summable_norm_sum_mul_range_of_summable_norm ( hf.norm ) ( hg.norm )

lemma pmfConv_hasSum (f g : ℕ → ℝ)
    (hf_nn : ∀ k, 0 ≤ f k) (hf_sum : HasSum f 1)
    (hg_nn : ∀ k, 0 ≤ g k) (hg_sum : HasSum g 1) :
    HasSum (pmfConv f g) 1 := by
      have h_sum : ∑' k, pmfConv f g k = (∑' k, f k) * (∑' k, g k) := by
        rw [ Summable.tsum_mul_tsum_eq_tsum_sum_range ];
        · rfl;
        · exact hf_sum.summable;
        · exact hg_sum.summable;
        · exact .of_norm <| by simpa using Summable.mul_norm ( hf_sum.summable.norm ) ( hg_sum.summable.norm ) ;
      convert h_sum ▸ Summable.hasSum _;
      · rw [ hf_sum.tsum_eq, hg_sum.tsum_eq, one_mul ];
      · exact pmfConv_summable f g ( hf_sum.summable ) ( hg_sum.summable )

lemma pmfConv_nonneg (f g : ℕ → ℝ)
    (hf_nn : ∀ k, 0 ≤ f k) (hg_nn : ∀ k, 0 ≤ g k) (k : ℕ) :
    0 ≤ pmfConv f g k := by
      exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hf_nn _ ) ( hg_nn _ )

lemma convN_nonneg (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (n : ℕ) (k : ℕ) :
    0 ≤ pmfConvN f n k := by
      induction' n with n ih generalizing k;
      · cases k <;> norm_num [ pmfConvN ];
      · exact pmfConv_nonneg _ _ hf ih _

lemma convN_sum_one (f : ℕ → ℝ) (hf_nn : ∀ k, 0 ≤ f k) (hf : HasSum f 1) (n : ℕ) :
    HasSum (pmfConvN f n) 1 := by
      induction' n with n ih;
      · exact hasSum_ite_eq 0 1;
      · convert pmfConv_hasSum f ( pmfConvN f n ) hf_nn hf ( fun k => convN_nonneg f hf_nn n k ) ih using 1

-- ============================================================================
-- d_TV properties
-- ============================================================================

lemma d_TV_nonneg (f g : ℕ → ℝ) : 0 ≤ d_TV f g := by
  unfold d_TV
  apply mul_nonneg
  · linarith
  · exact tsum_nonneg (fun k => abs_nonneg _)

lemma d_TV_self (f : ℕ → ℝ) : d_TV f f = 0 := by
  simp [d_TV]
