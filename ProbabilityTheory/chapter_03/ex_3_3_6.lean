/-
TASK ID: ex_3_3_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_01.Ex_1_2_3




open MeasureTheory ProbabilityTheory Set Real Filter
open scoped ENNReal BigOperators Topology

noncomputable section

 

 
def ex336CantorBase (x : ℝ) : ℝ :=
  max 0 (min 1 x)

 
def ex336CantorRefine (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else if x ≤ 1 / 3 then (1 / 2 : ℝ) * f (3 * x)
  else if x ≤ 2 / 3 then 1 / 2
  else if x ≤ 1 then 1 / 2 + (1 / 2 : ℝ) * f (3 * x - 2)
  else 1

 
def ex336CantorApprox : ℕ → ℝ → ℝ
  | 0 => ex336CantorBase
  | n + 1 => ex336CantorRefine (ex336CantorApprox n)

@[simp] theorem ex336_cantorApprox_succ (n : ℕ) :
    ex336CantorApprox (n + 1) = ex336CantorRefine (ex336CantorApprox n) :=
  rfl

lemma ex336CantorBase_zero : ex336CantorBase 0 = 0 := by
  simp [ex336CantorBase]

lemma ex336CantorBase_one : ex336CantorBase 1 = 1 := by
  simp [ex336CantorBase]

lemma ex336CantorBase_range (x : ℝ) :
    0 ≤ ex336CantorBase x ∧ ex336CantorBase x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma continuous_ex336CantorBase : Continuous ex336CantorBase := by
  unfold ex336CantorBase
  fun_prop

lemma ex336CantorRefine_zero (f : ℝ → ℝ) : ex336CantorRefine f 0 = 0 := by
  norm_num [ex336CantorRefine]

lemma ex336CantorRefine_one {f : ℝ → ℝ} (hf1 : f 1 = 1) :
    ex336CantorRefine f 1 = 1 := by
  norm_num [ex336CantorRefine, hf1]

lemma ex336CantorRefine_range {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : ℝ) :
    0 ≤ ex336CantorRefine f x ∧ ex336CantorRefine f x ≤ 1 := by
  simp only [ex336CantorRefine]
  split_ifs
  · constructor <;> norm_num
  · have h := hf (3 * x)
    constructor <;> nlinarith
  · constructor <;> norm_num
  · have h := hf (3 * x - 2)
    constructor <;> nlinarith
  · constructor <;> norm_num



lemma continuous_ex336CantorRefine {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    Continuous (ex336CantorRefine f) := by
  have hright : Continuous (fun x : ℝ =>
      if x ≤ 1 then 1 / 2 + (1 / 2 : ℝ) * f (3 * x - 2) else 1) := by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · intro x hx
      change x = 1 at hx
      subst x
      norm_num [hf1]
  have hmiddle : Continuous (fun x : ℝ =>
      if x ≤ 2 / 3 then 1 / 2
      else if x ≤ 1 then 1 / 2 + (1 / 2 : ℝ) * f (3 * x - 2) else 1) := by
    apply Continuous.if_le
    · fun_prop
    · exact hright
    · fun_prop
    · fun_prop
    · intro x hx
      change x = 2 / 3 at hx
      subst x
      norm_num [hf0]
  have hleft : Continuous (fun x : ℝ =>
      if x ≤ 1 / 3 then (1 / 2 : ℝ) * f (3 * x)
      else if x ≤ 2 / 3 then 1 / 2
      else if x ≤ 1 then 1 / 2 + (1 / 2 : ℝ) * f (3 * x - 2) else 1) := by
    apply Continuous.if_le
    · fun_prop
    · exact hmiddle
    · fun_prop
    · fun_prop
    · intro x hx
      change x = 1 / 3 at hx
      subst x
      norm_num [hf1]
  change Continuous (fun x : ℝ =>
      if x ≤ 0 then 0
      else if x ≤ 1 / 3 then (1 / 2 : ℝ) * f (3 * x)
      else if x ≤ 2 / 3 then 1 / 2
      else if x ≤ 1 then 1 / 2 + (1 / 2 : ℝ) * f (3 * x - 2) else 1)
  apply Continuous.if_le
  · fun_prop
  · exact hleft
  · fun_prop
  · fun_prop
  · intro x hx
    change x = 0 at hx
    subst x
    norm_num [hf0]

theorem ex336_cantorApprox_endpoints (n : ℕ) :
    ex336CantorApprox n 0 = 0 ∧ ex336CantorApprox n 1 = 1 := by
  induction n with
  | zero => exact ⟨ex336CantorBase_zero, ex336CantorBase_one⟩
  | succ n ih =>
      exact ⟨ex336CantorRefine_zero _, ex336CantorRefine_one ih.2⟩

theorem ex336CantorApprox_range (n : ℕ) (x : ℝ) :
    0 ≤ ex336CantorApprox n x ∧ ex336CantorApprox n x ≤ 1 := by
  induction n generalizing x with
  | zero => exact ex336CantorBase_range x
  | succ n ih => exact ex336CantorRefine_range ih x

theorem continuous_ex336CantorApprox (n : ℕ) :
    Continuous (ex336CantorApprox n) := by
  induction n with
  | zero => exact continuous_ex336CantorBase
  | succ n ih =>
      exact continuous_ex336CantorRefine ih
        (ex336_cantorApprox_endpoints n).1 (ex336_cantorApprox_endpoints n).2

 
theorem ex336_cantorApprox_one_left {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 3) :
    ex336CantorApprox 1 x = 3 * x / 2 := by
  by_cases hx : x ≤ 0
  · have : x = 0 := le_antisymm hx hx0
    subst x
    norm_num [ex336CantorApprox, ex336CantorRefine, ex336CantorBase]
  · have hxpos : 0 < x := lt_of_not_ge hx
    have h3x0 : 0 ≤ 3 * x := by nlinarith
    have h3x1 : 3 * x ≤ 1 := by nlinarith
    change ex336CantorRefine ex336CantorBase x = 3 * x / 2
    rw [ex336CantorRefine, if_neg hx, if_pos hx1, ex336CantorBase,
      min_eq_right h3x1, max_eq_right h3x0]
    ring

 
theorem ex336_cantorApprox_one_middle {x : ℝ}
    (hx0 : 1 / 3 ≤ x) (hx1 : x ≤ 2 / 3) :
    ex336CantorApprox 1 x = 1 / 2 := by
  have hxnot0 : ¬x ≤ 0 := by norm_num at hx0 ⊢; linarith
  by_cases hxleft : x ≤ 1 / 3
  · have hx : x = 1 / 3 := le_antisymm hxleft hx0
    subst x
    norm_num [ex336CantorApprox, ex336CantorRefine, ex336CantorBase]
  · change ex336CantorRefine ex336CantorBase x = 1 / 2
    rw [ex336CantorRefine, if_neg hxnot0, if_neg hxleft, if_pos hx1]

 
theorem ex336_cantorApprox_one_right {x : ℝ}
    (hx0 : 2 / 3 ≤ x) (hx1 : x ≤ 1) :
    ex336CantorApprox 1 x = 1 / 2 + (1 / 2) * (3 * x - 2) := by
  have hxnot0 : ¬x ≤ 0 := by norm_num at hx0 ⊢; linarith
  have hxnot13 : ¬x ≤ 1 / 3 := by norm_num at hx0 ⊢; linarith
  by_cases hxmid : x ≤ 2 / 3
  · have hx : x = 2 / 3 := le_antisymm hxmid hx0
    subst x
    norm_num [ex336CantorApprox, ex336CantorRefine, ex336CantorBase]
  · have hy0 : 0 ≤ 3 * x - 2 := by nlinarith
    have hy1 : 3 * x - 2 ≤ 1 := by nlinarith
    change ex336CantorRefine ex336CantorBase x =
      1 / 2 + (1 / 2) * (3 * x - 2)
    rw [ex336CantorRefine, if_neg hxnot0, if_neg hxnot13, if_neg hxmid,
      if_pos hx1, ex336CantorBase, min_eq_right hy1, max_eq_right hy0]

 
theorem ex336_cantorApprox_two_flat_left
    {x : ℝ} (hx : x ∈ Set.Ioo (1 / 9) (2 / 9)) :
    ex336CantorApprox 2 x = 1 / 4 := by
  have hx0 : ¬x ≤ 0 := by norm_num at hx ⊢; linarith
  have hx13 : x ≤ 1 / 3 := by norm_num at hx ⊢; linarith
  have hy0 : 1 / 3 ≤ 3 * x := by norm_num at hx ⊢; linarith
  have hy1 : 3 * x ≤ 2 / 3 := by norm_num at hx ⊢; linarith
  change ex336CantorRefine (ex336CantorApprox 1) x = 1 / 4
  rw [ex336CantorRefine, if_neg hx0, if_pos hx13,
    ex336_cantorApprox_one_middle hy0 hy1]
  norm_num

theorem ex336_cantorApprox_two_flat_right
    {x : ℝ} (hx : x ∈ Set.Ioo (7 / 9) (8 / 9)) :
    ex336CantorApprox 2 x = 3 / 4 := by
  have hx0 : ¬x ≤ 0 := by norm_num at hx ⊢; linarith
  have hx13 : ¬x ≤ 1 / 3 := by norm_num at hx ⊢; linarith
  have hx23 : ¬x ≤ 2 / 3 := by norm_num at hx ⊢; linarith
  have hx1 : x ≤ 1 := by norm_num at hx ⊢; linarith
  have hy0 : 1 / 3 ≤ 3 * x - 2 := by norm_num at hx ⊢; linarith
  have hy1 : 3 * x - 2 ≤ 2 / 3 := by norm_num at hx ⊢; linarith
  change ex336CantorRefine (ex336CantorApprox 1) x = 3 / 4
  rw [ex336CantorRefine, if_neg hx0, if_neg hx13, if_neg hx23, if_pos hx1,
    ex336_cantorApprox_one_middle hy0 hy1]
  norm_num

 

theorem continuous_ex123U : Continuous ex123U := by
  change Continuous (Real.ofDigits ∘ ex123Digits)
  apply Real.continuous_ofDigits.comp
  exact continuous_pi fun i => by
    change Continuous (fun ω : ex123Ω => cond (ω i) (2 : Fin 3) 0)
    fun_prop

theorem measurable_ex123U : Measurable ex123U :=
  continuous_ex123U.measurable

theorem ex336_ex123U_injective : Function.Injective ex123U := by
  intro f g hfg
  have hdigits : ex123Digits f = ex123Digits g := by
    apply ofDigits_zero_two_sequence_unique
    · intro i
      cases h : f i <;> simp [ex123Digits, h]
    · intro i
      cases h : g i <;> simp [ex123Digits, h]
    · simpa [ex123U] using hfg
  funext i
  have hi := congrFun hdigits i
  cases hf : f i <;> cases hg : g i <;> simp [ex123Digits, hf, hg] at hi ⊢

 
def cantorDistribution : Measure ℝ :=
  ex123P.map ex123U

instance cantorDistribution_isProbability : IsProbabilityMeasure cantorDistribution :=
  Measure.isProbabilityMeasure_map measurable_ex123U.aemeasurable

 
def cantorStieltjesFunction : StieltjesFunction ℝ :=
  ProbabilityTheory.cdf cantorDistribution

theorem cantorDistribution_eq_ex123_law :
    cantorDistribution = ex123P.map ex123U :=
  rfl

theorem cantorDistribution_Iic_eq_ex123CDF (x : ℝ) :
    cantorDistribution (Set.Iic x) = ex123CDF x := by
  rw [cantorDistribution, Measure.map_apply measurable_ex123U measurableSet_Iic]
  rfl

 
lemma ex336_tprod_half_eq_zero : (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) = 0 := by
  have hle : ∀ n : ℕ, (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) ≤
      ∏ i ∈ Finset.range n, (1 / 2 : ℝ≥0∞) := by
    intro n
    rw [ENNReal.tprod_eq_iInf_prod (by intro i; norm_num)]
    exact iInf_le (fun s : Finset ℕ => ∏ i ∈ s, (1 / 2 : ℝ≥0∞)) (Finset.range n)
  have hzero : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 / 2 : ℝ≥0∞))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
  exact le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hzero hle)
    bot_le

 
theorem ex336_ex123P_singleton_eq_zero (ω : ex123Ω) :
    ex123P {ω} = 0 := by
  rw [ex123P, Measure.infinitePi_singleton]
  rw [show (∏' i : ℕ, ex123FairCoin {ω i}) =
      (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) by
    congr with i
    exact ex123FairCoin_apply_singleton (ω i)]
  exact ex336_tprod_half_eq_zero

def ex336Tail (ω : ex123Ω) : ex123Ω :=
  fun n => ω (n + 1)

def ex336HeadTail (ω : ex123Ω) : Bool × ex123Ω :=
  (ω 0, ex336Tail ω)

theorem measurable_ex336Tail : Measurable ex336Tail := by
  unfold ex336Tail
  exact measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

theorem measurable_ex336HeadTail : Measurable ex336HeadTail := by
  unfold ex336HeadTail ex336Tail
  fun_prop

theorem ex336_tail_law :
    ex123P.map ex336Tail = ex123P := by
  change ex123P.map (fun ω i => ω (i + 1)) = ex123P
  simpa [ex123P] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => ex123FairCoin) Nat.succ_injective)

theorem ex336_head_law :
    ex123P.map (fun ω : ex123Ω => ω 0) = ex123FairCoin := by
  simpa [ex123P] using
    (Measure.infinitePi_map_eval (fun _ : ℕ => ex123FairCoin) 0)

 
lemma ex336_head_indep_tail :
    IndepFun (fun ω : ex123Ω => ω 0) ex336Tail ex123P := by
  apply IndepFun.indepFun_process
  · exact measurable_pi_apply 0
  · intro n
    change Measurable (fun ω : ex123Ω => ω (n + 1))
    exact measurable_pi_apply (n + 1)
  · intro I
    let S : Finset ℕ := {0}
    let T : Finset ℕ := I.image Nat.succ
    have hST : Disjoint S T := by
      simp [S, T]
    have hfinite := iIndepFun.indepFun_finset S T hST
      ex123B_independent ex123B_measurable
    let φ : (∀ _ : S, Bool) → Bool := fun z => z ⟨0, by simp [S]⟩
    let ψ : (∀ _ : T, Bool) → (∀ _ : I, Bool) :=
      fun z i => z ⟨i.1 + 1, by simp [T]⟩
    have hφ : Measurable φ := by
      exact measurable_pi_apply (⟨0, by simp [S]⟩ : S)
    have hψ : Measurable ψ := by
      exact measurable_pi_lambda _ fun i =>
        measurable_pi_apply (⟨i.1 + 1, by simp [T]⟩ : T)
    have hcomp := hfinite.comp hφ hψ
    simpa [φ, ψ, S, T, ex123B, ex336Tail, Function.comp_def] using hcomp

 
theorem ex336_head_tail_law :
    ex123P.map ex336HeadTail = ex123FairCoin.prod ex123P := by
  have hjoint := ex336_head_indep_tail.map_prod_eq_prod_map_map
    (by fun_prop : Measurable (fun ω : ex123Ω => ω 0)).aemeasurable
    measurable_ex336Tail.aemeasurable
  calc
    ex123P.map ex336HeadTail =
        (ex123P.map (fun ω : ex123Ω => ω 0)).prod (ex123P.map ex336Tail) := by
      change ex123P.map (fun ω : ex123Ω => (ω 0, ex336Tail ω)) =
        (ex123P.map (fun ω : ex123Ω => ω 0)).prod (ex123P.map ex336Tail)
      exact hjoint
    _ = ex123FairCoin.prod ex123P := by
      rw [ex336_head_law, ex336_tail_law]

def ex336LeftBranch (x : ℝ) : ℝ := x / 3

def ex336RightBranch (x : ℝ) : ℝ := (2 + x) / 3

lemma measurable_ex336LeftBranch : Measurable ex336LeftBranch := by
  unfold ex336LeftBranch
  fun_prop

lemma measurable_ex336RightBranch : Measurable ex336RightBranch := by
  unfold ex336RightBranch
  fun_prop

def ex336HeadTailCode (p : Bool × ex123Ω) : ℝ :=
  if p.1 then ex336RightBranch (ex123U p.2) else ex336LeftBranch (ex123U p.2)

lemma measurable_ex336HeadTailCode : Measurable ex336HeadTailCode := by
  unfold ex336HeadTailCode
  refine Measurable.ite (by measurability) ?_ ?_
  · exact measurable_ex336RightBranch.comp (measurable_ex123U.comp measurable_snd)
  · exact measurable_ex336LeftBranch.comp (measurable_ex123U.comp measurable_snd)

lemma ex336_code_eq_head_tail (ω : ex123Ω) :
    ex123U ω = ex336HeadTailCode (ex336HeadTail ω) := by
  rw [ex123U_tail]
  have htail : (fun n => ω (n + 1)) = ex336Tail ω := rfl
  rw [htail]
  cases h : ω 0 <;>
    simp [ex336HeadTail, ex336HeadTailCode, ex336LeftBranch,
      ex336RightBranch, h] <;> ring

 
theorem cantorDistribution_self_similar :
    cantorDistribution =
      (1 / 2 : ℝ≥0∞) • cantorDistribution.map ex336LeftBranch +
      (1 / 2 : ℝ≥0∞) • cantorDistribution.map ex336RightBranch := by
  have hfactor : ex123U = ex336HeadTailCode ∘ ex336HeadTail := by
    funext ω
    exact ex336_code_eq_head_tail ω
  calc
    cantorDistribution = ex123P.map (ex336HeadTailCode ∘ ex336HeadTail) := by
      rw [cantorDistribution, hfactor]
    _ = (ex123P.map ex336HeadTail).map ex336HeadTailCode := by
      rw [Measure.map_map measurable_ex336HeadTailCode measurable_ex336HeadTail]
    _ = (ex123FairCoin.prod ex123P).map ex336HeadTailCode := by
      rw [ex336_head_tail_law]
    _ = ((1 / 2 : ℝ≥0∞) • (Measure.dirac false).prod ex123P +
        (1 / 2 : ℝ≥0∞) • (Measure.dirac true).prod ex123P).map
          ex336HeadTailCode := by
      rw [ex123FairCoin, Measure.add_prod,
        Measure.prod_smul_left, Measure.prod_smul_left]
    _ = (1 / 2 : ℝ≥0∞) • ex123P.map (fun ω => ex123U ω / 3) +
        (1 / 2 : ℝ≥0∞) • ex123P.map (fun ω => (2 + ex123U ω) / 3) := by
      rw [Measure.map_add _ _ measurable_ex336HeadTailCode]
      simp only [Measure.map_smul, Measure.dirac_prod]
      rw [Measure.map_map measurable_ex336HeadTailCode (by fun_prop),
        Measure.map_map measurable_ex336HeadTailCode (by fun_prop)]
      rfl
    _ = (1 / 2 : ℝ≥0∞) • cantorDistribution.map ex336LeftBranch +
        (1 / 2 : ℝ≥0∞) • cantorDistribution.map ex336RightBranch := by
      rw [cantorDistribution,
        Measure.map_map measurable_ex336LeftBranch measurable_ex123U,
        Measure.map_map measurable_ex336RightBranch measurable_ex123U]
      rfl

 



lemma cantorDistribution_Iic_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    cantorDistribution (Set.Iic x) = 0 := by
  rw [cantorDistribution, Measure.map_apply measurable_ex123U measurableSet_Iic]
  by_cases hpre : ex123U ⁻¹' Set.Iic x = ∅
  · rw [hpre, measure_empty]
  · obtain ⟨ω₀, hω₀⟩ := Set.nonempty_iff_ne_empty.mpr hpre
    have hsingleton : ex123U ⁻¹' Set.Iic x = {ω₀} := by
      ext ω
      constructor
      · intro hω
        change ex123U ω ≤ x at hω
        change ex123U ω₀ ≤ x at hω₀
        have hω_nonneg := (ex123U_mem_unit ω).1
        have hω₀_nonneg := (ex123U_mem_unit ω₀).1
        have hω_eq : ex123U ω = 0 := le_antisymm (le_trans hω hx) hω_nonneg
        have hω₀_eq : ex123U ω₀ = 0 := le_antisymm (le_trans hω₀ hx) hω₀_nonneg
        exact Set.mem_singleton_iff.mpr
          (ex336_ex123U_injective (hω_eq.trans hω₀_eq.symm))
      · intro hω
        simp only [Set.mem_singleton_iff] at hω
        subst ω
        exact hω₀
    rw [hsingleton, ex336_ex123P_singleton_eq_zero]

lemma cantorDistribution_Iic_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    cantorDistribution (Set.Iic x) = 1 := by
  rw [cantorDistribution, Measure.map_apply measurable_ex123U measurableSet_Iic]
  have hpre : ex123U ⁻¹' Set.Iic x = Set.univ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
    exact le_trans (ex123U_mem_unit ω).2 hx
  rw [hpre, measure_univ]

lemma cantorDistribution_Iic_recursion (x : ℝ) :
    cantorDistribution (Set.Iic x) =
      (1 / 2 : ℝ≥0∞) * cantorDistribution (Set.Iic (3 * x)) +
      (1 / 2 : ℝ≥0∞) * cantorDistribution (Set.Iic (3 * x - 2)) := by
  have hleft : ex336LeftBranch ⁻¹' Set.Iic x = Set.Iic (3 * x) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, ex336LeftBranch]
    constructor <;> intro h <;> nlinarith
  have hright : ex336RightBranch ⁻¹' Set.Iic x = Set.Iic (3 * x - 2) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, ex336RightBranch]
    constructor <;> intro h <;> nlinarith
  nth_rewrite 1 [cantorDistribution_self_similar]
  rw [Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_ex336LeftBranch measurableSet_Iic,
    Measure.map_apply measurable_ex336RightBranch measurableSet_Iic,
    hleft, hright]
  rfl

lemma ex336_cdf_eq_toReal (x : ℝ) :
    ProbabilityTheory.cdf cantorDistribution x =
      (cantorDistribution (Set.Iic x)).toReal := by
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def]

lemma ex336_cdf_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    ProbabilityTheory.cdf cantorDistribution x = 0 := by
  rw [ex336_cdf_eq_toReal, cantorDistribution_Iic_eq_zero_of_nonpos hx]
  norm_num

lemma ex336_cdf_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ProbabilityTheory.cdf cantorDistribution x = 1 := by
  rw [ex336_cdf_eq_toReal, cantorDistribution_Iic_eq_one_of_one_le hx]
  norm_num

lemma ex336_cdf_left {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 3) :
    ProbabilityTheory.cdf cantorDistribution x =
      (1 / 2 : ℝ) * ProbabilityTheory.cdf cantorDistribution (3 * x) := by
  have hright : 3 * x - 2 ≤ 0 := by nlinarith
  rw [ex336_cdf_eq_toReal, cantorDistribution_Iic_recursion,
    cantorDistribution_Iic_eq_zero_of_nonpos hright, mul_zero, add_zero,
    ENNReal.toReal_mul, ← ex336_cdf_eq_toReal]
  norm_num

lemma ex336_cdf_middle {x : ℝ} (hx0 : 1 / 3 < x) (hx1 : x ≤ 2 / 3) :
    ProbabilityTheory.cdf cantorDistribution x = 1 / 2 := by
  have hleft : 1 ≤ 3 * x := by nlinarith
  have hright : 3 * x - 2 ≤ 0 := by nlinarith
  rw [ex336_cdf_eq_toReal, cantorDistribution_Iic_recursion,
    cantorDistribution_Iic_eq_one_of_one_le hleft,
    cantorDistribution_Iic_eq_zero_of_nonpos hright]
  norm_num

lemma ex336_cdf_right {x : ℝ} (hx0 : 2 / 3 < x) (hx1 : x ≤ 1) :
    ProbabilityTheory.cdf cantorDistribution x =
      1 / 2 + (1 / 2 : ℝ) *
        ProbabilityTheory.cdf cantorDistribution (3 * x - 2) := by
  have hleft : 1 ≤ 3 * x := by nlinarith
  have hfinite :
      (1 / 2 : ℝ≥0∞) * cantorDistribution (Set.Iic (3 * x - 2)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)
  rw [ex336_cdf_eq_toReal, cantorDistribution_Iic_recursion,
    cantorDistribution_Iic_eq_one_of_one_le hleft,
    ENNReal.toReal_add (by norm_num) hfinite,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← ex336_cdf_eq_toReal]
  norm_num

 
theorem ex336_cdf_fixedBy_refine :
    ex336CantorRefine (fun x => ProbabilityTheory.cdf cantorDistribution x) =
      fun x => ProbabilityTheory.cdf cantorDistribution x := by
  funext x
  by_cases h0 : x ≤ 0
  · rw [ex336CantorRefine, if_pos h0]
    exact (ex336_cdf_eq_zero_of_nonpos h0).symm
  · have hx0 : 0 < x := lt_of_not_ge h0
    by_cases h13 : x ≤ 1 / 3
    · rw [ex336CantorRefine, if_neg h0, if_pos h13]
      exact (ex336_cdf_left hx0 h13).symm
    · have hx13 : 1 / 3 < x := lt_of_not_ge h13
      by_cases h23 : x ≤ 2 / 3
      · rw [ex336CantorRefine, if_neg h0, if_neg h13, if_pos h23]
        exact (ex336_cdf_middle hx13 h23).symm
      · have hx23 : 2 / 3 < x := lt_of_not_ge h23
        by_cases h1 : x ≤ 1
        · rw [ex336CantorRefine, if_neg h0, if_neg h13, if_neg h23, if_pos h1]
          exact (ex336_cdf_right hx23 h1).symm
        · rw [ex336CantorRefine, if_neg h0, if_neg h13, if_neg h23, if_neg h1]
          exact (ex336_cdf_eq_one_of_one_le (le_of_not_ge h1)).symm

lemma ex336_dist_half_mul (a b : ℝ) :
    dist ((1 / 2 : ℝ) * a) ((1 / 2 : ℝ) * b) = (1 / 2 : ℝ) * dist a b := by
  simp [Real.dist_eq, ← mul_sub, abs_mul]

lemma ex336_dist_half_add (a b : ℝ) :
    dist (1 / 2 + (1 / 2 : ℝ) * a) (1 / 2 + (1 / 2 : ℝ) * b) =
      (1 / 2 : ℝ) * dist a b := by
  rw [Real.dist_eq, Real.dist_eq]
  have hsub :
      1 / 2 + (1 / 2 : ℝ) * a - (1 / 2 + (1 / 2 : ℝ) * b) =
        (1 / 2 : ℝ) * (a - b) := by ring
  rw [hsub, abs_mul]
  norm_num

lemma ex336_refine_contract {f g : ℝ → ℝ} {ε : ℝ}
    (hε : ∀ y, dist (f y) (g y) ≤ ε) (x : ℝ) :
    dist (ex336CantorRefine f x) (ex336CantorRefine g x) ≤ (1 / 2 : ℝ) * ε := by
  have hε0 : 0 ≤ ε := le_trans dist_nonneg (hε 0)
  simp only [ex336CantorRefine]
  split_ifs
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hε0
  · rw [ex336_dist_half_mul]
    exact mul_le_mul_of_nonneg_left (hε (3 * x)) (by norm_num)
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hε0
  · rw [ex336_dist_half_add]
    exact mul_le_mul_of_nonneg_left (hε (3 * x - 2)) (by norm_num)
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hε0

 
theorem ex336_cantorApprox_error (n : ℕ) (x : ℝ) :
    dist (ex336CantorApprox n x)
      (ProbabilityTheory.cdf cantorDistribution x) ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, Real.dist_eq]
      have hF := ex336CantorApprox_range 0 x
      have hG0 := ProbabilityTheory.cdf_nonneg cantorDistribution x
      have hG1 := ProbabilityTheory.cdf_le_one cantorDistribution x
      exact (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
  | succ n ih =>
      have hfixed := congrFun ex336_cdf_fixedBy_refine x
      rw [ex336_cantorApprox_succ, pow_succ]
      calc
        dist (ex336CantorRefine (ex336CantorApprox n) x)
            (ProbabilityTheory.cdf cantorDistribution x) =
            dist (ex336CantorRefine (ex336CantorApprox n) x)
              (ex336CantorRefine
                (fun y => ProbabilityTheory.cdf cantorDistribution y) x) := by
              rw [hfixed]
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n) :=
          ex336_refine_contract ih x
        _ = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) := by ring

theorem ex336_cantorApprox_tendstoUniformly :
    TendstoUniformly ex336CantorApprox
      (fun x => ProbabilityTheory.cdf cantorDistribution x) atTop := by
  refine Metric.tendstoUniformly_iff.2 ?_
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact ((tendsto_order.1 hpow).2 ε hε).mono fun n hn x =>
    lt_of_le_of_lt (by simpa [dist_comm] using ex336_cantorApprox_error n x) hn

 

theorem cantorStieltjesFunction_eq_ex123CDF_toReal (x : ℝ) :
    cantorStieltjesFunction x = (ex123CDF x).toReal := by
  rw [cantorStieltjesFunction, ex336_cdf_eq_toReal,
    cantorDistribution_Iic_eq_ex123CDF]

theorem cantorDistribution_Iic_eq_sourceFunction (x : ℝ) :
    cantorDistribution (Set.Iic x) =
      ENNReal.ofReal (cantorStieltjesFunction x) := by
  simpa [cantorStieltjesFunction] using
    (ProbabilityTheory.ofReal_cdf cantorDistribution x).symm



theorem continuous_cantorStieltjesFunction :
    Continuous (fun x => cantorStieltjesFunction x) := by
  have hcontinuous :
      ∃ᶠ n in (atTop : Filter ℕ), Continuous (ex336CantorApprox n) :=
    Frequently.of_forall continuous_ex336CantorApprox
  simpa [cantorStieltjesFunction] using
    ex336_cantorApprox_tendstoUniformly.continuous hcontinuous

theorem cantorStieltjesFunction_measure :
    cantorStieltjesFunction.measure = cantorDistribution := by
  simpa [cantorStieltjesFunction] using
    (ProbabilityTheory.measure_cdf cantorDistribution)

theorem cantorDistribution_cantorSet_eq_one :
    cantorDistribution cantorSet = 1 := by
  rw [cantorDistribution,
    Measure.map_apply measurable_ex123U isClosed_cantorSet.measurableSet]
  exact ex123_cantor_set_probability_one

theorem cantorDistribution_singleton_eq_zero (x : ℝ) :
    cantorDistribution {x} = 0 := by
  rw [cantorDistribution,
    Measure.map_apply measurable_ex123U (measurableSet_singleton x)]
  by_cases hx : ∃ ω : ex123Ω, ex123U ω = x
  · rcases hx with ⟨ω, rfl⟩
    have hpre : ex123U ⁻¹' {ex123U ω} = {ω} := by
      ext η
      constructor
      · intro hη
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη
        exact Set.mem_singleton_iff.mpr
          (ex336_ex123U_injective hη)
      · intro hη
        simp only [Set.mem_singleton_iff] at hη ⊢
        simpa [hη]
    rw [hpre, ex336_ex123P_singleton_eq_zero]
  · have hpre : ex123U ⁻¹' {x} = ∅ := by
      ext ω
      constructor
      · intro hω
        exact False.elim (hx ⟨ω, Set.mem_singleton_iff.mp hω⟩)
      · intro hω
        exact False.elim hω
    rw [hpre, measure_empty]

 
theorem cantor_removed_gaps_volume_eq_one :
    volume ex123T = 1 := by
  rw [ex123_removed_gaps_union,
    measure_sdiff_null ex123_volume_cantorSet_eq_zero, Real.volume_Icc]
  norm_num

theorem cantorStieltjesFunction_flat_on_removed_gaps
    {a b u u' : ℝ} (hsub : Set.Ioo a b ⊆ ex123T)
    (hu : u ∈ Set.Ioo a b) (hu' : u' ∈ Set.Ioo a b) :
    cantorStieltjesFunction u = cantorStieltjesFunction u' := by
  rw [cantorStieltjesFunction_eq_ex123CDF_toReal,
    cantorStieltjesFunction_eq_ex123CDF_toReal]
  exact congrArg ENNReal.toReal (ex123CDF_flat_on_removed_gaps hsub hu hu')

theorem cantorStieltjesFunction_deriv_zero_ae :
    ∀ᵐ x ∂(volume : Measure ℝ),
      HasDerivAt (fun t => cantorStieltjesFunction t) 0 x := by
  simpa only [cantorStieltjesFunction_eq_ex123CDF_toReal] using
    ex123CDF_deriv_zero_ae

theorem cantorDistribution_is_source_iterative_stieltjes :
    TendstoUniformly ex336CantorApprox
        (fun x => cantorStieltjesFunction x) atTop ∧
      cantorStieltjesFunction.measure = cantorDistribution ∧
      (∀ x, cantorDistribution (Set.Iic x) =
        ENNReal.ofReal (cantorStieltjesFunction x)) := by
  exact ⟨by simpa [cantorStieltjesFunction] using
      ex336_cantorApprox_tendstoUniformly,
    cantorStieltjesFunction_measure,
    cantorDistribution_Iic_eq_sourceFunction⟩



theorem ex_3_3_6 :
    TendstoUniformly ex336CantorApprox
        (fun x => cantorStieltjesFunction x) atTop ∧
      Continuous (fun x => cantorStieltjesFunction x) ∧
      cantorStieltjesFunction.measure = cantorDistribution ∧
      volume ex123T = 1 ∧
      volume cantorSet = 0 ∧
      cantorDistribution cantorSet = 1 ∧
      (∀ x : ℝ, cantorDistribution {x} = 0) ∧
      (∀ {a b u u' : ℝ}, Set.Ioo a b ⊆ ex123T →
        u ∈ Set.Ioo a b → u' ∈ Set.Ioo a b →
        cantorStieltjesFunction u = cantorStieltjesFunction u') ∧
      (∀ᵐ x ∂(volume : Measure ℝ),
        HasDerivAt (fun t => cantorStieltjesFunction t) 0 x) := by
  exact ⟨by simpa [cantorStieltjesFunction] using
      ex336_cantorApprox_tendstoUniformly,
    continuous_cantorStieltjesFunction,
    cantorStieltjesFunction_measure,
    cantor_removed_gaps_volume_eq_one,
    ex123_volume_cantorSet_eq_zero,
    cantorDistribution_cantorSet_eq_one,
    cantorDistribution_singleton_eq_zero,
    fun {_ _ _ _} hsub hu hu' =>
      cantorStieltjesFunction_flat_on_removed_gaps hsub hu hu',
    cantorStieltjesFunction_deriv_zero_ae⟩
