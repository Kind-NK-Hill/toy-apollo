/-
TASK ID: prob_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_3_5
import ToyApollo.Output.thm_3_3
import ToyApollo.Output.def_3_4
import ToyApollo.Output.thm_3_2

open Set Filter MeasureTheory ENNReal

noncomputable def F_stieltjes : StieltjesFunction ℝ where
  toFun := fun x => if x < 0 then 0 else if x < 2 then x / 4 else 1
  mono' := by
    exact fun x y hxy => by norm_num; split_ifs <;> linarith;
  right_continuous' := by
    intro x;
    rw [ Metric.continuousWithinAt_iff ];
    intro ε ε_pos;
    by_cases hx' : x < 2;
    · exact ⟨ Min.min ( 2 - x ) ( ε * 4 ), lt_min ( by linarith ) ( by linarith ), fun y hy₁ hy₂ => abs_lt.mpr ⟨ by split_ifs <;> linarith [ abs_lt.mp hy₂, min_le_left ( 2 - x ) ( ε * 4 ), min_le_right ( 2 - x ) ( ε * 4 ) ], by split_ifs <;> linarith [ abs_lt.mp hy₂, min_le_left ( 2 - x ) ( ε * 4 ), min_le_right ( 2 - x ) ( ε * 4 ) ] ⟩ ⟩;
    · exact ⟨ ε, ε_pos, fun y hy₁ hy₂ => abs_lt.mpr ⟨ by split_ifs <;> linarith [ abs_lt.mp hy₂, hy₁.out ], by split_ifs <;> linarith [ abs_lt.mp hy₂, hy₁.out ] ⟩ ⟩

noncomputable def A_seq : ℕ → Set ℝ := fun n => Set.Icc (↑(n % 3)) (5 + Real.exp (-(n : ℝ)))

-- Helper: n % 3 takes only values 0, 1, 2
lemma nat_mod3_le_two (n : ℕ) : n % 3 ≤ 2 := by omega

-- Helper: n % 3 = 0 for n = 3*k
lemma mod3_of_mul3 (k : ℕ) : (3 * k) % 3 = 0 := by omega

-- Helper: exp(-n) > 0
lemma exp_neg_pos (n : ℕ) : Real.exp (-(n : ℝ)) > 0 := Real.exp_pos _

lemma limsup_A_eq : Filter.limsup A_seq Filter.atTop = Set.Icc (0 : ℝ) 5 := by
  refine' Set.Subset.antisymm _ _ <;> simp +decide [ Set.subset_def, limsup_eq_iInf_iSup_of_nat ];
  · intro x hx;
    constructor;
    · exact le_trans ( Nat.cast_nonneg _ ) ( hx 0 |> Classical.choose_spec |> And.right |> And.left );
    · contrapose! hx;
      -- Since $x > 5$, we can choose $i$ such that $e^{-i} < x - 5$.
      obtain ⟨i, hi⟩ : ∃ i : ℕ, Real.exp (-(i : ℝ)) < x - 5 := by
        simpa using ( Metric.tendsto_atTop.mp ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop ) ) ( x - 5 ) ( by linarith ) |> fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi i le_rfl ⟩;
      exact ⟨ i + 1, fun n hn => fun h => by linarith [ h.1, h.2, Real.exp_pos ( -n : ℝ ), Real.exp_le_exp.2 ( show - ( n : ℝ ) ≤ -i by linarith [ show ( n : ℝ ) ≥ i + 1 by norm_cast ] ) ] ⟩;
  · intros x hx₁ hx₂ n; use 3 * n; simp +arith +decide [ A_seq ] ;
    exact ⟨ hx₁, le_add_of_le_of_nonneg hx₂ <| Real.exp_nonneg _ ⟩

lemma liminf_A_eq : Filter.liminf A_seq Filter.atTop = Set.Icc (2 : ℝ) 5 := by
  ext x;
  simp (config := { decide := true }) only [liminf_eq_iSup_iInf_of_nat];
  constructor;
  · simp +decide [ Set.mem_iUnion, Set.mem_iInter ];
    intro n hn; have := hn ( 3 * n ) ( by linarith ) ; have := hn ( 3 * n + 1 ) ( by linarith ) ; have := hn ( 3 * n + 2 ) ( by linarith ) ; norm_num [ A_seq ] at * ;
    exact ⟨ this.1, le_of_tendsto_of_tendsto tendsto_const_nhds ( by simpa using tendsto_const_nhds.add ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.tendsto_atTop_mono ( fun m => by linarith ) tendsto_natCast_atTop_atTop ) ) <| Filter.eventually_atTop.mpr ⟨ n, fun m hm => hn m hm |>.2 ⟩ ⟩;
  · simp +zetaDelta at *;
    intro hx₁ hx₂
    use 3;
    intro i hi
    simp [A_seq];
    exact ⟨ le_trans ( mod_cast Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) ) ) hx₁, le_add_of_le_of_nonneg hx₂ ( Real.exp_nonneg _ ) ⟩

lemma measure_Icc_0_5 : F_stieltjes.measure (Set.Icc (0 : ℝ) 5) = 1 := by
  rw [ StieltjesFunction.measure_Icc ];
  -- By definition of $F_stieltjes$, we know that its left limit at 0 is 0.
  have h_left_lim : Function.leftLim (F_stieltjes.toFun) 0 = 0 := by
    rw [ eq_comm, leftLim_eq_of_tendsto ];
    · exact NeBot.ne';
    · exact tendsto_const_nhds.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ show F_stieltjes.toFun x = 0 by exact if_pos hx.out ] );
  rw [ h_left_lim, sub_zero, F_stieltjes ] ; norm_num

lemma measure_Icc_2_5 : F_stieltjes.measure (Set.Icc (2 : ℝ) 5) = 1 / 2 := by
  rw [ show F_stieltjes.measure ( Set.Icc 2 5 ) = F_stieltjes.measure ( { 2 } ∪ Set.Ioc 2 5 ) by
        norm_num [ Set.Icc_def ], MeasureTheory.measure_union ] <;> norm_num;
  -- Calculate the left limit of $F$ at $2$.
  have h_left_lim : Function.leftLim (F_stieltjes : ℝ → ℝ) 2 = 1 / 2 := by
    -- By definition of $F_stieltjes$, we know that its left limit at 2 is $1/2$.
    have h_left_lim : Filter.Tendsto (fun x => F_stieltjes x) (nhdsWithin 2 (Set.Iio 2)) (nhds (1 / 2)) := by
      -- For $x$ slightly less than $2$, we have $F(x) = x / 4$.
      have h_left_lim_def : ∀ᶠ x in nhdsWithin 2 (Set.Iio 2), F_stieltjes x = x / 4 := by
        refine' eventually_nhdsWithin_iff.mpr _;
        filter_upwards [ lt_mem_nhds one_lt_two ] with x hx₁ hx₂ using if_neg ( by linarith ) |> fun h => h.trans ( if_pos <| by linarith [ hx₂.out ] );
      rw [ Filter.tendsto_congr' h_left_lim_def ] ; exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ;
    refine' tendsto_nhds_unique _ h_left_lim;
    apply_rules [ Monotone.tendsto_leftLim ];
    exact F_stieltjes.mono';
  rw [ h_left_lim ] ; norm_num [ F_stieltjes ];
  rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num

theorem prob_3_1 :
    let A : ℕ → Set ℝ := fun n => Set.Icc (↑(n % 3)) (5 + Real.exp (-(n : ℝ)))
    let μ : Measure ℝ := F_stieltjes.measure
    Filter.limsup A Filter.atTop = Set.Icc (0 : ℝ) 5 ∧
    Filter.liminf A Filter.atTop = Set.Icc (2 : ℝ) 5 ∧
    μ (Filter.limsup A Filter.atTop) = 1 ∧
    μ (Filter.liminf A Filter.atTop) = 1 / 2 := by
  have h1 := limsup_A_eq
  have h2 := liminf_A_eq
  have h3 := measure_Icc_0_5
  have h4 := measure_Icc_2_5
  unfold A_seq at h1 h2
  exact ⟨h1, h2, by rw [h1]; exact h3, by rw [h2]; exact h4⟩
