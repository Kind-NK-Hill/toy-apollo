import Mathlib

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

/-- Expectation of a real-valued random variable. -/
noncomputable def E {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, X ω ∂P

/-- Variance of a real-valued random variable. -/
noncomputable def Var {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, (X ω - E X P) ^ 2 ∂P

namespace Prob610

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [hP : IsProbabilityMeasure P]
variable {ε : ℕ → Ω → ℝ}

lemma eps_sq_eq_one (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (k : ℕ) (ω : Ω) : (ε k ω) ^ 2 = 1 := by
  cases h_support k ω <;> simp +decide [ * ]

lemma prob_neg_one (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2)
    (k : ℕ) : P {ω | ε k ω = -1} = 1/2 := by
  have h_univ : P Set.univ = 1 := by
    simpa using (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := P))
  have h_compl : {ω | ε k ω = -1} = {ω | ε k ω = 1}ᶜ := by
    ext ω
    cases h_support k ω <;> simp [*] <;> norm_num
  rw [h_compl, MeasureTheory.measure_compl]
  · rw [h_univ, h_prob k]
    norm_num
  · exact measurableSet_eq_fun (h_meas k) measurable_const
  · exact MeasureTheory.measure_ne_top _ _

lemma eps_integrable (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (k : ℕ) : Integrable (ε k) P := by
  refine' MeasureTheory.Integrable.mono' _ _ _
  exacts [ fun _ => 1, by norm_num, ( h_meas k |> Measurable.aestronglyMeasurable ),
    Filter.Eventually.of_forall fun ω => by rcases h_support k ω with h | h <;> norm_num [ h ] ]

lemma eps_mean_zero (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2)
    (k : ℕ) : ∫ ω, ε k ω ∂P = 0 := by
  have h_integral : ∫ ω, ε k ω ∂P = (∫ ω in {ω | ε k ω = 1}, 1 ∂P) + (∫ ω in {ω | ε k ω = -1}, -1 ∂P) := by
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ]
    · rw [ ← MeasureTheory.integral_add ] ; congr ; ext ω ; rcases h_support k ω with h | h <;> norm_num [ h ]
      · exact MeasureTheory.integrable_indicator_iff ( measurableSet_eq_fun ( h_meas k ) measurable_const ) |>.2 ( by norm_num )
      · exact MeasureTheory.integrable_indicator_iff ( measurableSet_eq_fun ( h_meas k ) measurable_const ) |>.2 ( by norm_num )
    · exact measurableSet_eq_fun ( h_meas k ) measurable_const
    · exact measurableSet_eq_fun ( h_meas k ) measurable_const
  have h_integral_neg : ∫ ω in {ω | ε k ω = -1}, (1 : ℝ) ∂P = 1 - ∫ ω in {ω | ε k ω = 1}, (1 : ℝ) ∂P := by
    simp +zetaDelta at *
    rw [ eq_sub_iff_add_eq', ← MeasureTheory.measureReal_union ]
    · rw [ show { ω | ε k ω = 1 } ∪ { ω | ε k ω = -1 } = Set.univ by ext ω; simpa using h_support k ω ] ; simp +decide [ MeasureTheory.measureReal_def ]
    · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.symm, hx₂.symm ]
    · exact measurableSet_eq_fun ( h_meas k ) measurable_const
  simp_all +decide [ MeasureTheory.measureReal_def ]
  norm_num

lemma eps_sq_mean_one (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (k : ℕ) : ∫ ω, (ε k ω) ^ 2 ∂P = 1 := by
  convert MeasureTheory.integral_const ( 1 : ℝ )
  · cases h_support k ‹_› <;> simp +decide [ * ]
  · simp +decide [ MeasureTheory.measureReal_def ]

lemma eps_abs_le_one (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1) (k : ℕ) (ω : Ω) :
    |ε k ω| = 1 := by
  cases h_support k ω <;> simp +decide [ * ]

/-
The series Σ ε_{k+1}(ω) * (1/2)^{k+1} is summable for each ω.
-/
lemma series_summable (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1) (ω : Ω) :
    Summable (fun k => ε (k+1) ω * (1/2 : ℝ)^(k+1)) := by
  -- We can factor out the constant $(1/2)^{k+1}$ from the series.
  have h_factor : Summable (fun k => |ε (k + 1) ω| * (1 / 2) ^ (k + 1)) := by
    exact Summable.of_nonneg_of_le ( fun k => mul_nonneg ( abs_nonneg _ ) ( pow_nonneg ( by norm_num ) _ ) ) ( fun k => mul_le_mul_of_nonneg_right ( show |ε ( k + 1 ) ω| ≤ 1 from by rcases h_support ( k + 1 ) ω with h | h <;> rw [ h ] <;> norm_num ) ( pow_nonneg ( by norm_num ) _ ) ) ( by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_two );
  exact Summable.of_norm <| by simpa using h_factor.norm;

/-
The sum T(ω) = Σ ε_{k+1}(ω) * (1/2)^{k+1} is integrable.
-/
lemma T_integrable (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1) :
    Integrable (fun ω => ∑' k, ε (k+1) ω * (1/2 : ℝ)^(k+1)) P := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ∑' k : ℕ, ( 1 : ℝ ) * ( 1 / 2 ) ^ ( k + 1 );
  · norm_num;
  · refine' Measurable.aestronglyMeasurable _;
    refine' measurable_of_tendsto_metrizable _ _;
    exact fun n ω => ∑ k ∈ Finset.range n, ε ( k + 1 ) ω * ( 1 / 2 ) ^ ( k + 1 );
    · exact fun n => Finset.measurable_sum _ fun i _ => Measurable.mul ( h_meas _ ) measurable_const;
    · exact tendsto_pi_nhds.2 fun ω => Summable.hasSum ( series_summable ( by tauto ) ω ) |> HasSum.tendsto_sum_nat;
  · refine' Filter.Eventually.of_forall fun ω => _;
    refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
    · exact Summable.of_nonneg_of_le ( fun _ => norm_nonneg _ ) ( fun n => by rcases h_support ( n + 1 ) ω with h | h <;> norm_num [ h ] ) ( summable_nat_add_iff 1 |>.2 <| summable_geometric_two );
    · exact Summable.tsum_le_tsum ( fun k => by rcases h_support ( k + 1 ) ω with h | h <;> norm_num [ h ] ) ( by exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by rcases h_support ( k + 1 ) ω with h | h <;> norm_num [ h ] ) ( summable_geometric_two.comp_injective ( Nat.succ_injective ) ) ) ( by exact Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by norm_num ) ( summable_geometric_two.comp_injective ( Nat.succ_injective ) ) )

/-
The integral of T is 0.
-/
lemma T_integral_zero (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2) :
    ∫ ω, (∑' k, ε (k+1) ω * (1/2 : ℝ)^(k+1)) ∂P = 0 := by
  rw [ MeasureTheory.integral_tsum ];
  · rw [ tsum_congr fun i => by rw [ MeasureTheory.integral_mul_const, eps_mean_zero h_meas h_support h_prob _ ] ] ; norm_num;
  · exact fun k => Measurable.aestronglyMeasurable ( h_meas _ |> Measurable.mul <| measurable_const );
  · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun i => _ ) _ );
    use fun i => ENNReal.ofReal ( ( 1 / 2 ) ^ ( i + 1 ) );
    · refine' le_trans ( MeasureTheory.lintegral_mono fun ω => _ ) _;
      use fun ω => ENNReal.ofReal ( ( 1 / 2 ) ^ ( i + 1 ) );
      · cases h_support ( i + 1 ) ω <;> simp +decide [ * ];
        · erw [ Real.enorm_of_nonneg ] <;> norm_num;
        · erw [ Real.enorm_of_nonneg ] <;> norm_num;
      · simp +decide [ ENNReal.ofReal_pow ];
    · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
      exact Summable.comp_injective ( summable_geometric_two ) ( Nat.succ_injective )

/-
E[S] = 1.
-/
lemma E_S_eq_one (h_meas : ∀ k, Measurable (ε k))
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2) :
    let S : Ω → ℝ := fun ω => 1 + ∑' k, ε (k+1) ω * (1/2 : ℝ)^(k+1)
    E S P = 1 := by
  unfold E;
  field_simp;
  rw [ MeasureTheory.integral_add ];
  · rw [ T_integral_zero ] <;> aesop;
  · norm_num;
  · exact T_integrable h_meas h_support

/-
Var(S) = 1/3.
-/
lemma Var_S_eq (h_meas : ∀ k, Measurable (ε k))
    (h_indep : iIndepFun (β := fun _ => ℝ) ε P)
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1)
    (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2) :
    let S : Ω → ℝ := fun ω => 1 + ∑' k, ε (k+1) ω * (1/2 : ℝ)^(k+1)
    Var S P = 1/3 := by
  -- Let's simplify the expression inside the integral further by separating the sum into two parts.
  suffices h_suff' : ∫ ω, (∑' k, ε (k + 1) ω * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 ∂P = 1 / 3 by
    unfold Var;
    have := E_S_eq_one h_meas h_support h_prob; simp_all +decide [ E ] ;
  -- Let's simplify the expression inside the integral.
  have h_simp : ∀ n : ℕ, ∫ ω, (∑ k ∈ Finset.range n, (ε (k + 1) ω) * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 ∂P = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (2 * (k + 1)) := by
    intro n
    have h_expand : ∫ ω, (∑ k ∈ Finset.range n, (ε (k + 1) ω) * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 ∂P = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1 + l + 1) * ∫ ω, (ε (k + 1) ω) * (ε (l + 1) ω) ∂P := by
      simp +decide only [pow_add, pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, ← integral_const_mul,
          mul_assoc];
      rw [ MeasureTheory.integral_finset_sum ];
      · refine' Finset.sum_congr rfl fun i hi => MeasureTheory.integral_finset_sum _ fun j hj => _;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun ω => 1 * ( 1 * ( ( 1 / 2 ) ^ i * ( ( 1 / 2 ) ^ j * ( ( 1 / 2 ) ^ 1 * ( 1 / 2 ) ^ 1 ) ) ) );
        · exact MeasureTheory.integrable_const _;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( h_meas _ |> Measurable.aestronglyMeasurable ) ( MeasureTheory.AEStronglyMeasurable.mul ( h_meas _ |> Measurable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) );
        · filter_upwards [ ] with ω using by rcases h_support ( i + 1 ) ω with ha | ha <;> rcases h_support ( j + 1 ) ω with hb | hb <;> norm_num [ ha, hb ] ;
      · refine' fun i hi => MeasureTheory.integrable_finset_sum _ fun j hj => _;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun ω => 1 * ( 1 * ( ( 1 / 2 ) ^ i * ( ( 1 / 2 ) ^ j * ( ( 1 / 2 ) ^ 1 * ( 1 / 2 ) ^ 1 ) ) ) );
        · exact MeasureTheory.integrable_const _;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( h_meas _ |> Measurable.aestronglyMeasurable ) ( MeasureTheory.AEStronglyMeasurable.mul ( h_meas _ |> Measurable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const ) );
        · filter_upwards [ ] with ω using by rcases h_support ( i + 1 ) ω with ha | ha <;> rcases h_support ( j + 1 ) ω with hb | hb <;> norm_num [ ha, hb ] ;
    -- Since $\varepsilon_k$ are independent, we have $\int \varepsilon_k \varepsilon_l \, dP = \int \varepsilon_k \, dP \int \varepsilon_l \, dP$ for $k \neq l$.
    have h_indep : ∀ k l : ℕ, k ≠ l → ∫ ω, (ε (k + 1) ω) * (ε (l + 1) ω) ∂P = (∫ ω, (ε (k + 1) ω) ∂P) * (∫ ω, (ε (l + 1) ω) ∂P) := by
      intro k l hkl
      have h_indep : ProbabilityTheory.IndepFun (ε (k + 1)) (ε (l + 1)) P := by
        exact h_indep.indepFun ( by simpa );
      apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
      · exact h_meas _ |> Measurable.aestronglyMeasurable;
      · exact h_meas _ |> Measurable.aestronglyMeasurable;
    -- Since $\varepsilon_k$ are independent, we have $\int \varepsilon_k \, dP = 0$ for all `k`.
    have h_mean_zero : ∀ k : ℕ, ∫ ω, (ε (k + 1) ω) ∂P = 0 := by
      intro k; exact (by
      apply_rules [ Prob610.eps_mean_zero ]);
    rw [ h_expand, Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ( fun j hj => by by_cases hij : i = j <;> aesop ) ( by aesop ) ] ; norm_num [ h_mean_zero ] ; ring;
    norm_num [ add_comm, show ∀ k ω, ε ( k + 1 ) ω ^ 2 = 1 by intros k ω; specialize h_support ( k + 1 ) ω; aesop ];
  -- By the dominated convergence theorem, we can interchange the limit and the integral.
  have h_dominated : Filter.Tendsto (fun n => ∫ ω, (∑ k ∈ Finset.range n, (ε (k + 1) ω) * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 ∂P) Filter.atTop (nhds (∫ ω, (∑' k, (ε (k + 1) ω) * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 ∂P)) := by
    refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun ω => ( ∑' k, ( 1 / 2 : ℝ ) ^ ( k + 1 ) ) ^ 2;
    · fun_prop;
    · norm_num;
    · intro n; filter_upwards [ ] with ω; norm_num [ abs_mul, abs_of_nonneg, pow_nonneg ];
      -- Since `|ε_k ω| = 1`, the absolute partial sum is bounded by the geometric tail sum.
      have h_abs : |∑ k ∈ Finset.range n, ε (k + 1) ω * (1 / 2 : ℝ) ^ (k + 1)| ≤ ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) := by
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rcases h_support ( i + 1 ) ω with h | h <;> rw [ h ] <;> norm_num [ abs_mul, abs_of_nonneg ] );
      exact le_trans ( by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) h_abs 2 ) ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => by positivity ) ( Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => by positivity ) ( by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_two ) ) 2 );
    · refine' Filter.Eventually.of_forall fun ω => Filter.Tendsto.pow _ _;
      refine' ( Summable.hasSum _ ) |> HasSum.tendsto_sum_nat;
      -- Absolute convergence follows from comparison with the geometric series.
      have h_abs_conv : Summable (fun k => |ε (k + 1) ω| * (1 / 2 : ℝ) ^ (k + 1)) := by
        exact Summable.of_nonneg_of_le ( fun k => mul_nonneg ( abs_nonneg _ ) ( pow_nonneg ( by norm_num ) _ ) ) ( fun k => mul_le_of_le_one_left ( by positivity ) ( by cases h_support ( k + 1 ) ω <;> simp +decide [ * ] ) ) ( by simpa using summable_nat_add_iff 1 |>.2 <| summable_geometric_two );
      exact Summable.of_norm <| by simpa using h_abs_conv.norm;
  simp_all +decide [ pow_mul ];
  exact tendsto_nhds_unique h_dominated ( by simpa using HasSum.tendsto_sum_nat ( hasSum_nat_add_iff' 1 |>.2 <| hasSum_geometric_of_lt_one ( by norm_num ) <| inv_lt_one_of_one_lt₀ <| by norm_num ) ) ▸ by norm_num;

end Prob610

theorem prob_6_10 (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (h_meas : ∀ k, Measurable (ε k)) (h_indep : iIndepFun (β := fun _ => ℝ) ε P)
    (h_support : ∀ k ω, ε k ω = 1 ∨ ε k ω = -1) (h_prob : ∀ k, P {ω | ε k ω = 1} = 1/2) :
    let S : Ω → ℝ := fun ω => 1 + ∑' k : ℕ, (ε (k+1) ω) * ((1:ℝ)/2)^(k+1)
    E S P = 1 ∧ Var S P = 1/3 := by
  exact ⟨Prob610.E_S_eq_one h_meas h_support h_prob, Prob610.Var_S_eq h_meas h_indep h_support h_prob⟩
