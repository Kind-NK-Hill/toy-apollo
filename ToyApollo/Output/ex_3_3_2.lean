import Mathlib

/-
\textbf{Example 3.3.2 (Uniform Distribution)} \\
Let $F(x)$ be the function defined by
\[
F(x) = \begin{cases}
0 & \text{for } x < 0 \\
x & \text{for } 0 \le x \le 1 \\
1 & \text{for } 1 < x.
\end{cases}
\]
The resulting Lebesgue--Stieltjes measure is a model for uniform distribution between 0 and 1.
For example, for $0 < a < b < 1$, the measure of $(a, b)$ is $b - a$.
-/
noncomputable def F : StieltjesFunction ℝ where
  toFun x := if x < 0 then 0 else if x ≤ 1 then x else 1
  mono' := by
    intro x y hxy
    simp only
    split_ifs <;> linarith
  right_continuous' := by
    intro x;
    rw [ Metric.continuousWithinAt_iff ];
    exact fun ε ε_pos => ⟨ ε, ε_pos, fun y hy hy' => abs_lt.mpr ⟨ by split_ifs <;> linarith [ abs_lt.mp hy', hy.out ], by split_ifs <;> linarith [ abs_lt.mp hy', hy.out ] ⟩ ⟩

theorem ex_3_3_2 (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a < b) :
    F.measure (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
      rw [ StieltjesFunction.measure_Ioo ];
      have h_left_lim : Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds b) := by
        refine' Filter.Tendsto.congr' _ _;
        exact fun x => x;
        · filter_upwards [ Ioo_mem_nhdsLT hab ] with x hx using Eq.symm ( if_neg ( by linarith [ hx.1 ] ) |> fun h => h.trans ( if_pos ( by linarith [ hx.2 ] ) ) );
        · exact Filter.tendsto_id.mono_left inf_le_left;
      have h_left_lim_eq : Function.leftLim (F : ℝ → ℝ) b = b := by
        refine' tendsto_nhds_unique _ h_left_lim;
        apply_rules [ Monotone.tendsto_leftLim ];
        exact fun x y hxy => by exact F.mono hxy;
      rw [ h_left_lim_eq, show ( F : ℝ → ℝ ) a = a by exact if_neg ( by linarith ) |> fun h => h.trans ( if_pos <| by linarith ) ]