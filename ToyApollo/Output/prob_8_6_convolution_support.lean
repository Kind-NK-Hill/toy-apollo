import ToyApollo.Output.prob_8_6_single_step_support

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

lemma pmfConv_sub (f₁ f₂ g : ℕ → ℝ) (k : ℕ) :
    pmfConv f₁ g k - pmfConv f₂ g k = ∑ j ∈ range (k + 1), (f₁ j - f₂ j) * g (k - j) := by
      simp +decide [ pmfConv, sub_mul ]

/-
Key Fubini-type lemma: ∑_k ∑_{j≤k} a(j)*b(k-j) = (∑_j a(j)) * (∑_m b(m))
    for nonneg summable sequences.
-/
lemma tsum_conv_eq_tsum_mul_tsum (a b : ℕ → ℝ)
    (ha_nn : ∀ k, 0 ≤ a k) (hb_nn : ∀ k, 0 ≤ b k)
    (ha : Summable a) (hb : Summable b) :
    ∑' k, ∑ j ∈ range (k + 1), a j * b (k - j) = (∑' j, a j) * (∑' m, b m) := by
      rw [ Summable.tsum_mul_tsum_eq_tsum_sum_range ];
      · exact ha;
      · assumption;
      · exact .of_norm <| by simpa using Summable.mul_norm ( ha.norm ) ( hb.norm ) ;

/-
Pointwise bound: |conv diff| ≤ conv of |diff| when g ≥ 0.
-/
lemma abs_pmfConv_sub_le (f₁ f₂ g : ℕ → ℝ) (hg_nn : ∀ k, 0 ≤ g k) (k : ℕ) :
    |pmfConv f₁ g k - pmfConv f₂ g k| ≤
      ∑ j ∈ range (k + 1), |f₁ j - f₂ j| * g (k - j) := by
        rw [ pmfConv_sub, ← Finset.sum_congr rfl fun _ _ => by rw [ ← abs_of_nonneg ( hg_nn _ ) ] ];
        convert Finset.abs_sum_le_sum_abs _ _ using 2;
        · rw [ abs_mul, abs_of_nonneg ( hg_nn _ ) ];
          rw [ abs_of_nonneg ( hg_nn _ ) ];
        · infer_instance

/-
Tsum bound: Σ_k |conv_diff(k)| ≤ (Σ_j |f₁(j)-f₂(j)|) for g a valid PMF.
-/
lemma tsum_abs_pmfConv_sub_le (f₁ f₂ g : ℕ → ℝ)
    (hg_nn : ∀ k, 0 ≤ g k) (hg_sum : HasSum g 1)
    (hf_summable : Summable (fun k => |f₁ k - f₂ k|)) :
    ∑' k, |pmfConv f₁ g k - pmfConv f₂ g k| ≤ ∑' j, |f₁ j - f₂ j| := by
      refine' le_trans ( Summable.tsum_le_tsum ( fun k => _ ) _ _ ) _;
      use fun k => ∑ j ∈ Finset.range ( k + 1 ), |f₁ j - f₂ j| * g ( k - j );
      · exact abs_pmfConv_sub_le f₁ f₂ g hg_nn k;
      · refine' .of_nonneg_of_le ( fun k => abs_nonneg _ ) ( fun k => _ ) ( pmfConv_summable ( fun k => |f₁ k - f₂ k| ) g hf_summable hg_sum.summable );
        convert abs_pmfConv_sub_le f₁ f₂ g hg_nn k using 1;
      · have h_conv_sum : Summable (fun k => ∑ j ∈ Finset.range (k + 1), |f₁ j - f₂ j| * g (k - j)) := by
          have h_conv_sum : ∀ {a b : ℕ → ℝ}, Summable a → Summable b → Summable (fun k => ∑ j ∈ Finset.range (k + 1), a j * b (k - j)) := by
            intros a b ha hb;
            refine' .of_norm _;
            exact summable_norm_sum_mul_range_of_summable_norm ha.norm hb.norm
          exact h_conv_sum hf_summable hg_sum.summable;
        convert h_conv_sum using 1;
      · have := tsum_conv_eq_tsum_mul_tsum ( fun k => |f₁ k - f₂ k| ) g ?_ ?_ hf_summable hg_sum.summable;
        · rw [ this, hg_sum.tsum_eq, mul_one ];
        · exact fun k => abs_nonneg _;
        · assumption

/-- Convolving with a valid PMF on the right contracts TV distance. -/
lemma d_TV_conv_contract_right (f₁ f₂ g : ℕ → ℝ)
    (hg_nn : ∀ k, 0 ≤ g k) (hg_sum : HasSum g 1)
    (hf : Summable (fun k => |f₁ k - f₂ k|)) :
    d_TV (pmfConv f₁ g) (pmfConv f₂ g) ≤ d_TV f₁ f₂ := by
  unfold d_TV
  exact mul_le_mul_of_nonneg_left
    (tsum_abs_pmfConv_sub_le f₁ f₂ g hg_nn hg_sum hf) (by norm_num)

/-
Convolving with a valid PMF on the left contracts TV distance.
-/
lemma d_TV_conv_contract_left (f g₁ g₂ : ℕ → ℝ)
    (hf_nn : ∀ k, 0 ≤ f k) (hf_sum : HasSum f 1)
    (hg : Summable (fun k => |g₁ k - g₂ k|)) :
    d_TV (pmfConv f g₁) (pmfConv f g₂) ≤ d_TV g₁ g₂ := by
      convert d_TV_conv_contract_right g₁ g₂ f hf_nn hf_sum hg using 1
      unfold d_TV; congr! 2
      ext k; simp +decide only [pmfConv]
      simp +decide only [← sum_sub_distrib]
      rw [← Finset.sum_flip]
      exact congr_arg _ (Finset.sum_congr rfl fun x hx => by rw [Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hx)]; ring)

/-
============================================================================
Triangle inequality for d_TV
============================================================================
-/
lemma d_TV_triangle (f g h : ℕ → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    d_TV f h ≤ d_TV f g + d_TV g h := by
      have h_triangle : ∀ (f g h : ℕ → ℝ), Summable f → Summable g → Summable h → ∑' k, |f k - h k| ≤ ∑' k, |f k - g k| + ∑' k, |g k - h k| := by
        intro f g h hf hg hh; rw [ ← Summable.tsum_add ] ; apply_rules [ Summable.tsum_le_tsum ];
        · exact fun i => abs_sub_le _ _ _;
        · exact Summable.abs ( hf.sub hh );
        · exact Summable.add ( Summable.abs ( hf.sub hg ) ) ( Summable.abs ( hg.sub hh ) );
        · exact Summable.abs ( hf.sub hg );
        · exact Summable.abs ( hg.sub hh );
      unfold d_TV; convert mul_le_mul_of_nonneg_left ( h_triangle f g h hf hg hh ) ( by norm_num : ( 0 : ℝ ) ≤ 1 / 2 ) using 1 ; ring;

/-
============================================================================
The n-fold convolution TV bound
============================================================================

d_TV of n-fold convolutions is bounded by n times d_TV of components.
-/
lemma d_TV_convN_bound (f g : ℕ → ℝ)
    (hf_nn : ∀ k, 0 ≤ f k) (hf_sum : HasSum f 1)
    (hg_nn : ∀ k, 0 ≤ g k) (hg_sum : HasSum g 1)
    (n : ℕ) :
    d_TV (pmfConvN f n) (pmfConvN g n) ≤ ↑n * d_TV f g := by
      induction' n with n ih <;> simp_all +decide [ Nat.cast_succ ];
      · unfold d_TV pmfConvN; norm_num;
      · -- Apply the triangle inequality to the convolution.
        have h_triangle : d_TV (pmfConv f (pmfConvN f n)) (pmfConv g (pmfConvN g n)) ≤ d_TV (pmfConv f (pmfConvN f n)) (pmfConv f (pmfConvN g n)) + d_TV (pmfConv f (pmfConvN g n)) (pmfConv g (pmfConvN g n)) := by
          apply d_TV_triangle;
          · apply pmfConv_summable;
            · exact hf_sum.summable;
            · exact HasSum.summable ( convN_sum_one f hf_nn hf_sum n );
          · apply pmfConv_summable;
            · exact hf_sum.summable;
            · exact HasSum.summable ( convN_sum_one g hg_nn hg_sum n );
          · apply pmfConv_summable;
            · exact hg_sum.summable;
            · exact HasSum.summable ( convN_sum_one g hg_nn hg_sum n );
        -- Apply the contraction property to each term in the triangle inequality.
        have hfn_nn := convN_nonneg f hf_nn n
        have hfn_sum := convN_sum_one f hf_nn hf_sum n
        have hgn_nn := convN_nonneg g hg_nn n
        have hgn_sum := convN_sum_one g hg_nn hg_sum n
        have h_abs_fg : Summable (fun k => |f k - g k|) :=
          (hf_sum.summable.sub hg_sum.summable).abs
        have h_abs_fn_gn : Summable (fun k => |pmfConvN f n k - pmfConvN g n k|) :=
          (hfn_sum.summable.sub hgn_sum.summable).abs
        have h1 : d_TV (pmfConv f (pmfConvN f n)) (pmfConv f (pmfConvN g n))
            ≤ d_TV (pmfConvN f n) (pmfConvN g n) :=
          d_TV_conv_contract_left f _ _ hf_nn hf_sum h_abs_fn_gn
        have h2 : d_TV (pmfConv f (pmfConvN g n)) (pmfConv g (pmfConvN g n))
            ≤ d_TV f g :=
          d_TV_conv_contract_right f g _ hgn_nn hgn_sum h_abs_fg
        have heq : d_TV (pmfConvN f (n+1)) (pmfConvN g (n+1))
            = d_TV (pmfConv f (pmfConvN f n)) (pmfConv g (pmfConvN g n)) := rfl
        linarith
