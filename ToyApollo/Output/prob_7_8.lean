import Mathlib

open MeasureTheory Filter Set Topology

/-!
# Problem 7.8: Differentiation under the integral sign

## Note on the Lean formalization

The original formalization asked:
```
∀ x ∈ Set.Icc a b, Integrable (fun ω ↦ f' ω x) μ ∧
  HasDerivAt (fun x ↦ ∫ ω, f ω x ∂μ) (∫ ω, f' ω x ∂μ) x
```
This is false at boundary points of [a,b].

**Counterexample** (boundary failure): Ω = ℕ, μ = counting measure, a = 0, b = 1.
Define f(n, x) = x/n² for x ∈ [0,1], extended to x < 0 via the antiderivative of
f'(n,t) = 1/n² + n²t·eⁿᵗ, yielding f(n,x) = x/n² + 1 + nx·eⁿˣ - eⁿˣ for x < 0.
All hypotheses are satisfied: HasDerivAt holds with f'(n,x) = 1/n² on [0,1],
|f'| ≤ 1/n² which is summable. But for x < 0, f(n,x) → 1, so f(·,x) is not
summable and ∫ f(·,x) = 0. The function x ↦ ∫ f(·,x) has different one-sided
derivatives at 0, so HasDerivAt fails.

**Counterexample** (integrability failure when a = b): Ω = [0,1] with Lebesgue
measure, a = b = 0, f(ω,x) = 1_V(ω)·x where V is a Vitali set.
Then f'(ω,0) = 1_V(ω) which is non-measurable, hence not integrable.

Accordingly, the Lean theorem below expresses the derivative conclusion on the source
interval `Set.Icc a b` via `HasDerivWithinAt`, and it makes the nondegeneracy
assumption `a < b` explicit.
-/

/-
Convert the null set from h2 into an ae statement.
-/
private lemma h2_to_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℝ}
    {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ}
    (h2 : ∃ E, MeasurableSet E ∧ μ E = 0 ∧
      ∀ ω ∉ E, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x) :
    ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x := by
      obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h2; filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hE₂ ] with ω hω; aesop;

/-
f'(·,x) is ae-strongly-measurable: it's the ae limit of measurable
    difference quotients (f(·, x + 1/(n+1)) - f(·, x)) · (n+1).
-/
private lemma fprime_aesm {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℝ}
    {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ}
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2ae : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (hab : a < b) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    AEStronglyMeasurable (fun ω ↦ f' ω x) μ := by
      by_cases hx' : x = b;
      · -- Let's choose a sequence $h_n$ such that $h_n \to 0$ and $b + h_n \in [a, b]$ for all $n$.
        obtain ⟨hn_pos, hn_neg, hn_lim⟩ : ∃ hn : ℕ → ℝ, (∀ n, hn n < 0) ∧ (∀ n, b + hn n ∈ Set.Icc a b) ∧ Filter.Tendsto hn Filter.atTop (nhds 0) := by
          refine' ⟨ fun n => - ( b - a ) / 2 ^ ( n + 1 ), _, _, _ ⟩ <;> norm_num;
          · exact fun n => div_neg_of_neg_of_pos ( by linarith ) ( by positivity );
          · exact fun n => ⟨ by rw [ add_div', le_div_iff₀ ] <;> nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : n + 1 ≥ 1 ) ], div_nonpos_of_nonpos_of_nonneg ( by linarith ) ( by positivity ) ⟩;
          · exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ );
        -- By definition of $f'$, we know that for almost every $\omega$, $f'(ω, b) = \lim_{n \to \infty} \frac{f(ω, b + hn_pos n) - f(ω, b)}{hn_pos n}$.
        have h_deriv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (f ω (b + hn_pos n) - f ω b) / hn_pos n) Filter.atTop (nhds (f' ω b)) := by
          filter_upwards [ h2ae ] with ω hω;
          have := hω b ⟨ by linarith, by linarith ⟩;
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at this;
          simpa [ div_eq_inv_mul ] using this.comp ( show Filter.Tendsto ( fun n => hn_pos n ) Filter.atTop ( nhdsWithin 0 { 0 } ᶜ ) from tendsto_nhdsWithin_iff.mpr ⟨ hn_lim.2, Filter.Eventually.of_forall fun n => ne_of_lt ( hn_neg n ) ⟩ );
        have h_measurable : ∀ n, Measurable (fun ω => (f ω (b + hn_pos n) - f ω b) / hn_pos n) := by
          exact fun n => Measurable.mul ( Measurable.sub ( h1 _ ( hn_lim.1 n ) |>.1 ) ( h1 _ ( Set.right_mem_Icc.mpr hab.le ) |>.1 ) ) measurable_const;
        exact ( aestronglyMeasurable_of_tendsto_ae _ ( fun n => ( h_measurable n |> Measurable.aestronglyMeasurable ) ) h_deriv ) |> fun h => h.congr ( by filter_upwards [ h_deriv ] with ω hω; aesop );
      · -- Since $x < b$, we can choose a sequence $h_n \to 0$ such that $x + h_n \in [a,b]$ for all $n$.
        obtain ⟨hn, hhn⟩ : ∃ hn : ℕ → ℝ, (∀ n, 0 < hn n ∧ x + hn n ∈ Set.Icc a b) ∧ Filter.Tendsto hn Filter.atTop (nhds 0) := by
          use fun n => (b - x) / (n + 2);
          exact ⟨ fun n => ⟨ div_pos ( sub_pos.mpr ( lt_of_le_of_ne hx.2 hx' ) ) ( by linarith ), ⟨ by nlinarith [ hx.1, hx.2, div_mul_cancel₀ ( b - x ) ( by linarith : ( n : ℝ ) + 2 ≠ 0 ) ], by nlinarith [ hx.1, hx.2, div_mul_cancel₀ ( b - x ) ( by linarith : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ⟩, tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ⟩;
        have h_diff_quot : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (f ω (x + hn n) - f ω x) / hn n) Filter.atTop (nhds (f' ω x)) := by
          filter_upwards [ h2ae ] with ω hω;
          have := hω x hx;
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at this;
          simpa [ div_eq_inv_mul ] using this.comp ( show Filter.Tendsto ( fun n => hn n ) Filter.atTop ( nhdsWithin 0 { 0 } ᶜ ) from tendsto_nhdsWithin_iff.mpr ⟨ hhn.2, Filter.Eventually.of_forall fun n => ne_of_gt ( hhn.1 n |>.1 ) ⟩ );
        exact aestronglyMeasurable_of_tendsto_ae _ ( fun n => by exact ( h1 ( x + hn n ) ( hhn.1 n |>.2 ) |>.1.sub ( h1 x hx |>.1 ) |> Measurable.div_const <| hn n ) |> Measurable.aestronglyMeasurable ) h_diff_quot

/-
Integrability of f'(·,x) via domination.
-/
private lemma fprime_integrable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ} {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ} {g : Ω → ℝ}
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2ae : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (hg_int : Integrable g μ)
    (hg_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, |f' ω x| ≤ g ω)
    (hab : a < b) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    Integrable (fun ω ↦ f' ω x) μ := by
      refine' hg_int.mono' _ _;
      · exact fprime_aesm h1 h2ae hab x hx;
      · filter_upwards [ hg_bound ] with ω hω using hω x hx

/-
HasDerivAt for interior points via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/
private lemma integral_hasDerivAt_interior {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ} {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ} {g : Ω → ℝ}
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2ae : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (hg_int : Integrable g μ)
    (hg_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, |f' ω x| ≤ g ω)
    (hab : a < b) (x : ℝ) (hx_lo : a < x) (hx_hi : x < b) :
    HasDerivAt (fun x ↦ ∫ ω, f ω x ∂μ) (∫ ω, f' ω x ∂μ) x := by
      convert ( hasDerivAt_integral_of_dominated_loc_of_deriv_le ?_ ?_ ?_ ?_ ?_ ?_ ?_ ) |>.2 using 1;
      any_goals tauto;
      · exact Icc_mem_nhds hx_lo hx_hi;
      · filter_upwards [ Ioo_mem_nhds hx_lo hx_hi ] with y hy using ( h1 y ⟨ hy.1.le, hy.2.le ⟩ ) |>.1.aestronglyMeasurable;
      · exact h1 x ⟨ hx_lo.le, hx_hi.le ⟩ |>.2;
      · convert fprime_aesm h1 h2ae hab x ⟨ hx_lo.le, hx_hi.le ⟩

/-
Left-endpoint one-sided differentiation under the integral sign.
-/
private lemma integral_hasDerivWithinAt_left {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ} {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ} {g : Ω → ℝ}
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2ae : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (hg_int : Integrable g μ)
    (hg_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, |f' ω x| ≤ g ω)
    (hab : a < b) :
    HasDerivWithinAt (fun x ↦ ∫ ω, f ω x ∂μ) (∫ ω, f' ω a ∂μ) (Set.Icc a b) a := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by
    dsimp [c]
    linarith
  have hcb : c < b := by
    dsimp [c]
    linarith
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hfa_int : Integrable (fun ω ↦ f' ω a) μ :=
    fprime_integrable h1 h2ae hg_int hg_bound hab a ha_mem
  let Fext : ℝ → Ω → ℝ := fun x ω =>
    if x < a then f ω a + (x - a) * f' ω a else f ω x
  let Fderiv : ℝ → Ω → ℝ := fun x ω =>
    if x < a then f' ω a else f' ω x
  have hF_meas : ∀ᶠ x in 𝓝 a, AEStronglyMeasurable (Fext x) μ := by
    refine mem_of_superset (Iio_mem_nhds hac) ?_
    intro x hx
    by_cases hxa : x < a
    ·
      have h_int : Integrable (fun ω ↦ f ω a + (x - a) * f' ω a) μ := by
        exact (h1 a ha_mem).2.add (hfa_int.const_mul (x - a))
      simpa [Fext, hxa] using h_int.aestronglyMeasurable
    ·
      have hxa_le : a ≤ x := le_of_not_gt hxa
      have hxIcc : x ∈ Set.Icc a b := ⟨hxa_le, le_trans hx.le hcb.le⟩
      simpa [Fext, hxa] using (h1 x hxIcc).1.aestronglyMeasurable
  have hF_int : Integrable (Fext a) μ := by
    simpa [Fext] using (h1 a ha_mem).2
  have hF'_meas : AEStronglyMeasurable (fun ω ↦ Fderiv a ω) μ := by
    simpa [Fderiv] using hfa_int.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Iio c, |Fderiv x ω| ≤ g ω := by
    filter_upwards [hg_bound] with ω hω x hx
    by_cases hxa : x < a
    ·
      simpa [Fderiv, hxa] using hω a ha_mem
    ·
      have hxa_le : a ≤ x := le_of_not_gt hxa
      have hxIcc : x ∈ Set.Icc a b := ⟨hxa_le, le_trans hx.le hcb.le⟩
      simpa [Fderiv, hxa] using hω x hxIcc
  have h_diff : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Iio c, HasDerivAt (fun y ↦ Fext y ω) (Fderiv x ω) x := by
    filter_upwards [h2ae] with ω hω x hx
    by_cases hxa : x < a
    ·
      have h_lin : HasDerivAt (fun y ↦ (y - a) * f' ω a) (f' ω a) x := by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id x).sub_const a).mul_const (f' ω a)
      have h_aff :
          HasDerivAt ((fun _ ↦ f ω a) + fun y ↦ (y - a) * f' ω a) (f' ω a) x := by
        simpa using (hasDerivAt_const x (f ω a)).add h_lin
      have h_eq :
          (fun y ↦ Fext y ω) =ᶠ[𝓝 x] (((fun _ ↦ f ω a) + fun y ↦ (y - a) * f' ω a)) := by
        refine mem_of_superset (Iio_mem_nhds hxa) ?_
        intro y hy
        have hya : y < a := hy
        simpa [Fext, hya]
      simpa [Fderiv, hxa] using h_aff.congr_of_eventuallyEq h_eq
    ·
      have hxa_le : a ≤ x := le_of_not_gt hxa
      have hxIcc : x ∈ Set.Icc a b := ⟨hxa_le, le_trans hx.le hcb.le⟩
      by_cases hxeq : x = a
      ·
        have h_lin : HasDerivAt (fun y ↦ (y - a) * f' ω a) (f' ω a) a := by
          simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
            ((hasDerivAt_id a).sub_const a).mul_const (f' ω a)
        have h_aff :
            HasDerivAt ((fun _ ↦ f ω a) + fun y ↦ (y - a) * f' ω a) (f' ω a) a := by
          simpa using (hasDerivAt_const a (f ω a)).add h_lin
        have h_left :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω a) (Set.Iio a) a := by
          refine h_aff.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
          ·
            refine mem_of_superset self_mem_nhdsWithin ?_
            intro y hy
            have hya : y < a := hy
            simpa [Fext, hya]
          · simp [Fext]
        have h_right :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω a) (Set.Ici a) a := by
          refine (hω a ha_mem).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
          ·
            refine mem_of_superset self_mem_nhdsWithin ?_
            intro y hy
            have hya : a ≤ y := hy
            simpa [Fext, not_lt.mpr hya]
          · simp [Fext]
        have h_univ :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω a) Set.univ a := by
          have hset : Set.Iio a ∪ Set.Ici a = Set.univ := by
            ext y
            by_cases hy : y < a
            · simp [hy]
            · simp [hy, le_of_not_gt hy]
          simpa [hset] using h_left.union h_right
        rw [hasDerivWithinAt_univ] at h_univ
        simpa [Fderiv, hxeq] using h_univ
      ·
        have hxa_gt : a < x := lt_of_le_of_ne hxa_le (Ne.symm hxeq)
        have h_eq : (fun y ↦ Fext y ω) =ᶠ[𝓝 x] (fun y ↦ f ω y) := by
          refine mem_of_superset (Ioi_mem_nhds hxa_gt) ?_
          intro y hy
          have hya : a < y := hy
          simpa [Fext, not_lt.mpr hya.le]
        simpa [Fderiv, hxa] using (hω x hxIcc).congr_of_eventuallyEq h_eq
  have h_ext :
      HasDerivAt (fun x ↦ ∫ ω, Fext x ω ∂μ) (∫ ω, f' ω a ∂μ) a := by
    simpa [Fderiv] using
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Iio_mem_nhds hac)
        hF_meas hF_int hF'_meas h_bound hg_int h_diff).2
  refine h_ext.hasDerivWithinAt.congr_of_mem ?_ ha_mem
  intro y hy
  simp [Fext, not_lt.mpr hy.1]

/- 
Right-endpoint one-sided differentiation under the integral sign.
-/
private lemma integral_hasDerivWithinAt_right {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ} {f : Ω → ℝ → ℝ} {f' : Ω → ℝ → ℝ} {g : Ω → ℝ}
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2ae : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (hg_int : Integrable g μ)
    (hg_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, |f' ω x| ≤ g ω)
    (hab : a < b) :
    HasDerivWithinAt (fun x ↦ ∫ ω, f ω x ∂μ) (∫ ω, f' ω b ∂μ) (Set.Icc a b) b := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by
    dsimp [c]
    linarith
  have hcb : c < b := by
    dsimp [c]
    linarith
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hfb_int : Integrable (fun ω ↦ f' ω b) μ :=
    fprime_integrable h1 h2ae hg_int hg_bound hab b hb_mem
  let Fext : ℝ → Ω → ℝ := fun x ω =>
    if b < x then f ω b + (x - b) * f' ω b else f ω x
  let Fderiv : ℝ → Ω → ℝ := fun x ω =>
    if b < x then f' ω b else f' ω x
  have hF_meas : ∀ᶠ x in 𝓝 b, AEStronglyMeasurable (Fext x) μ := by
    refine mem_of_superset (Ioi_mem_nhds hcb) ?_
    intro x hx
    by_cases hbx : b < x
    ·
      have h_int : Integrable (fun ω ↦ f ω b + (x - b) * f' ω b) μ := by
        exact (h1 b hb_mem).2.add (hfb_int.const_mul (x - b))
      simpa [Fext, hbx] using h_int.aestronglyMeasurable
    ·
      have hxb_le : x ≤ b := le_of_not_gt hbx
      have hxIcc : x ∈ Set.Icc a b := ⟨le_trans hac.le hx.le, hxb_le⟩
      simpa [Fext, hbx] using (h1 x hxIcc).1.aestronglyMeasurable
  have hF_int : Integrable (Fext b) μ := by
    simpa [Fext] using (h1 b hb_mem).2
  have hF'_meas : AEStronglyMeasurable (fun ω ↦ Fderiv b ω) μ := by
    simpa [Fderiv] using hfb_int.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Ioi c, |Fderiv x ω| ≤ g ω := by
    filter_upwards [hg_bound] with ω hω x hx
    by_cases hbx : b < x
    ·
      simpa [Fderiv, hbx] using hω b hb_mem
    ·
      have hxb_le : x ≤ b := le_of_not_gt hbx
      have hxIcc : x ∈ Set.Icc a b := ⟨le_trans hac.le hx.le, hxb_le⟩
      simpa [Fderiv, hbx] using hω x hxIcc
  have h_diff : ∀ᵐ ω ∂μ, ∀ x ∈ Set.Ioi c, HasDerivAt (fun y ↦ Fext y ω) (Fderiv x ω) x := by
    filter_upwards [h2ae] with ω hω x hx
    by_cases hbx : b < x
    ·
      have h_lin : HasDerivAt (fun y ↦ (y - b) * f' ω b) (f' ω b) x := by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id x).sub_const b).mul_const (f' ω b)
      have h_aff :
          HasDerivAt ((fun _ ↦ f ω b) + fun y ↦ (y - b) * f' ω b) (f' ω b) x := by
        simpa using (hasDerivAt_const x (f ω b)).add h_lin
      have h_eq :
          (fun y ↦ Fext y ω) =ᶠ[𝓝 x] (((fun _ ↦ f ω b) + fun y ↦ (y - b) * f' ω b)) := by
        refine mem_of_superset (Ioi_mem_nhds hbx) ?_
        intro y hy
        have hyb : b < y := hy
        simpa [Fext, hyb]
      simpa [Fderiv, hbx] using h_aff.congr_of_eventuallyEq h_eq
    ·
      have hxb_le : x ≤ b := le_of_not_gt hbx
      have hxIcc : x ∈ Set.Icc a b := ⟨le_trans hac.le hx.le, hxb_le⟩
      by_cases hxeq : x = b
      ·
        have h_lin : HasDerivAt (fun y ↦ (y - b) * f' ω b) (f' ω b) b := by
          simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
            ((hasDerivAt_id b).sub_const b).mul_const (f' ω b)
        have h_aff :
            HasDerivAt ((fun _ ↦ f ω b) + fun y ↦ (y - b) * f' ω b) (f' ω b) b := by
          simpa using (hasDerivAt_const b (f ω b)).add h_lin
        have h_left :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω b) (Set.Iic b) b := by
          refine (hω b hb_mem).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
          ·
            refine mem_of_superset self_mem_nhdsWithin ?_
            intro y hy
            have hyb : y ≤ b := hy
            simpa [Fext, not_lt.mpr hyb]
          · simp [Fext]
        have h_right :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω b) (Set.Ioi b) b := by
          refine h_aff.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
          ·
            refine mem_of_superset self_mem_nhdsWithin ?_
            intro y hy
            have hyb : b < y := hy
            simpa [Fext, hyb]
          · simp [Fext]
        have h_univ :
            HasDerivWithinAt (fun y ↦ Fext y ω) (f' ω b) Set.univ b := by
          have hset : Set.Iic b ∪ Set.Ioi b = Set.univ := by
            ext y
            by_cases hy : y ≤ b
            · simp [hy]
            · simp [hy, lt_of_not_ge hy]
          simpa [hset] using h_left.union h_right
        rw [hasDerivWithinAt_univ] at h_univ
        simpa [Fderiv, hxeq] using h_univ
      ·
        have hxb_lt : x < b := lt_of_le_of_ne hxb_le hxeq
        have h_eq : (fun y ↦ Fext y ω) =ᶠ[𝓝 x] (fun y ↦ f ω y) := by
          refine mem_of_superset (Iio_mem_nhds hxb_lt) ?_
          intro y hy
          have hyb : y < b := hy
          simpa [Fext, not_lt.mpr hyb.le]
        simpa [Fderiv, hbx] using (hω x hxIcc).congr_of_eventuallyEq h_eq
  have h_ext :
      HasDerivAt (fun x ↦ ∫ ω, Fext x ω ∂μ) (∫ ω, f' ω b ∂μ) b := by
    simpa [Fderiv] using
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioi_mem_nhds hcb)
        hF_meas hF_int hF'_meas h_bound hg_int h_diff).2
  refine h_ext.hasDerivWithinAt.congr_of_mem ?_ hb_mem
  intro y hy
  simp [Fext, not_lt.mpr hy.2]

/-- Problem 7.8: differentiation under the integral sign on a closed interval.

The endpoint derivative is encoded as a derivative within the source interval `Set.Icc a b`,
while interior points are upgraded from `HasDerivAt`. -/
theorem prob_7_8 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {a b : ℝ}
    (f : Ω → ℝ → ℝ) (f' : Ω → ℝ → ℝ)
    (h1 : ∀ x ∈ Set.Icc a b,
      Measurable (fun ω ↦ f ω x) ∧ Integrable (fun ω ↦ f ω x) μ)
    (h2 : ∃ E, MeasurableSet E ∧ μ E = 0 ∧
      ∀ ω ∉ E, ∀ x ∈ Set.Icc a b, HasDerivAt (f ω) (f' ω x) x)
    (h3 : ∃ g, Integrable g μ ∧ ∀ᵐ ω ∂μ, ∀ x ∈ Set.Icc a b, |f' ω x| ≤ g ω)
    (hab : a < b) :
    (∀ x ∈ Set.Icc a b, Integrable (fun ω ↦ f' ω x) μ) ∧
    (∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun x ↦ ∫ ω, f ω x ∂μ) (∫ ω, f' ω x ∂μ) (Set.Icc a b) x) := by
  obtain ⟨g, hg_int, hg_bound⟩ := h3
  have h2ae := h2_to_ae h2
  refine ⟨
    (fun x hx => fprime_integrable h1 h2ae hg_int hg_bound hab x hx),
    ?_
  ⟩
  intro x hx
  by_cases hxa : x = a
  · simpa [hxa] using integral_hasDerivWithinAt_left h1 h2ae hg_int hg_bound hab
  by_cases hxb : x = b
  · simpa [hxb] using integral_hasDerivWithinAt_right h1 h2ae hg_int hg_bound hab
  have hx_lo : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
  have hx_hi : x < b := lt_of_le_of_ne hx.2 hxb
  exact (integral_hasDerivAt_interior h1 h2ae hg_int hg_bound hab x hx_lo hx_hi).hasDerivWithinAt
