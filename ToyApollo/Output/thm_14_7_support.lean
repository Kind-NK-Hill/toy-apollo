/-
TASK ID: thm_14_7_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_3_3
import ToyApollo.Output.thm_3_4
import ToyApollo.Output.thm_14_1

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

def thm_14_7_standardNormalCharacteristic (t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) ^ 2) / 2)

def thm_14_7_standardNormalLaw : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 (1 : NNReal), inferInstance⟩

def thm_14_7_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) :
    ProbabilityMeasure ℝ :=
  ⟨P.map X, Measure.isProbabilityMeasure_map hX⟩

theorem thm_14_7_standardNormalCharacteristic_continuous :
    Continuous thm_14_7_standardNormalCharacteristic := by
  unfold thm_14_7_standardNormalCharacteristic
  continuity

theorem thm_14_7_standardNormalLaw_characteristic (t : ℝ) :
    thm_14_1_characteristicFunction thm_14_7_standardNormalLaw t =
      thm_14_7_standardNormalCharacteristic t := by
  unfold thm_14_1_characteristicFunction thm_14_7_standardNormalLaw
    thm_14_7_standardNormalCharacteristic
  change charFun (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) t =
    Complex.exp (-↑t ^ 2 / 2)
  rw [ProbabilityTheory.charFun_gaussianReal (μ := 0) (v := (1 : NNReal)) t]
  norm_num
  congr 1
  ring

theorem thm_14_7_characteristicFunction_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    thm_14_1_characteristicFunction (thm_14_7_law P Y hY) 0 = 1 := by
  unfold thm_14_1_characteristicFunction thm_14_7_law
  rw [MeasureTheory.charFun_zero]
  exact_mod_cast
    (MeasureTheory.isProbabilityMeasure_iff_real.mp
      (Measure.isProbabilityMeasure_map hY))

def thm_14_7_quadraticCharacteristicExpansion
    (φ : ℝ → ℂ) (sigma : ℝ) : Prop :=
  ∃ r : ℝ → ℂ,
    (∀ t : ℝ, φ t = 1 - ((sigma : ℂ) ^ 2 * (t : ℂ) ^ 2) / 2 + r t) ∧
      Tendsto (fun t : ℝ => r t / ((t : ℂ) ^ 2))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ))

theorem thm_14_7_one_plus_const_over_index_tendsto (c : ℂ) :
    Tendsto (fun n : ℕ => (1 + c / ((n : ℂ) + 1)) ^ (n + 1))
      atTop (𝓝 (Complex.exp c)) := by
  have h :=
    (Complex.tendsto_one_add_div_pow_exp c).comp
      (tendsto_add_atTop_nat 1)
  change
    Tendsto (fun n : ℕ => (1 + c / ((n : ℂ) + 1)) ^ (n + 1))
      atTop (𝓝 (Complex.exp c))
  refine h.congr' ?_
  filter_upwards with n
  simp [Nat.cast_add, Nat.cast_one]

def thm_14_7_triangularPowerLimit
    (c : ℝ → ℕ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => c t n) atTop
      (𝓝 (-((t : ℂ) ^ 2) / 2)) →
      Tendsto (fun n : ℕ => (1 + c t n / ((n : ℂ) + 1)) ^ (n + 1))
        atTop (𝓝 (thm_14_7_standardNormalCharacteristic t))

theorem thm_14_7_triangularPowerLimit_proved
    (c : ℝ → ℕ → ℂ) : thm_14_7_triangularPowerLimit c := by
  intro t hc
  unfold thm_14_7_standardNormalCharacteristic
  let target : ℂ := -((t : ℂ) ^ 2) / 2
  let g : ℕ → ℂ := fun m => c t (m - 1) / (m : ℂ)
  have hg : Tendsto (fun m : ℕ => (m : ℂ) * g m) atTop (𝓝 target) := by
    have hshift : Tendsto (fun m : ℕ => c t (m - 1)) atTop (𝓝 target) := by
      exact hc.comp (tendsto_sub_atTop_nat 1)
    refine hshift.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with m hm
    change c t (m - 1) = (m : ℂ) * (c t (m - 1) / (m : ℂ))
    field_simp [Nat.cast_ne_zero.mpr hm]
  have hpow :
      Tendsto (fun m : ℕ => (1 + g m) ^ m) atTop (𝓝 (Complex.exp target)) :=
    Complex.tendsto_one_add_pow_exp_of_tendsto hg
  have hcomp := hpow.comp (tendsto_add_atTop_nat 1)
  refine hcomp.congr' ?_
  filter_upwards with n
  simp [g, Nat.cast_add, Nat.cast_one]

theorem thm_14_7_independentFiniteSumCharacteristic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i : Fin n, AEMeasurable (X i) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) (t : ℝ) :
    thm_14_1_characteristicFunction
        (thm_14_7_law P (fun ω => ∑ i : Fin n, X i ω) (by fun_prop)) t =
      ∏ i : Fin n,
        thm_14_1_characteristicFunction (thm_14_7_law P (X i) (hX i)) t := by
  simpa [thm_14_1_characteristicFunction, thm_14_7_law] using
    congrFun (hIndep.charFun_map_fun_sum_eq_prod hX) t

theorem thm_14_7_centeredUnitVarianceTaylor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hmean : P[X] = 0) (hsecond : P[X ^ 2] = 1) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 Set.univ 0 t =
      1 - (t : ℂ) ^ 2 / 2 := by
  simpa [sub_eq_add_neg] using
    MeasureTheory.taylorWithinEval_charFun_two_zero' hX hmean hsecond t

theorem thm_14_7_centeredUnitVariance_quadraticCharacteristicExpansion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ}
    (hY : AEMeasurable Y P)
    (hMean : P[Y] = 0)
    (hSecond : P[Y ^ 2] = 1) :
    thm_14_7_quadraticCharacteristicExpansion
      (fun t : ℝ =>
        thm_14_1_characteristicFunction (thm_14_7_law P Y hY) t)
      1 := by
  change thm_14_7_quadraticCharacteristicExpansion
    (fun t : ℝ => charFun (P.map Y) t) 1
  have hint : MemLp id 2 (P.map Y) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
    rw [integral_map]
    · simp [← Pi.pow_apply, hSecond]
    · fun_prop
    · fun_prop
  have hTaylorValue : ∀ t : ℝ,
      taylorWithinEval (charFun (P.map Y)) 2 Set.univ 0 t =
        1 - (t : ℂ) ^ 2 / 2 := by
    intro t
    simpa using MeasureTheory.taylorWithinEval_charFun_two_zero' hY hMean hSecond t
  refine ⟨fun t : ℝ =>
    charFun (P.map Y) t -
      taylorWithinEval (charFun (P.map Y)) 2 Set.univ 0 t, ?_, ?_⟩
  · intro t
    change charFun (P.map Y) t =
      1 - ((1 : ℂ) ^ 2 * (t : ℂ) ^ 2) / 2 +
        (charFun (P.map Y) t -
          taylorWithinEval (charFun (P.map Y)) 2 Set.univ 0 t)
    rw [hTaylorValue t]
    ring_nf
  · have hTaylorWithin :=
      (taylor_tendsto (s := Set.univ) (x₀ := (0 : ℝ)) (n := 2)
        convex_univ (Set.mem_univ 0)
        (MeasureTheory.contDiff_charFun (μ := P.map Y) (n := 2) hint).contDiffOn)
    have hTaylorNhds : Tendsto
        (fun x : ℝ => ((x - 0) ^ 2)⁻¹ •
          (charFun (P.map Y) x -
            taylorWithinEval (charFun (P.map Y)) 2 Set.univ 0 x))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      rw [← nhdsWithin_univ]
      exact hTaylorWithin
    have hTaylorPunctured :=
      hTaylorNhds.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    refine hTaylorPunctured.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rw [div_eq_inv_mul]
    rw [Complex.real_smul]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    simp [sub_zero, Complex.ofReal_inv, Complex.ofReal_pow]

def thm_14_7_centeredScaledVar
    {Ω : Type*} (X0 : Ω → ℝ) (mu sigma : ℝ) : Ω → ℝ :=
  fun ω => (X0 ω - mu) / sigma

theorem thm_14_7_centeredScaled_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X0 : Ω → ℝ} (mu sigma : ℝ)
    (hX0 : AEMeasurable X0 P) :
    AEMeasurable (thm_14_7_centeredScaledVar X0 mu sigma) P := by
  unfold thm_14_7_centeredScaledVar
  fun_prop

theorem thm_14_7_centeredScaled_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 : Ω → ℝ} {mu sigma : ℝ}
    (hIntegrable : Integrable X0 P)
    (hMean : P[X0] = mu) :
    P[thm_14_7_centeredScaledVar X0 mu sigma] = 0 := by
  unfold thm_14_7_centeredScaledVar
  rw [integral_div, integral_sub, hMean]
  · simp
  · exact hIntegrable
  · exact integrable_const mu

theorem thm_14_7_centeredScaled_secondMoment_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 : Ω → ℝ} {mu sigma : ℝ}
    (hX0 : AEMeasurable X0 P)
    (hIntegrable : Integrable X0 P)
    (hMean : P[X0] = mu)
    (hVariance : ProbabilityTheory.variance X0 P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    P[(thm_14_7_centeredScaledVar X0 mu sigma) ^ 2] = 1 := by
  have hYmean : P[thm_14_7_centeredScaledVar X0 mu sigma] = 0 :=
    thm_14_7_centeredScaled_mean_zero
      (P := P) (X0 := X0) hIntegrable hMean
  have hYae : AEMeasurable (thm_14_7_centeredScaledVar X0 mu sigma) P :=
    thm_14_7_centeredScaled_aemeasurable mu sigma hX0
  have hYvar :
      ProbabilityTheory.variance (thm_14_7_centeredScaledVar X0 mu sigma) P = 1 := by
    have hYeq :
        thm_14_7_centeredScaledVar X0 mu sigma =
          fun ω => sigma⁻¹ * (X0 ω - mu) := by
      funext ω
      simp [thm_14_7_centeredScaledVar, div_eq_mul_inv, mul_comm]
    calc
      ProbabilityTheory.variance (thm_14_7_centeredScaledVar X0 mu sigma) P
          = ProbabilityTheory.variance (fun ω => sigma⁻¹ * (X0 ω - mu)) P := by
            rw [hYeq]
      _ = (sigma⁻¹) ^ 2 *
            ProbabilityTheory.variance (fun ω => X0 ω - mu) P := by
            exact ProbabilityTheory.variance_const_mul sigma⁻¹
              (fun ω => X0 ω - mu) P
      _ = (sigma⁻¹) ^ 2 * ProbabilityTheory.variance X0 P := by
            rw [ProbabilityTheory.variance_sub_const hX0.aestronglyMeasurable mu]
      _ = (sigma⁻¹) ^ 2 * sigma ^ 2 := by
            rw [hVariance]
      _ = 1 := by
            field_simp [ne_of_gt hsigma]
  have hvarInt := ProbabilityTheory.variance_of_integral_eq_zero (μ := P)
    (X := thm_14_7_centeredScaledVar X0 mu sigma) hYae hYmean
  rw [hvarInt] at hYvar
  exact hYvar

theorem thm_14_7_centeredScaled_quadraticCharacteristicExpansion_of_moments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 : Ω → ℝ} {mu sigma : ℝ}
    (hX0 : AEMeasurable X0 P)
    (hMean0 : P[thm_14_7_centeredScaledVar X0 mu sigma] = 0)
    (hSecond1 : P[(thm_14_7_centeredScaledVar X0 mu sigma) ^ 2] = 1) :
    thm_14_7_quadraticCharacteristicExpansion
      (fun t : ℝ =>
        thm_14_1_characteristicFunction
          (thm_14_7_law P (thm_14_7_centeredScaledVar X0 mu sigma)
            (thm_14_7_centeredScaled_aemeasurable mu sigma hX0)) t)
      1 := by
  exact thm_14_7_centeredUnitVariance_quadraticCharacteristicExpansion
    (P := P) (Y := thm_14_7_centeredScaledVar X0 mu sigma)
    (thm_14_7_centeredScaled_aemeasurable mu sigma hX0) hMean0 hSecond1

theorem thm_14_7_centeredScaled_quadraticCharacteristicExpansion_of_variance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 : Ω → ℝ} {mu sigma : ℝ}
    (hX0 : AEMeasurable X0 P)
    (hIntegrable : Integrable X0 P)
    (hMean : P[X0] = mu)
    (hVariance : ProbabilityTheory.variance X0 P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    thm_14_7_quadraticCharacteristicExpansion
      (fun t : ℝ =>
        thm_14_1_characteristicFunction
          (thm_14_7_law P (thm_14_7_centeredScaledVar X0 mu sigma)
            (thm_14_7_centeredScaled_aemeasurable mu sigma hX0)) t)
      1 := by
  exact thm_14_7_centeredScaled_quadraticCharacteristicExpansion_of_moments
    (P := P) (X0 := X0) hX0
    (thm_14_7_centeredScaled_mean_zero
      (P := P) (X0 := X0) hIntegrable hMean)
    (thm_14_7_centeredScaled_secondMoment_one
      (P := P) (X0 := X0) hX0 hIntegrable hMean hVariance hsigma)

def thm_14_7_centeredScaledSeq
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mu sigma : ℝ) : ℕ → Ω → ℝ :=
  fun k ω => (X k ω - mu) / sigma

theorem thm_14_7_iIndepFun_centeredScaledSeq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {mu sigma : ℝ}
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.iIndepFun (thm_14_7_centeredScaledSeq X mu sigma) P := by
  let g : ℕ → ℝ → ℝ := fun _ x => (x - mu) / sigma
  have hg : ∀ k, Measurable (g k) := by
    intro k
    fun_prop
  simpa [thm_14_7_centeredScaledSeq, g, Function.comp_def] using
    hIndep.comp g hg

theorem thm_14_7_iIndepFun_centeredScaledSeq_fin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {mu sigma : ℝ}
    (hIndep : ProbabilityTheory.iIndepFun X P) (n : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun k : Fin (n + 1) => thm_14_7_centeredScaledSeq X mu sigma k.val) P := by
  have h := thm_14_7_iIndepFun_centeredScaledSeq
    (P := P) (X := X) (mu := mu) (sigma := sigma) hIndep
  simpa using h.precomp (g := fun k : Fin (n + 1) => k.val)
    (by intro a b h; exact Fin.ext h)

theorem thm_14_7_identDistrib_centeredScaledSeq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {mu sigma : ℝ}
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (k : ℕ) :
    IdentDistrib (thm_14_7_centeredScaledSeq X mu sigma k)
      (thm_14_7_centeredScaledSeq X mu sigma 0) P P := by
  let u : ℝ → ℝ := fun x => (x - mu) / sigma
  have hu : Measurable u := by
    fun_prop
  simpa [thm_14_7_centeredScaledSeq, u, Function.comp_def] using
    (hIdent k).comp hu

def thm_14_7_standardizedSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mu sigma : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω =>
    ((∑ k : Fin (n + 1), X k.val ω) - ((n : ℝ) + 1) * mu) /
      (sigma * Real.sqrt ((n : ℝ) + 1))

theorem thm_14_7_standardizedSum_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (thm_14_7_standardizedSum X mu sigma n) P := by
  unfold thm_14_7_standardizedSum
  fun_prop

theorem thm_14_7_standardizedSum_eq_centeredScaled_sum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hsigma : 0 < sigma) (n : ℕ) :
    thm_14_7_standardizedSum X mu sigma n =
      fun ω =>
        (∑ k : Fin (n + 1), thm_14_7_centeredScaledSeq X mu sigma k.val ω) /
          Real.sqrt ((n : ℝ) + 1) := by
  funext ω
  unfold thm_14_7_standardizedSum thm_14_7_centeredScaledSeq
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsum :
      (∑ k : Fin (n + 1), (X k.val ω - mu) / sigma) =
        (((∑ k : Fin (n + 1), X k.val ω) - ((n : ℝ) + 1) * mu) / sigma) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib]
    congr 1
    simp
  rw [hsum]
  field_simp [hsigma_ne, hsqrt_ne]

theorem thm_14_7_standardizedSum_eq_sum_scaled
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hsigma : 0 < sigma) (n : ℕ) :
    thm_14_7_standardizedSum X mu sigma n =
      fun ω => ∑ k : Fin (n + 1),
        thm_14_7_centeredScaledSeq X mu sigma k.val ω /
          Real.sqrt ((n : ℝ) + 1) := by
  funext ω
  unfold thm_14_7_standardizedSum thm_14_7_centeredScaledSeq
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsum :
      (∑ k : Fin (n + 1), (X k.val ω - mu) / sigma) =
        (((∑ k : Fin (n + 1), X k.val ω) - ((n : ℝ) + 1) * mu) / sigma) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib]
    congr 1
    simp
  rw [← Finset.sum_div, hsum]
  field_simp [hsigma_ne, hsqrt_ne]

theorem thm_14_7_standardizedSumCharacteristic_eq_prod_scaled
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hsigma : 0 < sigma) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction
        (thm_14_7_law P (thm_14_7_standardizedSum X mu sigma n)
          (thm_14_7_standardizedSum_aemeasurable X mu sigma hX n)) t =
      ∏ k : Fin (n + 1),
        thm_14_1_characteristicFunction
          (thm_14_7_law P
            (fun ω =>
              thm_14_7_centeredScaledSeq X mu sigma k.val ω /
                Real.sqrt ((n : ℝ) + 1))
            (by
              exact
                (thm_14_7_centeredScaled_aemeasurable mu sigma (hX k.val)).div_const
                  (Real.sqrt ((n : ℝ) + 1)))) t := by
  let Z : Fin (n + 1) → Ω → ℝ := fun k ω =>
    thm_14_7_centeredScaledSeq X mu sigma k.val ω /
      Real.sqrt ((n : ℝ) + 1)
  have hZmeas : ∀ k : Fin (n + 1), AEMeasurable (Z k) P := by
    intro k
    exact
      (thm_14_7_centeredScaled_aemeasurable mu sigma (hX k.val)).div_const
        (Real.sqrt ((n : ℝ) + 1))
  have hYind := thm_14_7_iIndepFun_centeredScaledSeq_fin
    (P := P) (X := X) (mu := mu) (sigma := sigma) hIndep n
  have hZind : ProbabilityTheory.iIndepFun Z P := by
    let g : Fin (n + 1) → ℝ → ℝ :=
      fun _ x => x / Real.sqrt ((n : ℝ) + 1)
    have hg : ∀ k, Measurable (g k) := by
      intro k
      fun_prop
    simpa [Z, g, Function.comp_def] using hYind.comp g hg
  have hprod :=
    thm_14_7_independentFiniteSumCharacteristic (P := P) (X := Z)
      hZmeas hZind t
  have hfun :
      thm_14_7_standardizedSum X mu sigma n =
        fun ω => ∑ i : Fin (n + 1), Z i ω := by
    simpa [Z] using
      thm_14_7_standardizedSum_eq_sum_scaled X mu sigma hsigma n
  change charFun (P.map (thm_14_7_standardizedSum X mu sigma n)) t = _
  rw [hfun]
  simpa [thm_14_1_characteristicFunction, thm_14_7_law, Z] using hprod

theorem thm_14_7_characteristicFunction_eq_of_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y Z : Ω → ℝ} (hY : AEMeasurable Y P) (hZ : AEMeasurable Z P)
    (hYZ : IdentDistrib Y Z P P) (t : ℝ) :
    thm_14_1_characteristicFunction (thm_14_7_law P Y hY) t =
      thm_14_1_characteristicFunction (thm_14_7_law P Z hZ) t := by
  simp [thm_14_1_characteristicFunction, thm_14_7_law, hYZ.map_eq]

theorem thm_14_7_standardizedSumCharacteristic_eq_power_scaled
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hsigma : 0 < sigma) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction
        (thm_14_7_law P (thm_14_7_standardizedSum X mu sigma n)
          (thm_14_7_standardizedSum_aemeasurable X mu sigma hX n)) t =
      (thm_14_1_characteristicFunction
        (thm_14_7_law P
          (fun ω =>
            thm_14_7_centeredScaledSeq X mu sigma 0 ω /
              Real.sqrt ((n : ℝ) + 1))
          (by
            exact
              (thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0)).div_const
                (Real.sqrt ((n : ℝ) + 1)))) t) ^ (n + 1) := by
  rw [thm_14_7_standardizedSumCharacteristic_eq_prod_scaled
    P X mu sigma hX hIndep hsigma n t]
  simpa [Fintype.card_fin] using
    (Finset.prod_eq_pow_card
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun k : Fin (n + 1) =>
        thm_14_1_characteristicFunction
          (thm_14_7_law P
            (fun ω =>
              thm_14_7_centeredScaledSeq X mu sigma k.val ω /
                Real.sqrt ((n : ℝ) + 1))
            (by
              exact
                (thm_14_7_centeredScaled_aemeasurable mu sigma (hX k.val)).div_const
                  (Real.sqrt ((n : ℝ) + 1)))) t)
      (b :=
        thm_14_1_characteristicFunction
          (thm_14_7_law P
            (fun ω =>
              thm_14_7_centeredScaledSeq X mu sigma 0 ω /
                Real.sqrt ((n : ℝ) + 1))
            (by
              exact
                (thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0)).div_const
                  (Real.sqrt ((n : ℝ) + 1)))) t)
      (by
        intro k hk
        let u : ℝ → ℝ := fun x => x / Real.sqrt ((n : ℝ) + 1)
        have hu : Measurable u := by
          fun_prop
        have hIdentScaled :
            IdentDistrib
              (fun ω =>
                thm_14_7_centeredScaledSeq X mu sigma k.val ω /
                  Real.sqrt ((n : ℝ) + 1))
              (fun ω =>
                thm_14_7_centeredScaledSeq X mu sigma 0 ω /
                  Real.sqrt ((n : ℝ) + 1))
              P P := by
          simpa [u, Function.comp_def] using
            (thm_14_7_identDistrib_centeredScaledSeq
              (P := P) (X := X) (mu := mu) (sigma := sigma) hIdent k.val).comp hu
        exact thm_14_7_characteristicFunction_eq_of_identDistrib
          (P := P)
          ((thm_14_7_centeredScaled_aemeasurable mu sigma (hX k.val)).div_const
            (Real.sqrt ((n : ℝ) + 1)))
          ((thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0)).div_const
            (Real.sqrt ((n : ℝ) + 1)))
          hIdentScaled t))

theorem thm_14_7_characteristicFunction_const_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : AEMeasurable Y P) (r t : ℝ) :
    thm_14_1_characteristicFunction
        (thm_14_7_law P (fun ω => r * Y ω) (by
          exact (measurable_const_mul r).aemeasurable.comp_aemeasurable hY)) t =
      thm_14_1_characteristicFunction (thm_14_7_law P Y hY) (r * t) := by
  unfold thm_14_1_characteristicFunction thm_14_7_law
  change charFun (Measure.map (((fun x : ℝ => r * x) ∘ Y)) P) t =
    charFun (Measure.map Y P) (r * t)
  rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY]
  exact MeasureTheory.charFun_map_mul r t

theorem thm_14_7_centeredScaledFactorCharacteristic_eq_base
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction
      (thm_14_7_law P
        (fun ω => thm_14_7_centeredScaledSeq X mu sigma 0 ω /
          Real.sqrt ((n : ℝ) + 1))
        (by
          exact
            (thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0)).div_const
              (Real.sqrt ((n : ℝ) + 1)))) t =
    thm_14_1_characteristicFunction
      (thm_14_7_law P (thm_14_7_centeredScaledSeq X mu sigma 0)
        (thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0)))
      (t / Real.sqrt ((n : ℝ) + 1)) := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    thm_14_7_characteristicFunction_const_mul
      (P := P)
      (Y := thm_14_7_centeredScaledSeq X mu sigma 0)
      (thm_14_7_centeredScaled_aemeasurable mu sigma (hX 0))
      (Real.sqrt ((n : ℝ) + 1))⁻¹ t

def thm_14_7_characteristicPowerCorrection
    (φ : ℝ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1) * (φ (t / Real.sqrt ((n : ℝ) + 1)) - 1)

theorem thm_14_7_characteristicPowerCorrection_identity
    (φ : ℝ → ℂ) (t : ℝ) (n : ℕ) :
    φ (t / Real.sqrt ((n : ℝ) + 1)) =
      1 + thm_14_7_characteristicPowerCorrection φ t n / ((n : ℂ) + 1) := by
  unfold thm_14_7_characteristicPowerCorrection
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn]
  ring

theorem thm_14_7_standardizedSumCharacteristic_eq_correction_power
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hsigma : 0 < sigma) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction
        (thm_14_7_law P (thm_14_7_standardizedSum X mu sigma n)
          (thm_14_7_standardizedSum_aemeasurable (P := P) X mu sigma hX n)) t =
      (1 + thm_14_7_characteristicPowerCorrection
        (fun s : ℝ => thm_14_1_characteristicFunction
          (thm_14_7_law P (thm_14_7_centeredScaledSeq X mu sigma 0)
            (thm_14_7_centeredScaled_aemeasurable (P := P) mu sigma (hX 0))) s)
        t n / ((n : ℂ) + 1)) ^ (n + 1) := by
  rw [thm_14_7_standardizedSumCharacteristic_eq_power_scaled
    (P := P) (X := X) (mu := mu) (sigma := sigma) (hX := hX)
    (hIndep := hIndep) (hIdent := hIdent) (hsigma := hsigma) (n := n) (t := t)]
  rw [thm_14_7_centeredScaledFactorCharacteristic_eq_base
    (P := P) (X := X) (mu := mu) (sigma := sigma) (hX := hX) (n := n) (t := t)]
  let φ : ℝ → ℂ := fun s : ℝ =>
    thm_14_1_characteristicFunction
      (thm_14_7_law P (thm_14_7_centeredScaledSeq X mu sigma 0)
        (thm_14_7_centeredScaled_aemeasurable (P := P) mu sigma (hX 0))) s
  change φ (t / Real.sqrt ((n : ℝ) + 1)) ^ (n + 1) =
    (1 + thm_14_7_characteristicPowerCorrection φ t n / ((n : ℂ) + 1)) ^
      (n + 1)
  rw [thm_14_7_characteristicPowerCorrection_identity φ t n]

theorem thm_14_7_sqrt_index_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1))
      (atTop : Filter ℕ) (atTop : Filter ℝ) := by
  have hnat : Tendsto (fun n : ℕ => n + 1)
      (atTop : Filter ℕ) (atTop : Filter ℕ) :=
    tendsto_add_atTop_nat 1
  have hbase : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
      (atTop : Filter ℕ) (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hbase' : Tendsto (fun n : ℕ => (n : ℝ) + 1)
      (atTop : Filter ℕ) (atTop : Filter ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hbase
  exact Real.tendsto_sqrt_atTop.comp hbase'

theorem thm_14_7_scaledArgument_tendsto_zero (t : ℝ) :
    Tendsto (fun n : ℕ => t / Real.sqrt ((n : ℝ) + 1))
      (atTop : Filter ℕ) (𝓝 0) := by
  exact Filter.Tendsto.div_atTop tendsto_const_nhds
    thm_14_7_sqrt_index_tendsto_atTop

theorem thm_14_7_scaledArgument_sq (t : ℝ) (n : ℕ) :
    ((t / Real.sqrt ((n : ℝ) + 1) : ℂ)^2) =
      (t : ℂ)^2 / ((n : ℂ) + 1) := by
  have hNnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  have hsqrt_sq : (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 = ((n : ℂ) + 1) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hNnonneg]
    norm_num
  calc
    ((t / Real.sqrt ((n : ℝ) + 1) : ℂ)^2)
        = (t : ℂ)^2 / (Real.sqrt ((n : ℝ) + 1) : ℂ)^2 := by
          ring_nf
    _ = (t : ℂ)^2 / ((n : ℂ) + 1) := by rw [hsqrt_sq]

theorem thm_14_7_characteristicPowerCorrection_algebra
    (T N R X2 : ℂ) (hN : N ≠ 0) (hT : T ≠ 0)
    (hX2 : X2 = T ^ 2 / N) :
    N * (-(X2 / 2) + R) = -T ^ 2 / 2 + T ^ 2 * (R / X2) := by
  subst X2
  field_simp [hN, hT]

theorem thm_14_7_characteristicPowerCorrection_tendsto_of_expansion
    (φ : ℝ → ℂ)
    (hφ : thm_14_7_quadraticCharacteristicExpansion φ 1)
    (hφ0 : φ 0 = 1) (t : ℝ) :
    Tendsto (fun n : ℕ => thm_14_7_characteristicPowerCorrection φ t n)
      atTop (𝓝 (-((t : ℂ) ^ 2) / 2)) := by
  rcases hφ with ⟨r, hdecomp, hrem⟩
  by_cases ht : t = 0
  · subst t
    simp [thm_14_7_characteristicPowerCorrection, hφ0]
  · let x : ℕ → ℝ := fun n => t / Real.sqrt ((n : ℝ) + 1)
    have hx0 : Tendsto x atTop (𝓝 0) := by
      simpa [x] using thm_14_7_scaledArgument_tendsto_zero t
    have hx_ne : ∀ᶠ n in atTop, x n ∈ ({0}ᶜ : Set ℝ) := by
      filter_upwards with n
      have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < (n : ℝ) + 1))
      simp [x, ht, hsqrt_ne]
    have hx_within : Tendsto x atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x hx0 hx_ne
    have hremSeq :
        Tendsto (fun n : ℕ => r (x n) / ((x n : ℂ) ^ 2))
          atTop (𝓝 (0 : ℂ)) :=
      hrem.comp hx_within
    have hterm :
        Tendsto
          (fun n : ℕ => (t : ℂ) ^ 2 * (r (x n) / ((x n : ℂ) ^ 2)))
          atTop (𝓝 ((t : ℂ) ^ 2 * 0)) :=
      Filter.Tendsto.const_mul ((t : ℂ) ^ 2) hremSeq
    have hsum :
        Tendsto
          (fun n : ℕ => -((t : ℂ) ^ 2) / 2 +
            (t : ℂ) ^ 2 * (r (x n) / ((x n : ℂ) ^ 2)))
          atTop (𝓝 (-((t : ℂ) ^ 2) / 2 + (t : ℂ) ^ 2 * 0)) :=
      Filter.Tendsto.const_add (-((t : ℂ) ^ 2) / 2) hterm
    have hcongr : ∀ᶠ n in atTop,
        thm_14_7_characteristicPowerCorrection φ t n =
          -((t : ℂ) ^ 2) / 2 +
            (t : ℂ) ^ 2 * (r (x n) / ((x n : ℂ) ^ 2)) := by
      filter_upwards with n
      have hN : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      have hde := hdecomp (x n)
      unfold thm_14_7_characteristicPowerCorrection
      rw [hde]
      have hT : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hx2 : ((x n : ℂ) ^ 2) = (t : ℂ) ^ 2 / ((n : ℂ) + 1) := by
        simpa [x] using thm_14_7_scaledArgument_sq t n
      have halg :=
        thm_14_7_characteristicPowerCorrection_algebra
          (T := (t : ℂ)) (N := ((n : ℂ) + 1))
          (R := r (x n)) (X2 := ((x n : ℂ) ^ 2)) hN hT hx2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using halg
    have hfinal :
        Tendsto (fun n : ℕ => thm_14_7_characteristicPowerCorrection φ t n)
          atTop (𝓝 (-((t : ℂ) ^ 2) / 2 + (t : ℂ) ^ 2 * 0)) := by
      refine Filter.Tendsto.congr' ?_ hsum
      filter_upwards [hcongr] with n hn
      exact hn.symm
    simpa using hfinal

def thm_14_7_standardizedSumLaws
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n =>
    thm_14_7_law P (thm_14_7_standardizedSum X mu sigma n)
      (thm_14_7_standardizedSum_aemeasurable X mu sigma hX n)

theorem thm_14_7_pointwiseCharacteristicConvergence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hIntegrable : Integrable (X 0) P)
    (hSquareIntegrable : Integrable (fun ω => (X 0 ω) ^ 2) P)
    (hMean : P[X 0] = mu)
    (hVariance : ProbabilityTheory.variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    thm_14_1_pointwiseCharFunConvergence
      (thm_14_7_standardizedSumLaws P X mu sigma hX)
      thm_14_7_standardNormalCharacteristic := by
  have _hSquareIntegrable := hSquareIntegrable
  intro t
  let φ : ℝ → ℂ := fun s : ℝ =>
    thm_14_1_characteristicFunction
      (thm_14_7_law P (thm_14_7_centeredScaledSeq X mu sigma 0)
        (thm_14_7_centeredScaled_aemeasurable (P := P) mu sigma (hX 0))) s
  have hφ : thm_14_7_quadraticCharacteristicExpansion φ 1 := by
    simpa [φ, thm_14_7_centeredScaledSeq, thm_14_7_centeredScaledVar] using
      thm_14_7_centeredScaled_quadraticCharacteristicExpansion_of_variance
        (P := P) (X0 := X 0) (mu := mu) (sigma := sigma)
        (hX 0) hIntegrable hMean hVariance hsigma
  have hφ0 : φ 0 = 1 := by
    simpa [φ] using
      thm_14_7_characteristicFunction_zero
        (P := P) (Y := thm_14_7_centeredScaledSeq X mu sigma 0)
        (thm_14_7_centeredScaled_aemeasurable (P := P) mu sigma (hX 0))
  have hc :
      Tendsto (fun n : ℕ => thm_14_7_characteristicPowerCorrection φ t n)
        atTop (𝓝 (-((t : ℂ) ^ 2) / 2)) :=
    thm_14_7_characteristicPowerCorrection_tendsto_of_expansion φ hφ hφ0 t
  have hpow :=
    thm_14_7_triangularPowerLimit_proved
      (fun s n => thm_14_7_characteristicPowerCorrection φ s n) t hc
  refine Filter.Tendsto.congr' ?_ hpow
  filter_upwards with n
  exact (thm_14_7_standardizedSumCharacteristic_eq_correction_power
    (P := P) (X := X) (mu := mu) (sigma := sigma) (hX := hX)
    (hIndep := hIndep) (hIdent := hIdent) (hsigma := hsigma)
    (n := n) (t := t)).symm
