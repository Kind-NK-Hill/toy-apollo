/-
TASK ID: prob_11_9_moment_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_11_9_model_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

theorem prob_11_9_tendsto_one_sub_const_div_pow
    {boxes k : ℕ → ℕ} {a c : ℝ}
    (hc : 0 ≤ c)
    (hboxes : Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ))
      atTop (nhds a)) :
    Tendsto (fun n : ℕ => (1 - c / (boxes n : ℝ)) ^ k n)
      atTop (nhds (Real.exp (-(c * a)))) := by
  have hlog0 :
      Tendsto
        (fun n : ℕ => (boxes n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (-c)) := by
    refine ((Real.tendsto_mul_log_one_add_div_atTop (-c)).comp hboxes).congr' ?_
    exact Eventually.of_forall (fun _ => rfl)
  have hmul0 := hratio.mul hlog0
  have hmul1 :
      Tendsto
        (fun n : ℕ => (k n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (a * (-c))) := by
    refine hmul0.congr' ?_
    filter_upwards [hboxes.eventually_gt_atTop (0 : ℝ)] with n hbn
    have hbne : (boxes n : ℝ) ≠ 0 := ne_of_gt hbn
    field_simp [hbne]
  have hmul :
      Tendsto
        (fun n : ℕ => (k n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (-(c * a))) := by
    convert hmul1 using 1
    ring
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp ((k n : ℝ) *
            Real.log (1 + (-c) / (boxes n : ℝ))))
        atTop (nhds (Real.exp (-(c * a)))) :=
    (Real.continuous_exp.tendsto _).comp hmul
  refine hexp.congr' ?_
  filter_upwards [hboxes.eventually_gt_atTop (c + 1)] with n hlarge
  have hposbox : 0 < (boxes n : ℝ) := lt_trans (by linarith : 0 < c + 1) hlarge
  have hbase : 0 < 1 + (-c) / (boxes n : ℝ) := by
    have hdivlt : c / (boxes n : ℝ) < 1 := by
      rw [div_lt_one hposbox]
      linarith
    have hsub : 0 < 1 - c / (boxes n : ℝ) := sub_pos.mpr hdivlt
    convert hsub using 1
    ring
  calc
    Real.exp ((k n : ℝ) * Real.log (1 + (-c) / (boxes n : ℝ)))
        = Real.exp (Real.log (1 + (-c) / (boxes n : ℝ)) * (k n : ℝ)) := by
          ring
    _ = (1 + (-c) / (boxes n : ℝ)) ^ ((k n : ℕ) : ℝ) := by
      rw [Real.rpow_def_of_pos hbase]
    _ = (1 + (-c) / (boxes n : ℝ)) ^ k n := by
      rw [Real.rpow_natCast]
    _ = (1 - c / (boxes n : ℝ)) ^ k n := by
      ring_nf

theorem prob_11_9_oneBoxIndicator_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i)) :
    Integrable
      (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω) P := by
  rw [integrable_indicator_iff hMeas]
  exact (integrable_const (α := Ω) (μ := P) (1 : ℝ)).integrableOn

theorem prob_11_9_twoBoxIndicator_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j)) :
    Integrable
      (fun ω : Ω =>
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω) P := by
  rw [integrable_indicator_iff hMeas]
  exact (integrable_const (α := Ω) (μ := P) (1 : ℝ)).integrableOn

theorem prob_11_9_oneBoxIndicator_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i)) :
    ∫ ω : Ω,
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω ∂P =
      P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) := by
  rw [show (fun _ : Ω => (1 : ℝ)) = (1 : Ω → ℝ) by
    funext ω
    simp]
  exact
    (MeasureTheory.integral_indicator_one (μ := P)
      (s := prob_11_9_oneBoxEmptyEvent boxes k locations n i) hMeas)

theorem prob_11_9_twoBoxIndicator_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j)) :
    ∫ ω : Ω,
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω ∂P =
      P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) := by
  rw [show (fun _ : Ω => (1 : ℝ)) = (1 : Ω → ℝ) by
    funext ω
    simp]
  exact
    (MeasureTheory.integral_indicator_one (μ := P)
      (s := prob_11_9_twoBoxEmptyEvent boxes k locations n i j) hMeas)

theorem prob_11_9_oneBoxIndicator_mul_self {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n)) :
    (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω) =
      fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  funext ω
  by_cases hω : ω ∈ prob_11_9_oneBoxEmptyEvent boxes k locations n i
  · simp [Set.indicator, hω]
  · simp [Set.indicator, hω]

theorem prob_11_9_oneBoxIndicator_mul_pair {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n)) :
    (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
            (fun _ : Ω => (1 : ℝ)) ω) =
      fun ω : Ω =>
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  funext ω
  by_cases hi : ∀ b : Fin (k n), locations n ω b ≠ i
  · by_cases hj : ∀ b : Fin (k n), locations n ω b ≠ j
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
  · by_cases hj : ∀ b : Fin (k n), locations n ω b ≠ j
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]

theorem prob_11_9_oneBoxIndicator_product_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hOneMeas : ∀ i : Fin (boxes n),
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i))
    (hTwoMeas : ∀ i j : Fin (boxes n),
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j))
    (hOneProb : ∀ i : Fin (boxes n),
      P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
        (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n))
    (hTwoProb : ∀ i j : Fin (boxes n), i ≠ j →
      P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) =
        (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) :
    ∫ ω : Ω,
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
            (fun _ : Ω => (1 : ℝ)) ω ∂P =
      if i = j then
        (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
      else
        (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [prob_11_9_oneBoxIndicator_mul_self]
    simpa [hOneProb i] using
      (prob_11_9_oneBoxIndicator_integral P boxes k locations i (hOneMeas i))
  · rw [if_neg hij]
    rw [prob_11_9_oneBoxIndicator_mul_pair boxes k locations i j]
    simpa [hTwoProb i j hij] using
      (prob_11_9_twoBoxIndicator_integral P boxes k locations i j (hTwoMeas i j))

theorem prob_11_9_emptyBoxRatio_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∫ ω : Ω, prob_11_9_emptyBoxRatio boxes X n ω ∂P =
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  rcases hModel with
    ⟨locations, hX, hOneMeas, _hTwoMeas, hUniform⟩
  have hOneProb :
      ∀ i : Fin (boxes n),
        P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
          (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i => prob_11_9_oneBoxEmptyEvent_probability P boxes k locations
      hbox i (hUniform n)
  let p1 : ℝ := (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  have hYeq :
      (fun ω : Ω => prob_11_9_emptyBoxRatio boxes X n ω) =
        fun ω : Ω =>
          (1 / (boxes n : ℝ)) *
            ∑ i : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω := by
    funext ω
    have hcount :=
      congrFun (prob_11_9_emptyBoxCount_eq_sum_indicators boxes k locations n) ω
    calc
      prob_11_9_emptyBoxRatio boxes X n ω =
          X n ω / (boxes n : ℝ) := rfl
      _ =
          (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ) /
            (boxes n : ℝ) := by
            rw [hX n ω]
      _ =
          (∑ i : Fin (boxes n),
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω) / (boxes n : ℝ) := by
            rw [hcount]
      _ =
          (1 / (boxes n : ℝ)) *
            ∑ i : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω := by
            ring
  have hInt :
      ∀ i ∈ (Finset.univ : Finset (Fin (boxes n))),
        Integrable
          (fun ω : Ω =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i _hi
    exact prob_11_9_oneBoxIndicator_integrable P boxes k locations i
      (hOneMeas n i)
  have hEach :
      ∀ i : Fin (boxes n),
        ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω ∂P = p1 := by
    intro i
    simpa [p1, hOneProb i] using
      (prob_11_9_oneBoxIndicator_integral P boxes k locations i
        (hOneMeas n i))
  rw [hYeq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum Finset.univ hInt]
  calc
    (1 / (boxes n : ℝ)) *
        ∑ i : Fin (boxes n),
          ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω ∂P =
        (1 / (boxes n : ℝ)) * ∑ _i : Fin (boxes n), p1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          exact hEach i
    _ = p1 := by
      have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hbox
      rw [Finset.sum_const]
      simp [Fintype.card_fin, hbne]

theorem prob_11_9_emptyBoxRatio_sq_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∫ ω : Ω, (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 ∂P =
      ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n))) := by
  classical
  rcases hModel with
    ⟨locations, hX, hOneMeas, hTwoMeas, hUniform⟩
  have hOneProb :
      ∀ i : Fin (boxes n),
        P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
          (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i => prob_11_9_oneBoxEmptyEvent_probability P boxes k locations
      hbox i (hUniform n)
  have hTwoProb :
      ∀ i j : Fin (boxes n), i ≠ j →
        P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) =
          (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i j hij => prob_11_9_twoBoxEmptyEvent_probability P boxes k locations
      hbox i j hij (hUniform n)
  let p1 : ℝ := (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let p2 : ℝ := (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let b : ℝ := (boxes n : ℝ)
  have hbne : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast ne_of_gt hbox
  have hYsqeq :
      (fun ω : Ω => (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2) =
        fun ω : Ω =>
          (1 / b ^ 2) *
            ∑ i : Fin (boxes n),
              ∑ j : Fin (boxes n),
                (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                    (fun _ : Ω => (1 : ℝ)) ω *
                  (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                    (fun _ : Ω => (1 : ℝ)) ω := by
    funext ω
    have hcount :=
      congrFun (prob_11_9_emptyBoxCount_eq_sum_indicators boxes k locations n) ω
    let S : ℝ :=
      ∑ i : Fin (boxes n),
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω
    have hsumprod :
        S * S =
          ∑ i : Fin (boxes n),
            ∑ j : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                  (fun _ : Ω => (1 : ℝ)) ω *
                (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                  (fun _ : Ω => (1 : ℝ)) ω := by
      dsimp [S]
      simpa using
        (Finset.sum_mul_sum (Finset.univ : Finset (Fin (boxes n)))
          (Finset.univ : Finset (Fin (boxes n)))
          (fun i : Fin (boxes n) =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω)
          (fun j : Fin (boxes n) =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
              (fun _ : Ω => (1 : ℝ)) ω))
    have hratio :
        prob_11_9_emptyBoxRatio boxes X n ω = S / b := by
      calc
        prob_11_9_emptyBoxRatio boxes X n ω =
            X n ω / (boxes n : ℝ) := rfl
        _ =
            (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ) /
              (boxes n : ℝ) := by
              rw [hX n ω]
        _ = S / b := by
          dsimp [S, b]
          rw [hcount]
    calc
      (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 =
          (S / b) ^ 2 := by rw [hratio]
      _ = (1 / b ^ 2) * (S * S) := by
        field_simp [hbne]
      _ =
          (1 / b ^ 2) *
            ∑ i : Fin (boxes n),
              ∑ j : Fin (boxes n),
                (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                    (fun _ : Ω => (1 : ℝ)) ω *
                  (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                    (fun _ : Ω => (1 : ℝ)) ω := by
          rw [hsumprod]
  have hProdInt :
      ∀ i j : Fin (boxes n),
        Integrable
          (fun ω : Ω =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [prob_11_9_oneBoxIndicator_mul_self boxes k locations i]
      exact prob_11_9_oneBoxIndicator_integrable P boxes k locations i
        (hOneMeas n i)
    · rw [prob_11_9_oneBoxIndicator_mul_pair boxes k locations i j]
      exact prob_11_9_twoBoxIndicator_integrable P boxes k locations i j
        (hTwoMeas n i j)
  have hInnerInt :
      ∀ i ∈ (Finset.univ : Finset (Fin (boxes n))),
        Integrable
          (fun ω : Ω =>
            ∑ j : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                  (fun _ : Ω => (1 : ℝ)) ω *
                (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                  (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i _hi
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _hj => hProdInt i j)
  have hEachIntegral :
      ∀ i j : Fin (boxes n),
        ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω ∂P =
          if i = j then p1 else p2 := by
    intro i j
    simpa [p1, p2] using
      (prob_11_9_oneBoxIndicator_product_integral P boxes k locations i j
        (fun i => hOneMeas n i) (fun i j => hTwoMeas n i j)
        hOneProb hTwoProb)
  rw [hYsqeq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum Finset.univ hInnerInt]
  have hInnerIntegral :
      (∑ i : Fin (boxes n),
        ∫ ω : Ω,
          ∑ j : Fin (boxes n),
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω ∂P) =
        ∑ i : Fin (boxes n), ∑ j : Fin (boxes n), (if i = j then p1 else p2) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _hj => hProdInt i j)]
    apply Finset.sum_congr rfl
    intro j _hj
    exact hEachIntegral i j
  rw [hInnerIntegral]
  rw [prob_11_9_fin_double_two_probability_sum]
  dsimp [b, p1, p2]
  field_simp [show (boxes n : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hbox]

theorem prob_11_9_emptyBoxRatio_bounds {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∀ ω : Ω,
      0 ≤ prob_11_9_emptyBoxRatio boxes X n ω ∧
        prob_11_9_emptyBoxRatio boxes X n ω ≤ 1 := by
  classical
  rcases hModel with
    ⟨locations, hX, _hOneMeas, _hTwoMeas, _hUniform⟩
  intro ω
  have hcard :
      prob_11_9_emptyBoxCountFromLocations boxes k locations n ω ≤ boxes n := by
    unfold prob_11_9_emptyBoxCountFromLocations
    have hle :
        (Finset.univ.filter
          (fun i : Fin (boxes n) => ∀ b : Fin (k n), locations n ω b ≠ i)).card ≤
          (Finset.univ : Finset (Fin (boxes n))).card :=
      Finset.card_filter_le _ _
    simpa [Fintype.card_fin] using hle
  have hbpos : 0 < (boxes n : ℝ) := by exact_mod_cast hbox
  rw [prob_11_9_emptyBoxRatio, hX n ω]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hbpos)
  · rw [div_le_one hbpos]
    exact_mod_cast hcard

theorem prob_11_9_centered_square_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ} (c : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n)
    (hYMeas : AEStronglyMeasurable
      ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ∫ ω : Ω,
        |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 ∂P =
      (((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
        (2 * c) *
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
        c ^ 2 := by
  classical
  let Y : Ω → ℝ := (prob_11_9_emptyBoxRatio boxes X) n
  have hBounds := prob_11_9_emptyBoxRatio_bounds P boxes k X hModel hbox
  have hYInt : Integrable Y P := by
    refine Integrable.of_bound hYMeas 1 ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    dsimp [Y]
    rw [abs_of_nonneg hnonneg]
    exact hle
  have hY2Meas : AEStronglyMeasurable (fun ω : Ω => Y ω ^ 2) P := by
    refine (hYMeas.pow 2).congr ?_
    filter_upwards with ω
    rfl
  have hY2Int : Integrable (fun ω : Ω => Y ω ^ 2) P := by
    refine Integrable.of_bound hY2Meas 1 ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    have hyabs : |Y ω| ≤ 1 := by
      dsimp [Y]
      rw [abs_of_nonneg hnonneg]
      exact hle
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω))]
    nlinarith [hle, hnonneg]
  have hLinInt : Integrable (fun ω : Ω => (2 * c) * Y ω) P :=
    hYInt.const_mul (2 * c)
  have hSubInt :
      Integrable (fun ω : Ω => Y ω ^ 2 - (2 * c) * Y ω) P :=
    hY2Int.sub hLinInt
  calc
    ∫ ω : Ω, |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 ∂P =
        ∫ ω : Ω, Y ω ^ 2 - (2 * c) * Y ω + c ^ 2 ∂P := by
          congr 1
          funext ω
          dsimp [Y]
          rw [sq_abs]
          ring
    _ =
        (∫ ω : Ω, Y ω ^ 2 - (2 * c) * Y ω ∂P) +
          ∫ _ω : Ω, c ^ 2 ∂P := by
          rw [MeasureTheory.integral_add hSubInt (integrable_const (c ^ 2))]
    _ =
        (∫ ω : Ω, Y ω ^ 2 ∂P) -
          (∫ ω : Ω, (2 * c) * Y ω ∂P) +
          c ^ 2 := by
          rw [MeasureTheory.integral_sub hY2Int hLinInt]
          simp
    _ =
        (∫ ω : Ω, (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 ∂P) -
          (2 * c) *
            (∫ ω : Ω, prob_11_9_emptyBoxRatio boxes X n ω ∂P) +
          c ^ 2 := by
          dsimp [Y]
          rw [MeasureTheory.integral_const_mul]
    _ =
      (((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
        (2 * c) *
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
        c ^ 2 := by
          rw [prob_11_9_emptyBoxRatio_sq_integral_eq P boxes k X hModel hbox,
            prob_11_9_emptyBoxRatio_integral_eq P boxes k X hModel hbox]

theorem prob_11_9_meanDeviationMoment_eq_formula {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ} (c : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n)
    (hYMeas : AEStronglyMeasurable
      ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => c) 2 n =
      ENNReal.ofReal
        ((((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
            (boxes n : ℝ) +
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
            ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
          (2 * c) *
            ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
          c ^ 2) := by
  classical
  let Y : Ω → ℝ := (prob_11_9_emptyBoxRatio boxes X) n
  have hBounds := prob_11_9_emptyBoxRatio_bounds P boxes k X hModel hbox
  have hDevMeas :
      AEStronglyMeasurable
        (fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2) P := by
    have hbase : AEStronglyMeasurable (fun ω : Ω => ‖Y ω - c‖ ^ 2) P := by
      exact ((hYMeas.sub aestronglyMeasurable_const).norm.pow 2)
    simpa [Y, Real.norm_eq_abs] using hbase
  have hDevInt :
      Integrable
        (fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2) P := by
    refine Integrable.of_bound hDevMeas ((1 + |c|) ^ 2) ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    have hyabs :
        |prob_11_9_emptyBoxRatio boxes X n ω| ≤ 1 := by
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hdevle :
        |prob_11_9_emptyBoxRatio boxes X n ω - c| ≤ 1 + |c| :=
      by
        have htri := abs_sub (prob_11_9_emptyBoxRatio boxes X n ω) c
        nlinarith [htri, hyabs, abs_nonneg c]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hdevle, abs_nonneg c,
      abs_nonneg (prob_11_9_emptyBoxRatio boxes X n ω - c)]
  have hNonneg :
      0 ≤ᵐ[P]
        fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 :=
    Eventually.of_forall (fun _ω => sq_nonneg _)
  rw [meanDeviationMoment]
  norm_num
  calc
    ∫⁻ ω : Ω,
        ENNReal.ofReal ((prob_11_9_emptyBoxRatio boxes X n ω - c) ^ 2) ∂P
        = ∫⁻ ω : Ω,
            ENNReal.ofReal
              (|prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2) ∂P := by
          congr with ω
          rw [sq_abs]
    _ = ENNReal.ofReal
            (∫ ω : Ω,
              |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 ∂P) := by
          exact
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              hDevInt hNonneg).symm
    _ = _ := by
          rw [prob_11_9_centered_square_integral_eq
            P boxes k X c hModel hbox hYMeas]
