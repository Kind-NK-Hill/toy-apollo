import Mathlib

/-!
# Problem 6.7

Consider a sequence X₁, X₂, X₃, ... of nonneg independent random variables,
where P(Xₖ > a) ≥ δ for all k. Show that ∑ Xₖ = ∞ with probability 1.
-/

open MeasureTheory ProbabilityTheory Filter Finset

/-
If infinitely many X_k > a (with a > 0 and all X_k nonneg),
then the partial sums tend to ∞.
-/
lemma tendsto_sum_of_frequently_gt {X : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (h_nn : ∀ k, 0 ≤ X k)
    (h_freq : ∀ N, ∃ k, k ≥ N ∧ X k > a) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, X k) atTop atTop := by
  refine' Filter.tendsto_atTop_atTop.mpr _
  intro B
  obtain ⟨N, hN⟩ : ∃ N, N * a > B := by
    exact ⟨(B + 1) / a, by rw [div_mul_cancel₀ _ ha.ne']; linarith⟩
  obtain ⟨ks, h_ks⟩ :
      ∃ ks : Finset ℕ, ks.card = Nat.ceil N ∧ ∀ k ∈ ks, X k > a := by
    have h_inf : Set.Infinite {k | X k > a} := by
      exact Set.infinite_of_forall_exists_gt fun n => by
        obtain ⟨k, hk₁, hk₂⟩ := h_freq n.succ
        exact ⟨k, hk₂, hk₁⟩
    have := h_inf.exists_subset_card_eq ⌈N⌉₊
    tauto
  use ks.sup id + 1
  intro n hn
  have := Finset.sum_le_sum fun i (hi : i ∈ ks) => h_ks.2 i hi |> le_of_lt
  simp_all +decide
  exact le_trans (by nlinarith [Nat.le_ceil N])
    (this.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_iff.mpr fun x hx =>
        Finset.mem_range.mpr <| lt_of_le_of_lt (Finset.le_sup (f := id) hx) hn)
      fun _ _ _ => h_nn _))

/-
The events {X_k > a} are independent given iIndepFun.
-/
lemma iIndepSet_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℝ) (fun _ => inferInstance) X P)
    (_h_meas : ∀ k, Measurable (X k))
    {a : ℝ} :
    iIndepSet (fun k => {ω | X k ω > a}) P := by
  convert h_indep.comp (fun k ω => ω > a) using 1
  swap
  exact fun _ => by infer_instance
  simp +decide [iIndepSet, iIndepFun]
  simp +decide [Kernel.iIndepSet, Kernel.iIndepFun]
  exact ⟨fun h => fun _ => h, fun h => h measurableSet_Ioi.mem⟩

/-
The sum ∑ P(A_k) = ⊤ when each P(A_k) ≥ δ > 0.
-/
lemma tsum_measure_eq_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : ℕ → Set Ω) (δ : ℝ) (hδ : 0 < δ)
    (h_prob : ∀ k, P (s k) ≥ ENNReal.ofReal δ) :
    ∑' k, P (s k) = ⊤ := by
  refine' top_unique (le_trans _ (ENNReal.tsum_le_tsum h_prob))
  aesop

/-
limsup of {X_k > a} ⊆ {ω | sum diverges}.
-/
lemma limsup_subset_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a) (h_nn : ∀ k ω, 0 ≤ X k ω) :
    limsup (fun k => {ω | X k ω > a}) atTop ⊆
      {ω | Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop atTop} := by
  intro ω
  rw [mem_limsup_iff_frequently_mem]
  refine' fun h => tendsto_sum_of_frequently_gt ha (fun k => h_nn k ω) _
  rw [Filter.frequently_atTop] at h
  tauto

theorem prob_6_7 (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (h_nonneg : ∀ k ω, 0 ≤ X k ω)
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℝ) (fun _ => inferInstance) X P)
    (h_meas : ∀ k, Measurable (X k)) (a : ℝ) (ha : 0 < a) (δ : ℝ)
    (hδ : 0 < δ ∧ δ < 1)
    (h_prob : ∀ k, P {ω | X k ω > a} ≥ ENNReal.ofReal δ) :
    P {ω | Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, X k ω) atTop atTop} = 1 := by
  set A := fun k => {ω | X k ω > a} with hA_def
  have hA_meas : ∀ k, MeasurableSet (A k) := by
    intro k
    exact measurableSet_lt measurable_const (h_meas k)
  have hA_indep : iIndepSet A P := iIndepSet_of_iIndepFun h_indep h_meas
  have hA_sum : ∑' k, P (A k) = ⊤ := tsum_measure_eq_top A δ hδ.1 h_prob
  have hA_limsup : P (limsup A atTop) = 1 :=
    measure_limsup_eq_one hA_meas hA_indep hA_sum
  have hA_sub : limsup A atTop ⊆
      {ω | Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop atTop} :=
    limsup_subset_tendsto ha h_nonneg
  have h_ge : P {ω | Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop atTop} ≥ 1 := by
    rw [← hA_limsup]
    exact measure_mono hA_sub
  exact le_antisymm prob_le_one h_ge
