/-
TASK ID: prob_11_6
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_10_3
import ToyApollo.Output.prob_11_5
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.thm_11_7

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

set_option maxHeartbeats 900000

noncomputable def prob_11_6_partialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n + 1), X i.1 ω

noncomputable def prob_11_6_normalizer (n : ℕ) : ℝ :=
  Real.rpow ((n : ℝ) + 1) (3 / 4 : ℝ)

noncomputable def prob_11_6_scaledSum {Ω : Type*} (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => prob_11_6_partialSum X n ω / prob_11_6_normalizer n

theorem prob_11_6_scaledSum_def {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    prob_11_6_scaledSum X n =
      fun ω => (∑ i : Fin (n + 1), X i.1 ω) / prob_11_6_normalizer n := by
  rfl

def prob_11_6_sixthMomentSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ,
      Integrable (fun ω => (prob_11_6_partialSum X n ω) ^ 6) P ∧
      (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) ≤ C * ((n : ℝ) + 1) ^ 3

def prob_11_6_uniformAEBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c

def prob_11_6_noSingleton {α : Type*} (p : Fin 6 → α) : Prop :=
  ∀ r : Fin 6, ∃ s : Fin 6, s ≠ r ∧ p s = p r

theorem prob_11_6_exists_singleton_of_not_noSingleton {α : Type*} (p : Fin 6 → α)
    (h : ¬ prob_11_6_noSingleton p) :
    ∃ r : Fin 6, ∀ s : Fin 6, s ≠ r → p r ≠ p s := by
  classical
  simp [prob_11_6_noSingleton] at h
  rcases h with ⟨r, hr⟩
  refine ⟨r, fun s hs hEq => ?_⟩
  exact hr s hs (hEq.symm)

theorem prob_11_6_noSingleton_image_card_le_three {α : Type*} [DecidableEq α]
    (p : Fin 6 → α) (hNo : prob_11_6_noSingleton p) :
    (Finset.univ.image p).card ≤ 3 := by
  classical
  have hEach : ∀ b ∈ Finset.univ.image p,
      2 ≤ (Finset.filter (fun a : Fin 6 => p a = b) Finset.univ).card := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨r, _hr, rfl⟩
    rcases hNo r with ⟨s, hsr, hs⟩
    have hrmem : r ∈ Finset.filter (fun a : Fin 6 => p a = p r) Finset.univ := by
      simp
    have hsmem : s ∈ Finset.filter (fun a : Fin 6 => p a = p r) Finset.univ := by
      simp [hs]
    have hone :
        1 < (Finset.filter (fun a : Fin 6 => p a = p r) Finset.univ).card := by
      rw [Finset.one_lt_card]
      exact ⟨r, hrmem, s, hsmem, hsr.symm⟩
    omega
  have hDouble :
      2 * (Finset.univ.image p).card ≤ (Finset.univ : Finset (Fin 6)).card :=
    Finset.mul_card_image_le_card (s := (Finset.univ : Finset (Fin 6))) (f := p) 2 hEach
  have hSix : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  omega

theorem prob_11_6_finset_subset_triple_of_card_le_three {α : Type*}
    [DecidableEq α] [Inhabited α] {s : Finset α} (hs : s.card ≤ 3) :
    ∃ a b c : α, s ⊆ {a, b, c} := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · refine ⟨default, default, default, ?_⟩
    simp [Finset.card_eq_zero.mp h0]
  · rcases Finset.card_eq_one.mp h1 with ⟨a, rfl⟩
    exact ⟨a, a, a, by simp⟩
  · rcases Finset.card_eq_two.mp h2 with ⟨a, b, _hab, rfl⟩
    exact ⟨a, b, b, by simp⟩
  · rcases Finset.card_eq_three.mp h3 with ⟨a, b, c, _hab, _hac, _hbc, rfl⟩
    exact ⟨a, b, c, by simp⟩

theorem prob_11_6_noSingleton_cover_three {α : Type*} [DecidableEq α] [Inhabited α]
    (p : Fin 6 → α) (hNo : prob_11_6_noSingleton p) :
    ∃ t : α × α × α,
      ∀ r : Fin 6, p r = t.1 ∨ p r = t.2.1 ∨ p r = t.2.2 := by
  classical
  rcases prob_11_6_finset_subset_triple_of_card_le_three
      (prob_11_6_noSingleton_image_card_le_three p hNo) with ⟨a, b, c, hsub⟩
  refine ⟨(a, b, c), fun r => ?_⟩
  have hr : p r ∈ Finset.univ.image p := by simp
  have hmem := hsub hr
  simpa using hmem

def prob_11_6_decodeTriple {α : Type*} (t : α × α × α) (k : Fin 3) : α :=
  if k = 0 then t.1 else if k = 1 then t.2.1 else t.2.2

def prob_11_6_encodeTripleValue {α : Type*} [DecidableEq α]
    (t : α × α × α) (x : α) : Fin 3 :=
  if x = t.1 then 0 else if x = t.2.1 then 1 else 2

theorem prob_11_6_decode_encodeTripleValue {α : Type*} [DecidableEq α]
    (t : α × α × α) (x : α)
    (hx : x = t.1 ∨ x = t.2.1 ∨ x = t.2.2) :
    prob_11_6_decodeTriple t (prob_11_6_encodeTripleValue t x) = x := by
  classical
  by_cases h0 : x = t.1
  · rw [h0]
    simp [prob_11_6_decodeTriple, prob_11_6_encodeTripleValue]
  · by_cases h1 : x = t.2.1
    · have ht0 : ¬ t.2.1 = t.1 := by
        intro ht
        exact h0 (h1.trans ht)
      rw [h1]
      simp [prob_11_6_decodeTriple, prob_11_6_encodeTripleValue, ht0]
    · have h2 : x = t.2.2 := by
        rcases hx with hx | hx | hx
        · exact (h0 hx).elim
        · exact (h1 hx).elim
        · exact hx
      have ht0 : ¬ t.2.2 = t.1 := by
        intro ht
        exact h0 (h2.trans ht)
      have ht1 : ¬ t.2.2 = t.2.1 := by
        intro ht
        exact h1 (h2.trans ht)
      rw [h2]
      simp [prob_11_6_decodeTriple, prob_11_6_encodeTripleValue, ht0, ht1]

noncomputable def prob_11_6_coverTriple {α : Type*} [DecidableEq α] [Inhabited α]
    (p : Fin 6 → α) (hNo : prob_11_6_noSingleton p) : α × α × α :=
  Classical.choose (prob_11_6_noSingleton_cover_three p hNo)

theorem prob_11_6_coverTriple_spec {α : Type*} [DecidableEq α] [Inhabited α]
    (p : Fin 6 → α) (hNo : prob_11_6_noSingleton p) :
    ∀ r : Fin 6,
      p r = (prob_11_6_coverTriple p hNo).1 ∨
        p r = (prob_11_6_coverTriple p hNo).2.1 ∨
        p r = (prob_11_6_coverTriple p hNo).2.2 :=
  Classical.choose_spec (prob_11_6_noSingleton_cover_three p hNo)

theorem prob_11_6_noSingleton_tuple_card_le (n : ℕ) :
    Nat.card {p : Fin 6 → Fin (n + 1) // prob_11_6_noSingleton p} ≤
      3 ^ 6 * (n + 1) ^ 3 := by
  classical
  let enc :
      {p : Fin 6 → Fin (n + 1) // prob_11_6_noSingleton p} →
        ((Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) × (Fin 6 → Fin 3)) :=
    fun hp =>
      let t := prob_11_6_coverTriple hp.1 hp.2
      (t, fun r => prob_11_6_encodeTripleValue t (hp.1 r))
  have hdecode :
      ∀ hp : {p : Fin 6 → Fin (n + 1) // prob_11_6_noSingleton p}, ∀ r : Fin 6,
        prob_11_6_decodeTriple (enc hp).1 ((enc hp).2 r) = hp.1 r := by
    intro hp r
    dsimp [enc]
    exact prob_11_6_decode_encodeTripleValue
      (prob_11_6_coverTriple hp.1 hp.2) (hp.1 r)
      (prob_11_6_coverTriple_spec hp.1 hp.2 r)
  have hInj : Function.Injective enc := by
    intro hp hq heq
    apply Subtype.ext
    funext r
    have hfst : (enc hp).1 = (enc hq).1 := congrArg Prod.fst heq
    have hsnd : (enc hp).2 = (enc hq).2 := congrArg Prod.snd heq
    calc
      hp.1 r = prob_11_6_decodeTriple (enc hp).1 ((enc hp).2 r) := (hdecode hp r).symm
      _ = prob_11_6_decodeTriple (enc hq).1 ((enc hq).2 r) := by rw [hfst, hsnd]
      _ = hq.1 r := hdecode hq r
  have hcard := Nat.card_le_card_of_injective enc hInj
  calc
    Nat.card {p : Fin 6 → Fin (n + 1) // prob_11_6_noSingleton p}
        ≤ Nat.card
            ((Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) × (Fin 6 → Fin 3)) := hcard
    _ = 3 ^ 6 * (n + 1) ^ 3 := by
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_prod]
      ring

theorem prob_11_6_memLp_six_of_uniformAEBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    {c : ℝ} (_hc : 0 ≤ c) (hBound : ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c)
    (i : ℕ) :
    MemLp (X i) 6 P := by
  exact MemLp.of_bound (hXae i) c
    (by
      filter_upwards [hBound i] with ω hω
      simpa [Real.norm_eq_abs] using hω)

theorem prob_11_6_six_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    {c : ℝ} (hc : 0 ≤ c) (hBound : ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c)
    (p : Fin 6 → ℕ) :
    Integrable (fun ω => ∏ r : Fin 6, X (p r) ω) P := by
  haveI h663 : ENNReal.HolderTriple (6 : ℝ≥0∞) 6 3 :=
    NNReal.HolderTriple.coe_ennreal (p := 6) (q := 6) (r := 3)
      (by norm_num)
      (NNReal.HolderTriple.mk (by norm_num) (by norm_num) (by norm_num))
  haveI h632 : ENNReal.HolderTriple (6 : ℝ≥0∞) 3 2 :=
    NNReal.HolderTriple.coe_ennreal (p := 6) (q := 3) (r := 2)
      (by norm_num)
      (NNReal.HolderTriple.mk (by norm_num) (by norm_num) (by norm_num))
  haveI h221 : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := inferInstance
  have h6 : ∀ r : Fin 6, MemLp (fun ω => X (p r) ω) 6 P := by
    intro r
    exact prob_11_6_memLp_six_of_uniformAEBound P X hXae hc hBound (p r)
  have h01 : MemLp
      ((fun ω => X (p 0) ω) * (fun ω => X (p 1) ω)) 3 P :=
    (h6 1).mul (h6 0) (hpqr := h663)
  have h012 : MemLp
      ((fun ω => X (p 0) ω * X (p 1) ω) * (fun ω => X (p 2) ω)) 2 P := by
    convert h01.mul (h6 2) (hpqr := h632) using 1
    ext ω
    simp only [Pi.mul_apply]
    ring_nf
  have h34 : MemLp
      ((fun ω => X (p 3) ω) * (fun ω => X (p 4) ω)) 3 P :=
    (h6 4).mul (h6 3) (hpqr := h663)
  have h345 : MemLp
      ((fun ω => X (p 3) ω * X (p 4) ω) * (fun ω => X (p 5) ω)) 2 P := by
    convert h34.mul (h6 5) (hpqr := h632) using 1
    ext ω
    simp only [Pi.mul_apply]
    ring_nf
  have hMem : MemLp
      (((fun ω => X (p 0) ω * X (p 1) ω) * (fun ω => X (p 2) ω)) *
        ((fun ω => X (p 3) ω * X (p 4) ω) * (fun ω => X (p 5) ω))) 1 P :=
    h345.mul h012 (hpqr := h221)
  have hInt := hMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  convert hInt using 1
  ext ω
  simp [Fin.prod_univ_six, mul_assoc]

theorem prob_11_6_six_product_integral_le_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    {c : ℝ} (hc : 0 ≤ c) (hBound : ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c)
    (p : Fin 6 → ℕ) :
    (∫ ω, ∏ r : Fin 6, X (p r) ω ∂P) ≤ c ^ 6 := by
  have hInt :
      Integrable (fun ω => ∏ r : Fin 6, X (p r) ω) P :=
    prob_11_6_six_product_integrable P X hXae hc hBound p
  have hNormLe : (∫ ω, ‖∏ r : Fin 6, X (p r) ω‖ ∂P) ≤ c ^ 6 := by
    have hNormInt : Integrable (fun ω => ‖∏ r : Fin 6, X (p r) ω‖) P := hInt.norm
    have hConst : Integrable (fun _ : Ω => c ^ 6) P := integrable_const (c ^ 6)
    have hAe : (fun ω => ‖∏ r : Fin 6, X (p r) ω‖) ≤ᵐ[P] fun _ : Ω => c ^ 6 := by
      filter_upwards [hBound (p 0), hBound (p 1), hBound (p 2),
        hBound (p 3), hBound (p 4), hBound (p 5)] with ω h0 h1 h2 h3 h4 h5
      rw [Fin.prod_univ_six]
      simp only [Real.norm_eq_abs, abs_mul]
      have h01 : |X (p 0) ω| * |X (p 1) ω| ≤ c * c :=
        mul_le_mul h0 h1 (abs_nonneg _) hc
      have h23 : |X (p 2) ω| * |X (p 3) ω| ≤ c * c :=
        mul_le_mul h2 h3 (abs_nonneg _) hc
      have h45 : |X (p 4) ω| * |X (p 5) ω| ≤ c * c :=
        mul_le_mul h4 h5 (abs_nonneg _) hc
      have h0123 :
          (|X (p 0) ω| * |X (p 1) ω|) *
              (|X (p 2) ω| * |X (p 3) ω|) ≤
            (c * c) * (c * c) := by
        exact mul_le_mul h01 h23 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg hc hc)
      have hAll :
          ((|X (p 0) ω| * |X (p 1) ω|) *
              (|X (p 2) ω| * |X (p 3) ω|)) *
              (|X (p 4) ω| * |X (p 5) ω|) ≤
            ((c * c) * (c * c)) * (c * c) := by
        exact mul_le_mul h0123 h45
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg (mul_nonneg hc hc) (mul_nonneg hc hc))
      calc
        |X (p 0) ω| * |X (p 1) ω| * |X (p 2) ω| * |X (p 3) ω| *
              |X (p 4) ω| * |X (p 5) ω| ≤
            c * c * c * c * c * c := by
              simpa [mul_assoc] using hAll
        _ = c ^ 6 := by ring
    calc
      (∫ ω, ‖∏ r : Fin 6, X (p r) ω‖ ∂P)
          ≤ ∫ _ω : Ω, c ^ 6 ∂P := integral_mono_ae hNormInt hConst hAe
      _ = c ^ 6 := by simp
  calc
    (∫ ω, ∏ r : Fin 6, X (p r) ω ∂P)
        ≤ ‖∫ ω, ∏ r : Fin 6, X (p r) ω ∂P‖ := by
          simpa [Real.norm_eq_abs] using le_abs_self (∫ ω, ∏ r : Fin 6, X (p r) ω ∂P)
    _ ≤ ∫ ω, ‖∏ r : Fin 6, X (p r) ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ c ^ 6 := hNormLe

theorem prob_11_6_partialSum_sixth_expand {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (prob_11_6_partialSum X n ω) ^ 6 =
      ∑ p : Fin 6 → Fin (n + 1), ∏ r : Fin 6, X (p r).1 ω := by
  change (∑ i : Fin (n + 1), X i.1 ω) ^ 6 =
    ∑ p : Fin 6 → Fin (n + 1), ∏ r : Fin 6, X (p r).1 ω
  simpa using
    (Fintype.sum_pow (fun i : Fin (n + 1) => X i.1 ω) 6)

theorem prob_11_6_partialSum_sixth_integrable_of_uniformAEBound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    {c : ℝ} (hc : 0 ≤ c) (hBound : ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c)
    (n : ℕ) :
    Integrable (fun ω => (prob_11_6_partialSum X n ω) ^ 6) P := by
  have hSumMem : MemLp (prob_11_6_partialSum X n) 6 P := by
    change MemLp (fun ω => ∑ i : Fin (n + 1), X i.1 ω) 6 P
    exact memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
      (fun i _hi =>
        prob_11_6_memLp_six_of_uniformAEBound P X hXae hc hBound i.1)
  have hNorm : Integrable (fun ω => ‖prob_11_6_partialSum X n ω‖ ^ (6 : ℝ)) P :=
    hSumMem.integrable_norm_rpow (by norm_num : (6 : ℝ≥0∞) ≠ 0)
      (by norm_num : (6 : ℝ≥0∞) ≠ ∞)
  refine hNorm.congr (Eventually.of_forall ?_)
  intro ω
  change ‖prob_11_6_partialSum X n ω‖ ^ (6 : ℝ) =
    (prob_11_6_partialSum X n ω) ^ 6
  rw [Real.norm_eq_abs]
  rw [show |prob_11_6_partialSum X n ω| ^ (6 : ℝ) =
      |prob_11_6_partialSum X n ω| ^ (6 : ℕ) by
    exact Real.rpow_natCast |prob_11_6_partialSum X n ω| 6]
  exact Even.pow_abs (by norm_num : Even 6) (prob_11_6_partialSum X n ω)

theorem prob_11_6_partialSum_sixth_integral_expand {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    {c : ℝ} (hc : 0 ≤ c) (hBound : ∀ i : ℕ, ∀ᵐ ω ∂P, |X i ω| ≤ c)
    (n : ℕ) :
    (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) =
      ∑ p : Fin 6 → Fin (n + 1),
        ∫ ω, ∏ r : Fin 6, X (p r).1 ω ∂P := by
  have hTermInt : ∀ p : Fin 6 → Fin (n + 1),
      Integrable (fun ω => ∏ r : Fin 6, X (p r).1 ω) P := by
    intro p
    exact prob_11_6_six_product_integrable P X hXae hc hBound (fun r => (p r).1)
  rw [show (fun ω => (prob_11_6_partialSum X n ω) ^ 6) =
      fun ω => ∑ p : Fin 6 → Fin (n + 1), ∏ r : Fin 6, X (p r).1 ω by
        funext ω
        exact prob_11_6_partialSum_sixth_expand X n ω]
  rw [integral_finset_sum (Finset.univ : Finset (Fin 6 → Fin (n + 1)))
    (fun p _hp => hTermInt p)]

theorem prob_11_6_singleton_five_product_integral_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hInd : def_5_10_randomVariables P X) {a b c d e f : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hXae : ∀ i, AEStronglyMeasurable (X i) P) (hMeanA : P[X a] = 0) :
    (∫ ω, X a ω * (X b ω * X c ω * X d ω * X e ω * X f ω) ∂P) = 0 := by
  classical
  dsimp [def_5_10_randomVariables] at hInd
  let S : Finset ℕ := {a}
  let T : Finset ℕ := {b, c, d, e, f}
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hmem
    simp [S] at hx
    subst x
    simp [T, hab, hac, had, hae, haf] at hmem
  have hTuple : ProbabilityTheory.IndepFun
      (fun ω (i : S) => X i.1 ω) (fun ω (i : T) => X i.1 ω) P :=
    hInd.indepFun_finset₀ S T hST (fun i => (hXae i).aemeasurable)
  let ia : S := Subtype.mk a (by simp [S])
  let ib : T := Subtype.mk b (by simp [T])
  let ic : T := Subtype.mk c (by simp [T])
  let id : T := Subtype.mk d (by simp [T])
  let ie : T := Subtype.mk e (by simp [T])
  let iff : T := Subtype.mk f (by simp [T])
  let left : (∀ i : S, ℝ) → ℝ := fun y => y ia
  let right : (∀ i : T, ℝ) → ℝ := fun y =>
    y ib * y ic * y id * y ie * y iff
  have hLeftMeas : Measurable left := by
    dsimp [left]
    exact measurable_pi_apply ia
  have hRightMeas : Measurable right := by
    dsimp [right]
    exact ((((measurable_pi_apply ib).mul
      (measurable_pi_apply ic)).mul
      (measurable_pi_apply id)).mul
      (measurable_pi_apply ie)).mul
      (measurable_pi_apply iff)
  have hIndProd : ProbabilityTheory.IndepFun (X a)
      (fun ω => X b ω * X c ω * X d ω * X e ω * X f ω) P := by
    simpa [left, right, ia, ib, ic, id, ie, iff, S, T, Function.comp_def, mul_assoc] using
      hTuple.comp hLeftMeas hRightMeas
  have hRightAes : AEStronglyMeasurable
      (fun ω => X b ω * X c ω * X d ω * X e ω * X f ω) P :=
    ((((hXae b).mul (hXae c)).mul (hXae d)).mul (hXae e)).mul (hXae f)
  have hProd := hIndProd.integral_fun_mul_eq_mul_integral (hXae a) hRightAes
  simpa [hMeanA, mul_assoc] using hProd

theorem prob_11_6_singleton_product_integral_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hXae : ∀ i, AEStronglyMeasurable (X i) P) (hMean : ∀ i : ℕ, P[X i] = 0)
    (p : Fin 6 → ℕ) (r : Fin 6)
    (hSing : ∀ s : Fin 6, s ≠ r → p r ≠ p s) :
    (∫ ω, ∏ s : Fin 6, X (p s) ω ∂P) = 0 := by
  fin_cases r
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 0) (b := p 1) (c := p 2) (d := p 3) (e := p 4) (f := p 5)
      (hSing 1 (by decide)) (hSing 2 (by decide)) (hSing 3 (by decide))
      (hSing 4 (by decide)) (hSing 5 (by decide)) hXae (hMean (p 0))
    simpa [Fin.prod_univ_six, mul_assoc] using hZ
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 1) (b := p 0) (c := p 2) (d := p 3) (e := p 4) (f := p 5)
      (hSing 0 (by decide)) (hSing 2 (by decide)) (hSing 3 (by decide))
      (hSing 4 (by decide)) (hSing 5 (by decide)) hXae (hMean (p 1))
    simpa [Fin.prod_univ_six, mul_assoc, mul_left_comm, mul_comm] using hZ
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 2) (b := p 0) (c := p 1) (d := p 3) (e := p 4) (f := p 5)
      (hSing 0 (by decide)) (hSing 1 (by decide)) (hSing 3 (by decide))
      (hSing 4 (by decide)) (hSing 5 (by decide)) hXae (hMean (p 2))
    simpa [Fin.prod_univ_six, mul_assoc, mul_left_comm, mul_comm] using hZ
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 3) (b := p 0) (c := p 1) (d := p 2) (e := p 4) (f := p 5)
      (hSing 0 (by decide)) (hSing 1 (by decide)) (hSing 2 (by decide))
      (hSing 4 (by decide)) (hSing 5 (by decide)) hXae (hMean (p 3))
    simpa [Fin.prod_univ_six, mul_assoc, mul_left_comm, mul_comm] using hZ
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 4) (b := p 0) (c := p 1) (d := p 2) (e := p 3) (f := p 5)
      (hSing 0 (by decide)) (hSing 1 (by decide)) (hSing 2 (by decide))
      (hSing 3 (by decide)) (hSing 5 (by decide)) hXae (hMean (p 4))
    simpa [Fin.prod_univ_six, mul_assoc, mul_left_comm, mul_comm] using hZ
  · have hZ := prob_11_6_singleton_five_product_integral_eq_zero P X hInd
      (a := p 5) (b := p 0) (c := p 1) (d := p 2) (e := p 3) (f := p 4)
      (hSing 0 (by decide)) (hSing 1 (by decide)) (hSing 2 (by decide))
      (hSing 3 (by decide)) (hSing 4 (by decide)) hXae (hMean (p 5))
    simpa [Fin.prod_univ_six, mul_assoc, mul_left_comm, mul_comm] using hZ

theorem prob_11_6_sixthMomentSupport_of_uniformAEBound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hXae : ∀ i : ℕ, AEStronglyMeasurable (X i) P)
    (hMean : ∀ i : ℕ, P[X i] = 0)
    (hBoundPkg : prob_11_6_uniformAEBound P X) :
    prob_11_6_sixthMomentSupport P X := by
  classical
  rcases hBoundPkg with ⟨c, hcpos, hBound⟩
  let C : ℝ := (3 ^ 6 : ℝ) * max 1 (c ^ 6)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  · intro n
    constructor
    · exact prob_11_6_partialSum_sixth_integrable_of_uniformAEBound P X hXae
        hcpos.le hBound n
    · rw [prob_11_6_partialSum_sixth_integral_expand P X hXae hcpos.le hBound n]
      let term : (Fin 6 → Fin (n + 1)) → ℝ := fun p =>
        ∫ ω, ∏ r : Fin 6, X (p r).1 ω ∂P
      let good : (Fin 6 → Fin (n + 1)) → Prop := fun p =>
        prob_11_6_noSingleton p
      have hTermGood : ∀ p : Fin 6 → Fin (n + 1), good p → term p ≤ c ^ 6 := by
        intro p _hp
        exact prob_11_6_six_product_integral_le_bound P X hXae hcpos.le hBound
          (fun r => (p r).1)
      have hTermBad : ∀ p : Fin 6 → Fin (n + 1), ¬ good p → term p = 0 := by
        intro p hpbad
        rcases prob_11_6_exists_singleton_of_not_noSingleton p hpbad with ⟨r, hr⟩
        dsimp [term]
        exact prob_11_6_singleton_product_integral_eq_zero P X hInd hXae hMean
          (fun r => (p r).1) r
          (fun s hs hval => hr s hs (Fin.ext hval))
      have hsum_filter :
          (∑ p : Fin 6 → Fin (n + 1), term p) =
            ∑ p ∈ (Finset.univ.filter good), term p := by
        have hbad_sum :
            (∑ p ∈ (Finset.univ.filter fun p : Fin 6 → Fin (n + 1) => ¬ good p),
              term p) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro p hp
          exact hTermBad p (Finset.mem_filter.mp hp).2
        have hsplit := Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Fin 6 → Fin (n + 1))) good term
        rw [← hsplit]
        simp [hbad_sum, add_comm]
      have hcardNat : (Finset.univ.filter good).card ≤ 3 ^ 6 * (n + 1) ^ 3 := by
        have hcard := prob_11_6_noSingleton_tuple_card_le n
        rw [Nat.card_eq_fintype_card] at hcard
        rw [Fintype.card_subtype] at hcard
        simpa [good] using hcard
      have hcardReal :
          ((Finset.univ.filter good).card : ℝ) ≤
            (3 ^ 6 : ℝ) * ((n : ℝ) + 1) ^ 3 := by
        have hcast :
            ((Finset.univ.filter good).card : ℝ) ≤
              ((3 ^ 6 * (n + 1) ^ 3 : ℕ) : ℝ) := by
          exact_mod_cast hcardNat
        have hrewrite :
            ((3 ^ 6 * (n + 1) ^ 3 : ℕ) : ℝ) =
              (3 ^ 6 : ℝ) * ((n : ℝ) + 1) ^ 3 := by
          norm_num
        exact hcast.trans_eq hrewrite
      have hc6_nonneg : 0 ≤ c ^ 6 := by positivity
      calc
        (∑ p : Fin 6 → Fin (n + 1), term p)
            = ∑ p ∈ (Finset.univ.filter good), term p := hsum_filter
        _ ≤ ∑ _p ∈ (Finset.univ.filter good), c ^ 6 := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact hTermGood p (Finset.mem_filter.mp hp).2
        _ = ((Finset.univ.filter good).card : ℝ) * c ^ 6 := by
          simp [mul_comm]
        _ ≤ ((3 ^ 6 : ℝ) * ((n : ℝ) + 1) ^ 3) * c ^ 6 :=
          mul_le_mul_of_nonneg_right hcardReal hc6_nonneg
        _ ≤ ((3 ^ 6 : ℝ) * ((n : ℝ) + 1) ^ 3) * max 1 (c ^ 6) := by
          exact mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (c ^ 6))
            (mul_nonneg (by norm_num) (by positivity))
        _ = C * ((n : ℝ) + 1) ^ 3 := by
          dsimp [C]
          ring

def prob_11_6_tailSummabilitySupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∑' n : ℕ,
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε)) ≠ ∞

theorem prob_11_6_deviation_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (n : ℕ)
    (hInt : Integrable (fun ω => (prob_11_6_partialSum X n ω) ^ 6) P)
    {ε : ℝ} (hε : 0 < ε) :
    P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
      ENNReal.ofReal
        ((∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
          ((ε * prob_11_6_normalizer n) ^ 6)) := by
  let threshold := (ε * prob_11_6_normalizer n) ^ 6
  have hnorm_pos : 0 < prob_11_6_normalizer n := by
    dsimp [prob_11_6_normalizer]
    positivity
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hMarkov :
      P.real {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} ≤
        (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) / threshold := by
    exact thm_10_3 P
      (fun ω => (prob_11_6_partialSum X n ω) ^ 6)
      (Eventually.of_forall fun ω => by positivity)
      hInt hthreshold_pos
  have hsubset :
      almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε ⊆
        {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} := by
    intro ω hω
    have hlt_div : ε < |prob_11_6_partialSum X n ω| / prob_11_6_normalizer n := by
      simpa [almostSureDeviationEvent, prob_11_6_scaledSum, sub_zero, abs_div,
        abs_of_pos hnorm_pos] using hω
    have hmul := mul_lt_mul_of_pos_right hlt_div hnorm_pos
    have hbase_lt : ε * prob_11_6_normalizer n < |prob_11_6_partialSum X n ω| := by
      simpa [div_mul_cancel₀ _ hnorm_pos.ne'] using hmul
    have hpow :
        (ε * prob_11_6_normalizer n) ^ 6 ≤ |prob_11_6_partialSum X n ω| ^ 6 := by
      exact pow_le_pow_left₀ (by positivity) (le_of_lt hbase_lt) 6
    dsimp [threshold]
    simpa [Even.pow_abs (by norm_num : Even 6) (prob_11_6_partialSum X n ω)] using hpow
  have hfinite :
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≠ ∞ := by
    exact measure_ne_top P _
  rw [← MeasureTheory.ofReal_measureReal hfinite]
  have hmono :
      P.real (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
        P.real {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} := by
    exact measureReal_mono (μ := P) hsubset
  exact ENNReal.ofReal_le_ofReal (by
    simpa [threshold] using le_trans hmono hMarkov)

theorem prob_11_6_sixth_moment_ratio_eq_pseries_term
    (C ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (C * ((n : ℝ) + 1) ^ 3) / ((ε * prob_11_6_normalizer n) ^ 6) =
      (C / ε ^ 6) * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  dsimp [prob_11_6_normalizer]
  rw [abs_of_pos hx]
  field_simp [hx.ne', hε.ne']
  have hpow :
      (((n : ℝ) + 1) ^ (3 / 4 : ℝ)) ^ 6 =
        ((n : ℝ) + 1) ^ ((9 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    norm_num
  rw [hpow]
  have hcombine :
      ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (3 / 2 : ℝ) =
        ((n : ℝ) + 1) ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) + 1) 3]
    rw [← Real.rpow_add hx]
    norm_num
  rw [mul_assoc, hcombine]

private theorem prob_11_6_tailSummability_of_sixthMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSixth : prob_11_6_sixthMomentSupport P X) :
    prob_11_6_tailSummabilitySupport P X := by
  rcases hSixth with ⟨C, hCpos, hMoment⟩
  intro ε hε
  have hseries :
      (∑' n : ℕ, ENNReal.ofReal ((C / ε ^ 6) * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)))) ≠ ∞ := by
    have hCoeff : 0 ≤ C / ε ^ 6 := by
      exact div_nonneg hCpos.le (by positivity)
    exact prob_11_5_pseries_bound_ne_top (C / ε ^ 6) hCoeff
  refine ne_top_of_le_ne_top hseries ?_
  refine ENNReal.tsum_le_tsum fun n => ?_
  rcases hMoment n with ⟨hInt, hBound⟩
  have htail :
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
        ENNReal.ofReal
          ((∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
            ((ε * prob_11_6_normalizer n) ^ 6)) := by
    exact prob_11_6_deviation_event_bound P X n hInt hε
  refine le_trans htail ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hthreshold_nonneg : 0 ≤ (ε * prob_11_6_normalizer n) ^ 6 := by positivity
  have hdiv :
      (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
          ((ε * prob_11_6_normalizer n) ^ 6) ≤
        (C * ((n : ℝ) + 1) ^ 3) / ((ε * prob_11_6_normalizer n) ^ 6) := by
    exact div_le_div_of_nonneg_right hBound hthreshold_nonneg
  exact le_trans hdiv
    (le_of_eq (prob_11_6_sixth_moment_ratio_eq_pseries_term C ε hε n))

private theorem prob_11_6_of_tail_summability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hScaled : ∀ n : ℕ, AEStronglyMeasurable (prob_11_6_scaledSum X n) P)
    (hTail : prob_11_6_tailSummabilitySupport P X) :
    ConvergesAlmostSurely P (prob_11_6_scaledSum X) (fun _ => 0) := by
  refine (thm_10_1 P (prob_11_6_scaledSum X) (fun _ : Ω => 0)).2 ?_
  refine ⟨hScaled, aestronglyMeasurable_const, ?_⟩
  intro ε hε
  simpa [prob_11_6_tailSummabilitySupport, deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε)
      (hTail ε hε))

theorem prob_11_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hXae : ∀ n : ℕ, AEStronglyMeasurable (X n) P)
    (hMean : ∀ n : ℕ, P[X n] = 0)
    (hUniformBound : prob_11_6_uniformAEBound P X) :
    ConvergesAlmostSurely P (prob_11_6_scaledSum X) (fun _ => 0) := by
  have hSixthSupport : prob_11_6_sixthMomentSupport P X :=
    prob_11_6_sixthMomentSupport_of_uniformAEBound P X hInd hXae hMean hUniformBound
  have hScaled : ∀ n, AEStronglyMeasurable (prob_11_6_scaledSum X n) P := by
    intro n
    have hsum :
        AEStronglyMeasurable (fun ω => ∑ i : Fin (n + 1), X i.1 ω) P :=
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => hXae i.1)).congr
          (Eventually.of_forall fun _ => by simp)
    have hdenom :
        AEStronglyMeasurable (fun _ : Ω => prob_11_6_normalizer n) P :=
      aestronglyMeasurable_const
    change AEStronglyMeasurable
      (fun ω => (∑ i : Fin (n + 1), X i.1 ω) / prob_11_6_normalizer n) P
    exact (hsum.mul hdenom.inv₀).congr
      (Eventually.of_forall fun _ => rfl)
  exact prob_11_6_of_tail_summability P X hScaled
    (prob_11_6_tailSummability_of_sixthMoment P X hSixthSupport)
