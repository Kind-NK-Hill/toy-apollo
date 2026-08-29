/-
TASK ID: ex_6_5_2
TYPE: Example_Proof
SOURCE PLAN: 23_chap6_application_hat_ball_bin
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Finset BigOperators

noncomputable section

namespace Ex652Support

abbrev BallΩ (n k : ℕ) := Fin k → Fin n

instance instMeasurableSpaceBallΩ (n k : ℕ) : MeasurableSpace (BallΩ n k) := ⊤

noncomputable def ballMeasure (n k : ℕ) : Measure (BallΩ n k) := by
  classical
  by_cases h : Nonempty (BallΩ n k)
  · letI := h
    exact (PMF.uniformOfFintype (BallΩ n k)).toMeasure
  · exact 0

instance instIsFiniteMeasureBallMeasure (n k : ℕ) :
    IsFiniteMeasure (ballMeasure n k) := by
  classical
  by_cases h : Nonempty (BallΩ n k)
  · rw [ballMeasure, dif_pos h]
    infer_instance
  · rw [ballMeasure, dif_neg h]
    infer_instance

lemma nonempty_ballΩ_of_pos (n k : ℕ) (hn : 0 < n) : Nonempty (BallΩ n k) := by
  refine ⟨fun _ => ⟨0, hn⟩⟩

def locations (n k : ℕ) : BallΩ n k → (Fin k → Fin n) := fun ω => ω

def occupancy (n k : ℕ) (ω : BallΩ n k) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun b : Fin k => ω b = i).card

def occupancyVector (n k : ℕ) (ω : BallΩ n k) : Fin n → ℕ :=
  fun i => occupancy n k ω i

def singleBinEvent (n k : ℕ) (i : Fin n) : Set (BallΩ n k) :=
  {ω | occupancy n k ω i = 1}

def singleBinIndicator (n k : ℕ) (i : Fin n) : BallΩ n k → ℝ :=
  fun ω => if occupancy n k ω i = 1 then 1 else 0

def singleBinCount (n k : ℕ) : BallΩ n k → ℝ :=
  fun ω => ∑ i : Fin n, singleBinIndicator n k i ω

theorem measurableSet_singleBinEvent (n k : ℕ) (i : Fin n) :
    MeasurableSet (singleBinEvent n k i) := by
  simp [singleBinEvent]

theorem singleBinIndicator_eq_indicator (n k : ℕ) (i : Fin n) :
    singleBinIndicator n k i =
      Set.indicator (singleBinEvent n k i) (fun _ : BallΩ n k => (1 : ℝ)) := by
  funext ω
  by_cases hω : occupancy n k ω i = 1
  · simp [singleBinIndicator, singleBinEvent, Set.indicator, hω]
  · simp [singleBinIndicator, singleBinEvent, Set.indicator, hω]

theorem singleBinCount_eq_sum (n k : ℕ) :
    singleBinCount n k = fun ω => ∑ i : Fin n, singleBinIndicator n k i ω := by
  rfl

abbrev BallsExcept (k : ℕ) (b : Fin k) := {x : Fin k // x ≠ b}

abbrev BinsExcept (n : ℕ) (i : Fin n) := {x : Fin n // x ≠ i}

lemma card_binsExcept (n : ℕ) (i : Fin n) :
    Fintype.card (BinsExcept n i) = n - 1 := by
  simpa [Fintype.card_fin] using
    (Fintype.card_subtype_compl (fun x : Fin n => x = i)).trans (by
      rw [Fintype.card_subtype_eq i])

lemma card_ballsExcept_succ (m : ℕ) (b : Fin (m + 1)) :
    Fintype.card (BallsExcept (m + 1) b) = m := by
  simpa [Fintype.card_fin] using
    (Fintype.card_subtype_compl (fun x : Fin (m + 1) => x = b)).trans (by
      rw [Fintype.card_subtype_eq b])

def encodeSingleBin (n m : ℕ) (i : Fin n) :
    (Σ b : Fin (m + 1), BallsExcept (m + 1) b → BinsExcept n i) →
      {ω : BallΩ n (m + 1) // occupancy n (m + 1) ω i = 1}
  | ⟨b, g⟩ =>
      ⟨fun x => if h : x = b then i else (g ⟨x, h⟩ : Fin n), by
        have hfilter :
            Finset.filter
                (fun x : Fin (m + 1) =>
                  (if h : x = b then i else (g ⟨x, h⟩ : Fin n)) = i)
                Finset.univ = {b} := by
          ext x
          by_cases hx : x = b
          · simp [hx]
          · simp [hx, (g ⟨x, hx⟩).2]
        have hcard :
            (Finset.filter
              (fun x : Fin (m + 1) =>
                (if h : x = b then i else (g ⟨x, h⟩ : Fin n)) = i)
              Finset.univ).card = 1 := by
          rw [hfilter]
          simp
        simpa [occupancy] using hcard ⟩

lemma encodeSingleBin_injective (n m : ℕ) (i : Fin n) :
    Function.Injective (encodeSingleBin n m i) := by
  intro x y hxy
  rcases x with ⟨bx, gx⟩
  rcases y with ⟨byy, gy⟩
  have hfun := congrArg Subtype.val hxy
  have hbxy : bx = byy := by
    by_contra hne
    have hx_at_bx : (encodeSingleBin n m i ⟨bx, gx⟩ : BallΩ n (m + 1)) bx = i := by
      simp [encodeSingleBin]
    have hy_at_bx :
        (encodeSingleBin n m i ⟨byy, gy⟩ : BallΩ n (m + 1)) bx ≠ i := by
      simpa [encodeSingleBin, hne] using (gy ⟨bx, hne⟩).2
    exact hy_at_bx <| by simpa [hfun] using hx_at_bx
  subst hbxy
  have hg : gx = gy := by
    funext x
    apply Subtype.ext
    have hval := congrArg (fun f : BallΩ n (m + 1) => f x.1) hfun
    simpa [encodeSingleBin, x.2] using hval
  simp [hg]

lemma encodeSingleBin_surjective (n m : ℕ) (i : Fin n) :
    Function.Surjective (encodeSingleBin n m i) := by
  intro ω
  let s : Finset (Fin (m + 1)) := Finset.filter (fun b : Fin (m + 1) => ω.1 b = i) Finset.univ
  have hs_card : s.card = 1 := by
    simpa [s, occupancy] using ω.2
  rcases Finset.card_eq_one.mp hs_card with ⟨b, hb⟩
  refine ⟨⟨b, fun x => ⟨ω.1 x.1, ?_⟩⟩, ?_⟩
  · have hxnot_singleton : x.1 ∉ ({b} : Finset (Fin (m + 1))) := by
      simp [x.2]
    have hxnot : x.1 ∉ s := by
      simpa [hb] using hxnot_singleton
    intro hxi
    have hxmem : x.1 ∈ s := by
      simp [s, hxi]
    exact hxnot hxmem
  · apply Subtype.ext
    funext x
    by_cases hx : x = b
    · have hmem : b ∈ s := by
        simpa [hb]
      have hbval : ω.1 b = i := by
        simpa [s] using hmem
      simp [encodeSingleBin, hx, hbval]
    · simp [encodeSingleBin, hx]

lemma card_singleBinEvent (n k : ℕ) (hn : 0 < n) (i : Fin n) :
    Fintype.card {ω : BallΩ n k | occupancy n k ω i = 1} = k * (n - 1) ^ (k - 1) := by
  cases k with
  | zero =>
      simp [occupancy]
  | succ m =>
      have hbij :
          Function.Bijective
            (encodeSingleBin n m i) := by
        exact ⟨encodeSingleBin_injective n m i, encodeSingleBin_surjective n m i⟩
      have hcard :
          Fintype.card {ω : BallΩ n (m + 1) | occupancy n (m + 1) ω i = 1} =
            Fintype.card (Σ b : Fin (m + 1), BallsExcept (m + 1) b → BinsExcept n i) := by
        exact (Fintype.card_of_bijective (f := encodeSingleBin n m i) hbij).symm
      rw [hcard, Fintype.card_sigma]
      simp [card_binsExcept, card_ballsExcept_succ, Fintype.card_fun, Finset.sum_const,
        Fintype.card_fin, nsmul_eq_mul]

lemma sum_singleBinIndicator (n k : ℕ) (hn : 0 < n) (i : Fin n) :
    (∑ ω : BallΩ n k, singleBinIndicator n k i ω) =
      (k : ℝ) * (((n - 1 : ℕ) : ℝ) ^ (k - 1)) := by
  calc
    (∑ ω : BallΩ n k, singleBinIndicator n k i ω)
        = ((Finset.filter (fun ω : BallΩ n k => occupancy n k ω i = 1) Finset.univ).card : ℝ) := by
            simp [singleBinIndicator]
    _ = (Fintype.card {ω : BallΩ n k | occupancy n k ω i = 1} : ℝ) := by
          rw [Fintype.card_subtype]
          congr with ω
    _ = ((k * (n - 1) ^ (k - 1) : ℕ) : ℝ) := by
          exact congrArg (fun t : ℕ => (t : ℝ)) (card_singleBinEvent n k hn i)
    _ = (k : ℝ) * (((n - 1 : ℕ) : ℝ) ^ (k - 1)) := by
          norm_num [Nat.cast_mul, Nat.cast_pow]

theorem integral_singleBinIndicator_eq_prob (n k : ℕ) (hn : 0 < n) (i : Fin n) :
    ∫ ω, singleBinIndicator n k i ω ∂ ballMeasure n k =
      (ballMeasure n k).real (singleBinEvent n k i) := by
  rw [ballMeasure, dif_pos (nonempty_ballΩ_of_pos n k hn)]
  rw [singleBinIndicator_eq_indicator]
  simpa using
    (MeasureTheory.integral_indicator_one
      (μ := ballMeasure n k) (s := singleBinEvent n k i)
      (hs := measurableSet_singleBinEvent n k i))

theorem integral_singleBinIndicator_eq_closedForm (n k : ℕ) (hn : 0 < n) (i : Fin n) :
    ∫ ω, singleBinIndicator n k i ω ∂ ballMeasure n k =
      (k : ℝ) * ((1 : ℝ) / n) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
  rw [ballMeasure, dif_pos (nonempty_ballΩ_of_pos n k hn)]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  erw [MeasureTheory.integral_fintype]
  · cases k with
    | zero =>
        simp [singleBinIndicator, occupancy]
    | succ m =>
        have hcard :
            Fintype.card {ω : BallΩ n (m + 1) | occupancy n (m + 1) ω i = 1} =
              (m + 1) * (n - 1) ^ m := by
          simpa using card_singleBinEvent n (m + 1) hn i
        have hcardR :
            (Fintype.card {ω : BallΩ n (m + 1) | occupancy n (m + 1) ω i = 1} : ℝ) =
              ((m + 1) * (n - 1) ^ m : ℕ) := by
          exact_mod_cast hcard
        simp [singleBinIndicator, PMF.uniformOfFintype_apply, MeasureTheory.measureReal_def,
          Fintype.card_fun]
        have hsum :
            (∑ ω : BallΩ n (m + 1),
              if occupancy n (m + 1) ω i = 1 then (((n : ℝ) ^ (m + 1))⁻¹) else 0) =
              (Fintype.card {ω : BallΩ n (m + 1) | occupancy n (m + 1) ω i = 1} : ℝ) *
                (((n : ℝ) ^ (m + 1))⁻¹) := by
          have hcard_filter :
              (Finset.filter (fun ω : BallΩ n (m + 1) => occupancy n (m + 1) ω i = 1)
                Finset.univ).card =
                  Fintype.card {ω : BallΩ n (m + 1) | occupancy n (m + 1) ω i = 1} := by
            rw [Fintype.card_subtype]
            congr with ω
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [hcard_filter]
        rw [hsum, hcardR]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        field_simp [hnR]
        have hcancel : ((n : ℝ) ^ m) * ((n : ℝ)⁻¹) ^ m = 1 := by
          rw [← mul_pow]
          simp [hnR]
        rw [pow_succ, div_pow]
        ring_nf
        calc
          (((n - 1 : ℕ) : ℝ) ^ m) * (n : ℝ)
              = (((n - 1 : ℕ) : ℝ) ^ m) * (n : ℝ) * 1 := by ring
          _ = (((n - 1 : ℕ) : ℝ) ^ m) * (n : ℝ) *
                (((n : ℝ) ^ m) * ((n : ℝ)⁻¹) ^ m) := by rw [hcancel]
          _ = (((n - 1 : ℕ) : ℝ) ^ m) * (n : ℝ) * (n : ℝ) ^ m * ((n : ℝ)⁻¹) ^ m := by
                ring
  · exact Integrable.of_finite (f := singleBinIndicator n k i)

theorem singleBinEvent_prob_eq_closedForm (n k : ℕ) (hn : 0 < n) (i : Fin n) :
    (ballMeasure n k).real (singleBinEvent n k i) =
      (k : ℝ) * ((1 : ℝ) / n) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
  rw [← integral_singleBinIndicator_eq_prob n k hn i,
    integral_singleBinIndicator_eq_closedForm n k hn i]

def singleBinClosedForm (n k : ℕ) : ℝ :=
  (k : ℝ) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1))

lemma singleBinClosedForm_step_formula (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    singleBinClosedForm n (k + 1) - singleBinClosedForm n k =
      ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) * (((n : ℝ) - (k + 1 : ℝ)) / n) := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hk1 : k + 1 - 1 = k := by
    omega
  have hk_eq : k = (k - 1) + 1 := by
    omega
  have hk_succ : k - 1 + 1 = k := by
    omega
  set a : ℝ := (((n - 1 : ℕ) : ℝ) / n)
  unfold singleBinClosedForm
  rw [hk1]
  change (↑(k + 1) * a ^ k) - (k : ℝ) * a ^ (k - 1) = a ^ (k - 1) * (((n : ℝ) - (k + 1 : ℝ)) / n)
  have hpow : a ^ k = a ^ (k - 1) * a := by
    simpa [hk_succ] using (pow_succ a (k - 1))
  have hscalar : ((↑(k + 1) : ℝ) * a - k) = (((n : ℝ) - (k + 1 : ℝ)) / n) := by
    dsimp [a]
    field_simp [hnR]
    rw [Nat.cast_sub (Nat.succ_le_of_lt hn)]
    norm_num [Nat.cast_add]
    ring
  rw [hpow]
  calc
    (↑(k + 1) : ℝ) * (a ^ (k - 1) * a) - (k : ℝ) * a ^ (k - 1)
        = a ^ (k - 1) * (((↑(k + 1) : ℝ) * a) - k) := by
            ring
    _ = a ^ (k - 1) * (((n : ℝ) - (k + 1 : ℝ)) / n) := by rw [hscalar]

lemma singleBinClosedForm_step_ge (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    singleBinClosedForm n k ≤ singleBinClosedForm n (k + 1) := by
  have hdiff := singleBinClosedForm_step_formula n k hn hk
  have hbase_nonneg : 0 ≤ ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
    positivity
  have hfactor_nonneg : 0 ≤ (((n : ℝ) - (k + 1 : ℝ)) / n) := by
    have hk1 : (k + 1 : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt hkn
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    exact div_nonneg (sub_nonneg.mpr hk1) hn0
  have hnonneg :
      0 ≤ singleBinClosedForm n (k + 1) - singleBinClosedForm n k := by
    rw [hdiff]
    exact mul_nonneg hbase_nonneg hfactor_nonneg
  linarith

lemma singleBinClosedForm_step_le (n k : ℕ) (hn : 0 < n) (hnk : n ≤ k) :
    singleBinClosedForm n (k + 1) ≤ singleBinClosedForm n k := by
  have hk : 0 < k := by
    omega
  have hdiff := singleBinClosedForm_step_formula n k hn hk
  have hbase_nonneg : 0 ≤ ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
    positivity
  have hfactor_nonpos : (((n : ℝ) - (k + 1 : ℝ)) / n) ≤ 0 := by
    have hk1 : (n : ℝ) - (k + 1 : ℝ) ≤ 0 := by
      have hk1' : (n : ℝ) ≤ (k + 1 : ℝ) := by
        exact_mod_cast (show n ≤ k + 1 by omega)
      linarith
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hk1 hn0
  have hnonpos :
      singleBinClosedForm n (k + 1) - singleBinClosedForm n k ≤ 0 := by
    rw [hdiff]
    exact mul_nonpos_of_nonneg_of_nonpos hbase_nonneg hfactor_nonpos
  linarith

lemma singleBinClosedForm_max_at_n (n j : ℕ) (hn : 0 < n) :
    singleBinClosedForm n j ≤ singleBinClosedForm n n := by
  by_cases hj0 : j = 0
  · subst hj0
    have hnonneg : 0 ≤ (n : ℝ) * ((((n - 1 : ℕ) : ℝ) / n) ^ (n - 1)) := by
      positivity
    simpa [singleBinClosedForm] using hnonneg
  · by_cases hle : j ≤ n
    · have hleft :
          ∀ d t : ℕ, t + d = n → 0 < t → singleBinClosedForm n t ≤ singleBinClosedForm n n := by
        intro d
        induction d with
        | zero =>
            intro t htd ht
            have ht' : t = n := by
              omega
            simpa [ht']
        | succ d ih =>
            intro t htd ht
            have htlt : t < n := by
              omega
            have hstep : singleBinClosedForm n t ≤ singleBinClosedForm n (t + 1) := by
              exact singleBinClosedForm_step_ge n t hn ht htlt
            have hrest : singleBinClosedForm n (t + 1) ≤ singleBinClosedForm n n := by
              apply ih
              · omega
              · omega
            exact le_trans hstep hrest
      exact hleft (n - j) j (by omega) (Nat.pos_of_ne_zero hj0)
    · have hgt : n < j := by
        omega
      let d := j - n
      have hjd : j = n + d := by
        dsimp [d]
        omega
      have hright : ∀ d : ℕ, singleBinClosedForm n (n + d) ≤ singleBinClosedForm n n := by
        intro d
        induction d with
        | zero =>
            simp [singleBinClosedForm]
        | succ d ih =>
            have hstep : singleBinClosedForm n (n + d + 1) ≤ singleBinClosedForm n (n + d) := by
              exact singleBinClosedForm_step_le n (n + d) hn (Nat.le_add_right n d)
            exact le_trans hstep ih
      simpa [hjd] using hright d

theorem integral_singleBinCount_eq_sum (n k : ℕ) (hn : 0 < n) :
    ∫ ω, singleBinCount n k ω ∂ ballMeasure n k =
      ∑ i : Fin n, ∫ ω, singleBinIndicator n k i ω ∂ ballMeasure n k := by
  letI : Nonempty (BallΩ n k) := nonempty_ballΩ_of_pos n k hn
  have hsum :
      ∫ ω, singleBinCount n k ω ∂ (PMF.uniformOfFintype (BallΩ n k)).toMeasure =
        ∑ i : Fin n, ∫ ω, singleBinIndicator n k i ω
          ∂ (PMF.uniformOfFintype (BallΩ n k)).toMeasure := by
    rw [singleBinCount_eq_sum]
    simpa using
      (MeasureTheory.integral_finset_sum
        (s := Finset.univ)
        (f := fun i : Fin n => fun ω => singleBinIndicator n k i ω)
        (μ := (PMF.uniformOfFintype (BallΩ n k)).toMeasure)
        (fun _ _ => Integrable.of_finite))
  simpa [ballMeasure, dif_pos (nonempty_ballΩ_of_pos n k hn)] using hsum

end Ex652Support

theorem ex_6_5_2 (n k : ℕ) (hn : 0 < n) :
    (∀ ω : Ex652Support.BallΩ n k,
      Ex652Support.singleBinCount n k ω =
        ∑ i : Fin n, Ex652Support.singleBinIndicator n k i ω) ∧
    (∫ ω, Ex652Support.singleBinCount n k ω ∂ Ex652Support.ballMeasure n k =
      ∑ i : Fin n,
        ∫ ω, Ex652Support.singleBinIndicator n k i ω ∂ Ex652Support.ballMeasure n k) ∧
    (∀ i : Fin n,
      ∫ ω, Ex652Support.singleBinIndicator n k i ω ∂ Ex652Support.ballMeasure n k =
        (Ex652Support.ballMeasure n k).real (Ex652Support.singleBinEvent n k i)) ∧
    (∀ i : Fin n,
      (Ex652Support.ballMeasure n k).real (Ex652Support.singleBinEvent n k i) =
        (k : ℝ) * ((1 : ℝ) / n) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1))) ∧
    ∫ ω, Ex652Support.singleBinCount n k ω ∂ Ex652Support.ballMeasure n k =
      (k : ℝ) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) ∧
    ∀ j : ℕ,
      Ex652Support.singleBinClosedForm n j ≤ Ex652Support.singleBinClosedForm n n := by
  have hDecomp :
      ∀ ω : Ex652Support.BallΩ n k,
        Ex652Support.singleBinCount n k ω =
          ∑ i : Fin n, Ex652Support.singleBinIndicator n k i ω := by
    intro ω
    rfl
  have hLin :
      ∫ ω, Ex652Support.singleBinCount n k ω ∂ Ex652Support.ballMeasure n k =
        ∑ i : Fin n,
          ∫ ω, Ex652Support.singleBinIndicator n k i ω ∂ Ex652Support.ballMeasure n k := by
    exact Ex652Support.integral_singleBinCount_eq_sum n k hn
  have hIndicator :
      ∀ i : Fin n,
        ∫ ω, Ex652Support.singleBinIndicator n k i ω ∂ Ex652Support.ballMeasure n k =
          (Ex652Support.ballMeasure n k).real (Ex652Support.singleBinEvent n k i) := by
    intro i
    exact Ex652Support.integral_singleBinIndicator_eq_prob n k hn i
  have hProb :
      ∀ i : Fin n,
        (Ex652Support.ballMeasure n k).real (Ex652Support.singleBinEvent n k i) =
          (k : ℝ) * ((1 : ℝ) / n) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
    intro i
    exact Ex652Support.singleBinEvent_prob_eq_closedForm n k hn i
  have hFinal :
      ∫ ω, Ex652Support.singleBinCount n k ω ∂ Ex652Support.ballMeasure n k =
        (k : ℝ) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
    calc
      ∫ ω, Ex652Support.singleBinCount n k ω ∂ Ex652Support.ballMeasure n k
          = ∑ i : Fin n,
              ∫ ω, Ex652Support.singleBinIndicator n k i ω
                ∂ Ex652Support.ballMeasure n k := hLin
      _ = ∑ i : Fin n,
            (k : ℝ) * ((1 : ℝ) / n) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hIndicator i, hProb i]
      _ = (k : ℝ) * ((((n - 1 : ℕ) : ℝ) / n) ^ (k - 1)) := by
            have hnR : (n : ℝ) ≠ 0 := by
              exact_mod_cast hn.ne'
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            simp [Fintype.card_fin]
            field_simp [hnR]
  have hMax :
      ∀ j : ℕ,
        Ex652Support.singleBinClosedForm n j ≤ Ex652Support.singleBinClosedForm n n := by
    intro j
    exact Ex652Support.singleBinClosedForm_max_at_n n j hn
  exact ⟨hDecomp, hLin, hIndicator, hProb, hFinal, hMax⟩
