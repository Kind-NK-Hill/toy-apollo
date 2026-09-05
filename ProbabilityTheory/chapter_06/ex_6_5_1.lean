/-
TASK ID: ex_6_5_1
TYPE: Example_Proof
SOURCE PLAN: 23_chap6_application_hat_ball_bin
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Finset BigOperators

noncomputable section




namespace Ex651Support

abbrev HatΩ (n : ℕ) := Equiv.Perm (Fin n)

instance instMeasurableSpaceHatΩ (n : ℕ) : MeasurableSpace (HatΩ n) := ⊤

noncomputable def hatMeasure (n : ℕ) : Measure (HatΩ n) :=
  (PMF.uniformOfFintype (HatΩ n)).toMeasure

instance instIsProbabilityMeasureHatMeasure (n : ℕ) : IsProbabilityMeasure (hatMeasure n) := by
  dsimp [hatMeasure]
  infer_instance

def ownHatEvent (n : ℕ) (i : Fin n) : Set (HatΩ n) :=
  {σ | σ i = i}

def ownHatIndicator (n : ℕ) (i : Fin n) : HatΩ n → ℝ :=
  fun σ => if σ i = i then 1 else 0

def ownHatCount (n : ℕ) : HatΩ n → ℝ :=
  fun σ => ∑ i : Fin n, ownHatIndicator n i σ

theorem measurableSet_ownHatEvent (n : ℕ) (i : Fin n) :
    MeasurableSet (ownHatEvent n i) := by
  simp [ownHatEvent]

theorem ownHatIndicator_eq_indicator (n : ℕ) (i : Fin n) :
    ownHatIndicator n i = Set.indicator (ownHatEvent n i) (fun _ : HatΩ n => (1 : ℝ)) := by
  funext σ
  by_cases hσ : σ i = i
  · simp [ownHatIndicator, ownHatEvent, Set.indicator, hσ]
  · simp [ownHatIndicator, ownHatEvent, Set.indicator, hσ]

theorem ownHatCount_eq_sum (n : ℕ) :
    ownHatCount n = fun σ => ∑ i : Fin n, ownHatIndicator n i σ := by
  rfl

lemma card_perm_fixing_one (n : ℕ) (i : Fin n) :
    Fintype.card {σ : HatΩ n | σ i = i} = (n - 1).factorial := by
  rcases n with (_ | n) <;> simp_all +decide [Nat.factorial]
  · fin_cases i
  · rw [Fintype.card_subtype]
    have h_count :
        Finset.card (Finset.filter (fun σ : HatΩ (n + 1) => σ i = i) Finset.univ) =
          Finset.card
            (Finset.image (fun σ : Equiv.Perm {x // x ≠ i} => Equiv.Perm.ofSubtype σ)
              Finset.univ) := by
      congr with σ
      simp +decide [Equiv.Perm.ofSubtype]
      constructor
      · intro hi
        use Equiv.Perm.subtypePerm σ
          (by
            intro x
            refine ⟨?_, ?_⟩
            · intro hx
              rintro rfl
              exact hx hi
            · intro hx
              intro hx'
              exact hx <| σ.injective <| hx'.trans hi.symm)
        ext x
        by_cases hx : x = i <;> simp_all +decide [Equiv.Perm.extendDomain]
      · rintro ⟨a, rfl⟩
        simp +decide [Equiv.Perm.extendDomain]
    rw [h_count, Finset.card_image_of_injective]
    · simp +decide [Finset.card_univ, Fintype.card_perm]
    · exact Equiv.Perm.ofSubtype_injective

lemma sum_ownHatIndicator (n : ℕ) (i : Fin n) :
    (∑ σ : HatΩ n, ownHatIndicator n i σ) = ((n - 1).factorial : ℝ) := by
  convert card_perm_fixing_one n i using 1
  rw [Fintype.card_subtype]
  simp [ownHatIndicator]

theorem integral_ownHatIndicator_eq_prob (n : ℕ) (i : Fin n) :
    ∫ ω, ownHatIndicator n i ω ∂ hatMeasure n =
      (hatMeasure n).real (ownHatEvent n i) := by
  rw [ownHatIndicator_eq_indicator]
  simpa using
    (MeasureTheory.integral_indicator_one
      (μ := hatMeasure n) (s := ownHatEvent n i) (hs := measurableSet_ownHatEvent n i))

theorem integral_ownHatIndicator_eq_one_div_n (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ∫ ω, ownHatIndicator n i ω ∂ hatMeasure n = (1 : ℝ) / n := by
  rw [hatMeasure]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  erw [MeasureTheory.integral_fintype]
  · cases n with
    | zero =>
        cases Nat.lt_irrefl 0 hn
    | succ m =>
        have hcard :
            Fintype.card {σ : HatΩ (m + 1) | σ i = i} = m.factorial := by
          simpa using card_perm_fixing_one (m + 1) i
        have hcardR :
            (Fintype.card {σ : HatΩ (m + 1) | σ i = i} : ℝ) = (m.factorial : ℝ) := by
          exact_mod_cast hcard
        simp [ownHatIndicator, PMF.uniformOfFintype_apply, MeasureTheory.measureReal_def,
          Fintype.card_perm]
        have hsum :
            (∑ x : HatΩ (m + 1), if x i = i then (((m + 1).factorial : ℝ)⁻¹) else 0) =
              (Fintype.card {σ : HatΩ (m + 1) | σ i = i} : ℝ) * (((m + 1).factorial : ℝ)⁻¹) := by
          have hcard_filter :
              (Finset.filter (fun a : HatΩ (m + 1) => a i = i) Finset.univ).card =
                Fintype.card {σ : HatΩ (m + 1) | σ i = i} := by
            rw [Fintype.card_subtype]
            congr with x
          rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [hcard_filter]
        rw [hsum, hcardR]
        rw [show (((m + 1).factorial : ℕ) : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) by
          norm_num [Nat.factorial_succ, Nat.cast_mul]]
        field_simp
  · exact Integrable.of_finite (f := ownHatIndicator n i)

theorem ownHatEvent_prob_eq_one_div_n (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (hatMeasure n).real (ownHatEvent n i) = (1 : ℝ) / n := by
  rw [← integral_ownHatIndicator_eq_prob n i, integral_ownHatIndicator_eq_one_div_n n hn i]

theorem integral_ownHatCount_eq_sum (n : ℕ) :
    ∫ ω, ownHatCount n ω ∂ hatMeasure n =
      ∑ i : Fin n, ∫ ω, ownHatIndicator n i ω ∂ hatMeasure n := by
  rw [ownHatCount_eq_sum]
  simpa using
    (MeasureTheory.integral_finset_sum
      (s := Finset.univ)
      (f := fun i : Fin n => fun ω => ownHatIndicator n i ω)
      (μ := hatMeasure n)
      (fun _ _ => Integrable.of_finite))

end Ex651Support

theorem ex_6_5_1 (n : ℕ) (hn : 0 < n) :
    (∀ ω : Ex651Support.HatΩ n,
      Ex651Support.ownHatCount n ω =
        ∑ i : Fin n, Ex651Support.ownHatIndicator n i ω) ∧
    (∫ ω, Ex651Support.ownHatCount n ω ∂ Ex651Support.hatMeasure n =
      ∑ i : Fin n, ∫ ω, Ex651Support.ownHatIndicator n i ω ∂ Ex651Support.hatMeasure n) ∧
    (∀ i : Fin n,
      ∫ ω, Ex651Support.ownHatIndicator n i ω ∂ Ex651Support.hatMeasure n =
        (Ex651Support.hatMeasure n).real (Ex651Support.ownHatEvent n i)) ∧
    (∀ i : Fin n,
      (Ex651Support.hatMeasure n).real (Ex651Support.ownHatEvent n i) = (1 : ℝ) / n) ∧
    ∫ ω, Ex651Support.ownHatCount n ω ∂ Ex651Support.hatMeasure n = 1 := by
  have hDecomp :
      ∀ ω : Ex651Support.HatΩ n,
        Ex651Support.ownHatCount n ω =
          ∑ i : Fin n, Ex651Support.ownHatIndicator n i ω := by
    intro ω
    rfl
  have hLin :
      ∫ ω, Ex651Support.ownHatCount n ω ∂ Ex651Support.hatMeasure n =
        ∑ i : Fin n, ∫ ω, Ex651Support.ownHatIndicator n i ω ∂ Ex651Support.hatMeasure n := by
    exact Ex651Support.integral_ownHatCount_eq_sum n
  have hIndicator :
      ∀ i : Fin n,
        ∫ ω, Ex651Support.ownHatIndicator n i ω ∂ Ex651Support.hatMeasure n =
          (Ex651Support.hatMeasure n).real (Ex651Support.ownHatEvent n i) := by
    intro i
    exact Ex651Support.integral_ownHatIndicator_eq_prob n i
  have hProb :
      ∀ i : Fin n,
        (Ex651Support.hatMeasure n).real (Ex651Support.ownHatEvent n i) = (1 : ℝ) / n := by
    intro i
    exact Ex651Support.ownHatEvent_prob_eq_one_div_n n hn i
  have hFinal :
      ∫ ω, Ex651Support.ownHatCount n ω ∂ Ex651Support.hatMeasure n = 1 := by
    calc
      ∫ ω, Ex651Support.ownHatCount n ω ∂ Ex651Support.hatMeasure n
          = ∑ i : Fin n, ∫ ω, Ex651Support.ownHatIndicator n i ω ∂ Ex651Support.hatMeasure n := hLin
      _ = ∑ i : Fin n, (1 : ℝ) / n := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hIndicator i, hProb i]
      _ = 1 := by
            have hnR : (n : ℝ) ≠ 0 := by
              exact_mod_cast hn.ne'
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            simp [Fintype.card_fin, hnR]
  exact ⟨hDecomp, hLin, hIndicator, hProb, hFinal⟩
