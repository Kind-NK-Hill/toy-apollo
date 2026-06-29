import Mathlib
import ToyApollo.Output.def_13_4

/-
TASK ID: prob_13_5
TYPE: Problem
SOURCE PLAN: chapter13-problems
TASK CONTENT:
\textbf{13.5.} (a) Suppose X and Y are iid. random variables with finite mean. Prove that

E[X\vertX + Y]= (X + Y)/ 2. (Hint: Show that E [Y\vertX + Y]= E[X\vertX +Y ] .)

(b) Extend the result in part (a) to n iid. random variables.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section

/-- Independent identically distributed variables give exchangeability of the
ordered pair. -/
lemma prob_13_5_pair_swap_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hXY : IdentDistrib X Y P P) (hInd : X ⟂ᵢ[P] Y) :
    IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) P P := by
  exact IdentDistrib.prodMk hXY hXY.symm hInd hInd.symm

/-- Source hint bridge: over every `sigma(X+Y)`-measurable set, iid
exchangeability gives equal integrals of `X` and `Y`. -/
lemma prob_13_5_pair_setIntegral_eq {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hSwap : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) P P)
    {B : Set Ω} (hB : MeasurableSet[def_13_4_sigma (fun ω => X ω + Y ω)] B) :
    ∫ ω in B, X ω ∂P = ∫ ω in B, Y ω ∂P := by
  rcases (MeasurableSpace.measurableSet_comap.mp hB) with ⟨A, hA, hBA⟩
  let S : Set (ℝ × ℝ) := {p | p.1 + p.2 ∈ A}
  let F : ℝ × ℝ → ℝ := S.indicator (fun p => p.1)
  have hS : MeasurableSet S := hA.preimage (measurable_fst.add measurable_snd)
  have hF : Measurable F := measurable_fst.indicator hS
  have hBF : MeasurableSet B :=
    (def_13_4_sigma_subSigma_of_measurable (hXm.add hYm)) hB
  have hFX : (fun ω => F (X ω, Y ω)) = B.indicator X := by
    funext ω
    rw [← hBA]
    by_cases hω : X ω + Y ω ∈ A <;> simp [F, S, hω]
  have hFY : (fun ω => F (Y ω, X ω)) = B.indicator Y := by
    funext ω
    rw [← hBA]
    by_cases hω : X ω + Y ω ∈ A
    · have hω' : Y ω + X ω ∈ A := by simpa [add_comm] using hω
      simp [F, S, hω, hω']
    · have hω' : Y ω + X ω ∉ A := by simpa [add_comm] using hω
      simp [F, S, hω, hω']
  calc
    ∫ ω in B, X ω ∂P = ∫ ω, B.indicator X ω ∂P := by
      exact (integral_indicator hBF).symm
    _ = ∫ ω, F (X ω, Y ω) ∂P := by rw [hFX]
    _ = ∫ ω, F (Y ω, X ω) ∂P := by
      exact (hSwap.comp hF).integral_eq
    _ = ∫ ω, B.indicator Y ω ∂P := by rw [hFY]
    _ = ∫ ω in B, Y ω ∂P := by
      exact integral_indicator hBF

/-- Two-variable source conclusion: conditioning on the observed sum gives
half of that sum. -/
theorem prob_13_5_pair_condExp_eq_half_sum {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hSwap : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) P P) :
    P[X | def_13_4_sigma (fun ω => X ω + Y ω)] =ᵐ[P]
      fun ω => (X ω + Y ω) / 2 := by
  have hG : IsSubSigmaField (def_13_4_sigma (fun ω => X ω + Y ω)) 𝓕 :=
    def_13_4_sigma_subSigma_of_measurable (hXm.add hYm)
  haveI : SigmaFinite (P.trim hG) := inferInstance
  let Z : Ω → ℝ := fun ω => (X ω + Y ω) / 2
  have hZint : Integrable Z P := (hX.add hY).div_const 2
  have hZmeas :
      AEStronglyMeasurable[def_13_4_sigma (fun ω => X ω + Y ω)] Z P := by
    have hS :
        Measurable[def_13_4_sigma (fun ω => X ω + Y ω)]
          (fun ω => X ω + Y ω) :=
      comap_measurable _
    exact (hS.div_const 2).aestronglyMeasurable
  have hSetInt :
      ∀ ⦃B : Set Ω⦄,
        MeasurableSet[def_13_4_sigma (fun ω => X ω + Y ω)] B →
          P B < ∞ → IntegrableOn Z B P := by
    intro B _hB _hBfin
    exact hZint.integrableOn
  have hIntegral :
      ∀ ⦃B : Set Ω⦄,
        MeasurableSet[def_13_4_sigma (fun ω => X ω + Y ω)] B →
          P B < ∞ →
          ∫ ω in B, Z ω ∂P = ∫ ω in B, X ω ∂P := by
    intro B hB _hBfin
    have hXY : ∫ ω in B, X ω ∂P = ∫ ω in B, Y ω ∂P :=
      prob_13_5_pair_setIntegral_eq hXm hYm hSwap hB
    have hsum :
        ∫ ω in B, (fun ω => X ω + Y ω) ω ∂P =
          ∫ ω in B, X ω ∂P + ∫ ω in B, Y ω ∂P := by
      exact integral_add hX.integrableOn hY.integrableOn
    calc
      ∫ ω in B, Z ω ∂P
          = (∫ ω in B, (fun ω => X ω + Y ω) ω ∂P) / 2 := by
            simp [Z, integral_div]
      _ = (∫ ω in B, X ω ∂P + ∫ ω in B, Y ω ∂P) / 2 := by
            rw [hsum]
      _ = ∫ ω in B, X ω ∂P := by
            rw [hXY]
            ring
  exact (ae_eq_condExp_of_forall_setIntegral_eq hG hX hSetInt hIntegral hZmeas).symm

/-- Two-variable iid formulation of Problem 13.5(a). -/
theorem prob_13_5_pair_from_iid {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hXY : IdentDistrib X Y P P) (hInd : X ⟂ᵢ[P] Y) :
    P[X | def_13_4_sigma (fun ω => X ω + Y ω)] =ᵐ[P]
      fun ω => (X ω + Y ω) / 2 :=
  prob_13_5_pair_condExp_eq_half_sum hX hY hXm hYm
    (prob_13_5_pair_swap_identDistrib hXY hInd)

/-- Iid finite families are invariant in law under finite index permutations. -/
lemma prob_13_5_vector_perm_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hSame : ∀ i j : Fin n, IdentDistrib (X i) (X j) P P)
    (hInd : iIndepFun X P) (σ : Equiv.Perm (Fin n)) :
    IdentDistrib (fun ω => fun i => X i ω)
      (fun ω => fun i => X (σ i) ω) P P := by
  exact IdentDistrib.pi (fun i => hSame i (σ i)) hInd (hInd.precomp σ.injective)

/-- For an iid finite family, every two coordinates have equal integrals over
sets measurable with respect to the total sum. -/
lemma prob_13_5_n_setIntegral_coord_eq {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hSame : ∀ i j : Fin n, IdentDistrib (X i) (X j) P P)
    (hInd : iIndepFun X P) {i j : Fin n}
    {B : Set Ω}
    (hB : MeasurableSet[def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)] B) :
    ∫ ω in B, X i ω ∂P = ∫ ω in B, X j ω ∂P := by
  classical
  rcases (MeasurableSpace.measurableSet_comap.mp hB) with ⟨A, hA, hBA⟩
  let S : Set (Fin n → ℝ) := {v | (∑ k : Fin n, v k) ∈ A}
  let F : (Fin n → ℝ) → ℝ := S.indicator (fun v => v i)
  have hS : MeasurableSet S := by
    exact hA.preimage
      (Finset.measurable_sum Finset.univ
        (fun k _hk => measurable_pi_apply k))
  have hF : Measurable F := (measurable_pi_apply i).indicator hS
  have hTotalMeas : Measurable (fun ω => ∑ k : Fin n, X k ω) :=
    Finset.measurable_sum Finset.univ (fun k _hk => hXm k)
  have hBF : MeasurableSet B :=
    (def_13_4_sigma_subSigma_of_measurable hTotalMeas) hB
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hPerm :
      IdentDistrib (fun ω => fun k => X k ω)
        (fun ω => fun k => X (σ k) ω) P P :=
    prob_13_5_vector_perm_identDistrib hSame hInd σ
  have hFX : (fun ω => F (fun k => X k ω)) = B.indicator (X i) := by
    funext ω
    rw [← hBA]
    by_cases hω : (∑ k : Fin n, X k ω) ∈ A <;> simp [F, S, hω]
  have hFY : (fun ω => F (fun k => X (σ k) ω)) = B.indicator (X j) := by
    funext ω
    rw [← hBA]
    have hsum :
        (∑ k : Fin n, X (σ k) ω) = ∑ k : Fin n, X k ω :=
      Equiv.sum_comp σ (fun k => X k ω)
    by_cases hω : (∑ k : Fin n, X k ω) ∈ A
    · have hω' : (∑ k : Fin n, X (σ k) ω) ∈ A := by
        simpa [hsum] using hω
      have hσi : σ i = j := Equiv.swap_apply_left i j
      simp [F, S, hω, hω', hσi]
    · have hω' : (∑ k : Fin n, X (σ k) ω) ∉ A := by
        simpa [hsum] using hω
      simp [F, S, hω, hω']
  calc
    ∫ ω in B, X i ω ∂P = ∫ ω, B.indicator (X i) ω ∂P := by
      exact (integral_indicator hBF).symm
    _ = ∫ ω, F (fun k => X k ω) ∂P := by rw [hFX]
    _ = ∫ ω, F (fun k => X (σ k) ω) ∂P := by
      exact (hPerm.comp hF).integral_eq
    _ = ∫ ω, B.indicator (X j) ω ∂P := by rw [hFY]
    _ = ∫ ω in B, X j ω ∂P := by
      exact integral_indicator hBF

/-- Problem 13.5(b): for an iid finite family, each coordinate conditioned on
the total sum is the average total. -/
theorem prob_13_5_n_condExp_eq_average {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {n : ℕ} (hn : n ≠ 0)
    {X : Fin n → Ω → ℝ}
    (hInt : ∀ i : Fin n, Integrable (X i) P)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hSame : ∀ i j : Fin n, IdentDistrib (X i) (X j) P P)
    (hInd : iIndepFun X P) (i : Fin n) :
    P[X i | def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)] =ᵐ[P]
      fun ω => (∑ k : Fin n, X k ω) / (n : ℝ) := by
  classical
  have hTotalMeas : Measurable (fun ω => ∑ k : Fin n, X k ω) :=
    Finset.measurable_sum Finset.univ (fun k _hk => hXm k)
  have hG :
      IsSubSigmaField
        (def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)) 𝓕 :=
    def_13_4_sigma_subSigma_of_measurable hTotalMeas
  haveI : SigmaFinite (P.trim hG) := inferInstance
  let Z : Ω → ℝ := fun ω => (∑ k : Fin n, X k ω) / (n : ℝ)
  have hTotalInt : Integrable (fun ω => ∑ k : Fin n, X k ω) P :=
    integrable_finset_sum Finset.univ (fun k _hk => hInt k)
  have hZint : Integrable Z P := hTotalInt.div_const (n : ℝ)
  have hZmeas :
      AEStronglyMeasurable[def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)]
        Z P := by
    have hS :
        Measurable[def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)]
          (fun ω => ∑ k : Fin n, X k ω) :=
      comap_measurable _
    exact (hS.div_const (n : ℝ)).aestronglyMeasurable
  have hSetInt :
      ∀ ⦃B : Set Ω⦄,
        MeasurableSet[def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)] B →
          P B < ∞ → IntegrableOn Z B P := by
    intro B _hB _hBfin
    exact hZint.integrableOn
  have hIntegral :
      ∀ ⦃B : Set Ω⦄,
        MeasurableSet[def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)] B →
          P B < ∞ →
          ∫ ω in B, Z ω ∂P = ∫ ω in B, X i ω ∂P := by
    intro B hB _hBfin
    have hsum :
        ∫ ω in B, (fun ω => ∑ k : Fin n, X k ω) ω ∂P =
          ∑ k : Fin n, ∫ ω in B, X k ω ∂P := by
      exact integral_finset_sum Finset.univ
        (fun k _hk => (hInt k).integrableOn)
    have hcoords :
        (∑ k : Fin n, ∫ ω in B, X k ω ∂P) =
          (n : ℝ) * ∫ ω in B, X i ω ∂P := by
      calc
        (∑ k : Fin n, ∫ ω in B, X k ω ∂P)
            = ∑ _k : Fin n, ∫ ω in B, X i ω ∂P := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              exact prob_13_5_n_setIntegral_coord_eq hXm hSame hInd hB
        _ = (n : ℝ) * ∫ ω in B, X i ω ∂P := by
              simp
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      ∫ ω in B, Z ω ∂P
          = (∫ ω in B, (fun ω => ∑ k : Fin n, X k ω) ω ∂P) / (n : ℝ) := by
            simp [Z, integral_div]
      _ = (∑ k : Fin n, ∫ ω in B, X k ω ∂P) / (n : ℝ) := by
            rw [hsum]
      _ = ((n : ℝ) * ∫ ω in B, X i ω ∂P) / (n : ℝ) := by
            rw [hcoords]
      _ = ∫ ω in B, X i ω ∂P := by
            field_simp [hnR]
  exact (ae_eq_condExp_of_forall_setIntegral_eq hG (hInt i) hSetInt hIntegral hZmeas).symm

/-- Problem 13.5: iid finite-mean variables have conditional expectation equal
to their share of the observed total sum, first for two variables and then for
a finite family. -/
theorem prob_13_5 :
    (∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [IsFiniteMeasure P] {X Y : Ω → ℝ},
      Integrable X P → Integrable Y P →
      Measurable X → Measurable Y →
      IdentDistrib X Y P P → X ⟂ᵢ[P] Y →
      P[X | def_13_4_sigma (fun ω => X ω + Y ω)] =ᵐ[P]
        fun ω => (X ω + Y ω) / 2) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [IsFiniteMeasure P] {n : ℕ}, n ≠ 0 →
      ∀ {X : Fin n → Ω → ℝ},
      (∀ i : Fin n, Integrable (X i) P) →
      (∀ i : Fin n, Measurable (X i)) →
      (∀ i j : Fin n, IdentDistrib (X i) (X j) P P) →
      iIndepFun X P → ∀ i : Fin n,
      P[X i | def_13_4_sigma (fun ω => ∑ k : Fin n, X k ω)] =ᵐ[P]
        fun ω => (∑ k : Fin n, X k ω) / (n : ℝ)) := by
  constructor
  · intro Ω 𝓕 P _ X Y hX hY hXm hYm hXY hInd
    exact prob_13_5_pair_from_iid hX hY hXm hYm hXY hInd
  · intro Ω 𝓕 P _ n hn X hInt hXm hSame hInd i
    exact prob_13_5_n_condExp_eq_average hn hInt hXm hSame hInd i
