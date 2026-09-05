/-
TASK ID: chapter13_stopping_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_6

open MeasureTheory
open scoped BigOperators

noncomputable section






def chapter13_stoppedNatSum {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range (τ ω), X (k + 1) ω

@[simp]
theorem chapter13_stoppedNatSum_zero {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) {ω : Ω}
    (hτ : τ ω = 0) :
    chapter13_stoppedNatSum X τ ω = 0 := by
  simp [chapter13_stoppedNatSum, hτ]

theorem chapter13_stoppedNatSum_succ {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) {ω : Ω} {n : ℕ}
    (hτ : τ ω = n + 1) :
    chapter13_stoppedNatSum X τ ω =
      chapter13_stoppedNatSum X (fun _ => n) ω + X (n + 1) ω := by
  simp [chapter13_stoppedNatSum, hτ, Finset.sum_range_succ]

 
theorem chapter13_stoppedSum_centered_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (μ : ℝ) (ω : Ω) :
    chapter13_stoppedNatSum (fun n ω => X n ω - μ) τ ω =
      chapter13_stoppedNatSum X τ ω - μ * (τ ω : ℝ) := by
  simp [chapter13_stoppedNatSum, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_comm]

 
theorem chapter13_stoppedNatSum_eq_sum_indicator_range {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ) {ω : Ω}
    (hτN : τ ω ≤ N) :
    chapter13_stoppedNatSum X τ ω =
      ∑ k ∈ Finset.range N,
        if k < τ ω then X (k + 1) ω else (0 : ℝ) := by
  classical
  rw [chapter13_stoppedNatSum]
  symm
  calc
    (∑ k ∈ Finset.range N,
        if k < τ ω then X (k + 1) ω else (0 : ℝ))
        = ∑ k ∈ Finset.range (τ ω),
            if k < τ ω then X (k + 1) ω else (0 : ℝ) := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro k hk
            exact Finset.mem_range.mpr
              ((Finset.mem_range.mp hk).trans_le hτN)
          · intro k hkN hkτ
            have hk_not_lt : ¬ k < τ ω := by
              exact fun hk => hkτ (Finset.mem_range.mpr hk)
            simp [hk_not_lt]
    _ = ∑ k ∈ Finset.range (τ ω), X (k + 1) ω := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [Finset.mem_range.mp hk]
    _ = ∑ k ∈ Finset.range (τ ω), X (k + 1) ω := rfl

 
def chapter13_oneIndexedHistory {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (n : ℕ) : Ω → Fin n → ℝ :=
  fun ω k => Y (k.1 + 1) ω



@[reducible]
def chapter13_oneIndexedNaturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | n + 1 =>
      (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
        (chapter13_oneIndexedHistory Y (n + 1))

def chapter13_historyProjection {n m : ℕ} (h : n ≤ m) :
    (Fin m → ℝ) → (Fin n → ℝ) :=
  fun v k => v (Fin.castLE h k)

theorem chapter13_historyProjection_measurable {n m : ℕ} (h : n ≤ m) :
    Measurable (chapter13_historyProjection h) := by
  exact measurable_pi_lambda _ fun k => measurable_pi_apply (Fin.castLE h k)

theorem chapter13_historyProjection_comp {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    chapter13_oneIndexedHistory Y n =
      chapter13_historyProjection h ∘
        chapter13_oneIndexedHistory Y m := by
  funext ω k
  simp [chapter13_oneIndexedHistory, chapter13_historyProjection]

theorem chapter13_history_measurable_self {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    @Measurable Ω (Fin n → ℝ)
      (chapter13_oneIndexedNaturalFiltration Y n) _
      (chapter13_oneIndexedHistory Y n) := by
  cases n with
  | zero =>
      have hconst :
          chapter13_oneIndexedHistory Y 0 =
            fun _ : Ω => (default : Fin 0 → ℝ) := by
        funext ω k
        exact Fin.elim0 k
      rw [hconst]
      exact measurable_const
  | succ n =>
      exact Measurable.of_comap_le le_rfl

theorem chapter13_history_measurable_of_le {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    @Measurable Ω (Fin n → ℝ)
      (chapter13_oneIndexedNaturalFiltration Y m) _
      (chapter13_oneIndexedHistory Y n) := by
  have hself := chapter13_history_measurable_self Y m
  have hproj := chapter13_historyProjection_measurable h
  have hcomp :
      @Measurable Ω (Fin n → ℝ)
        (chapter13_oneIndexedNaturalFiltration Y m) _
        (chapter13_historyProjection h ∘
          chapter13_oneIndexedHistory Y m) :=
    hproj.comp hself
  simpa [chapter13_historyProjection_comp Y h] using hcomp

theorem chapter13_oneIndexedNaturalFiltration_mono {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    chapter13_oneIndexedNaturalFiltration Y n ≤
      chapter13_oneIndexedNaturalFiltration Y m := by
  cases n with
  | zero =>
      exact bot_le
  | succ n =>
      exact (chapter13_history_measurable_of_le Y h).comap_le

theorem chapter13_oneIndexedNaturalFiltration_sub_ambient {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y n)) (n : ℕ) :
    chapter13_oneIndexedNaturalFiltration Y n ≤ 𝓕 := by
  cases n with
  | zero =>
      exact bot_le
  | succ n =>
      have hhist :
          @Measurable Ω (Fin (n + 1) → ℝ) 𝓕 _
            (chapter13_oneIndexedHistory Y (n + 1)) := by
        exact measurable_pi_lambda _ fun k => hY (k.1 + 1)
      exact hhist.comap_le

theorem chapter13_oneIndexedNaturalFiltration_isFiltration {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y n)) :
    def_13_6_isFiltration (𝓕 := 𝓕)
      (chapter13_oneIndexedNaturalFiltration Y) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact chapter13_oneIndexedNaturalFiltration_sub_ambient Y hY n
  · intro n m hnm
    exact chapter13_oneIndexedNaturalFiltration_mono Y hnm
