/-
TASK ID: ex_13_6_1
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_8




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

 
def ex_13_6_1_history {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    Ω → Fin n → ℝ :=
  fun ω k => Y (k.1 + 1) ω



@[reducible]
def ex_13_6_1_naturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | n + 1 =>
      (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
        (ex_13_6_1_history Y (n + 1))

theorem ex_13_6_1_naturalFiltration_zero {Ω : Type*}
    (Y : ℕ → Ω → ℝ) :
    ex_13_6_1_naturalFiltration Y 0 = ⊥ :=
  rfl

theorem ex_13_6_1_naturalFiltration_succ {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    ex_13_6_1_naturalFiltration Y (n + 1) =
      (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
        (ex_13_6_1_history Y (n + 1)) :=
  rfl

 
def ex_13_6_1_historyProjection {n m : ℕ} (h : n ≤ m) :
    (Fin m → ℝ) → (Fin n → ℝ) :=
  fun v k => v (Fin.castLE h k)

theorem ex_13_6_1_historyProjection_measurable {n m : ℕ} (h : n ≤ m) :
    Measurable (ex_13_6_1_historyProjection h) := by
  exact measurable_pi_lambda _ fun k => measurable_pi_apply (Fin.castLE h k)

theorem ex_13_6_1_historyProjection_comp {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    ex_13_6_1_history Y n =
      ex_13_6_1_historyProjection h ∘ ex_13_6_1_history Y m := by
  funext ω k
  simp [ex_13_6_1_history, ex_13_6_1_historyProjection]

theorem ex_13_6_1_history_measurable_self {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    @Measurable Ω (Fin n → ℝ) (ex_13_6_1_naturalFiltration Y n)
      _ (ex_13_6_1_history Y n) := by
  cases n with
  | zero =>
      have hconst :
          ex_13_6_1_history Y 0 =
            fun _ : Ω => (fun k : Fin 0 => Fin.elim0 k) := by
        funext ω k
        exact Fin.elim0 k
      rw [hconst]
      exact measurable_const
  | succ n =>
      exact Measurable.of_comap_le le_rfl

theorem ex_13_6_1_history_measurable_of_le {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    @Measurable Ω (Fin n → ℝ) (ex_13_6_1_naturalFiltration Y m)
      _ (ex_13_6_1_history Y n) := by
  have hself := ex_13_6_1_history_measurable_self Y m
  have hproj := ex_13_6_1_historyProjection_measurable h
  have hcomp : @Measurable Ω (Fin n → ℝ) (ex_13_6_1_naturalFiltration Y m)
      _ (ex_13_6_1_historyProjection h ∘ ex_13_6_1_history Y m) :=
    hproj.comp hself
  simpa [ex_13_6_1_historyProjection_comp Y h] using hcomp



theorem ex_13_6_1_naturalFiltration_mono {Ω : Type*}
    (Y : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) :
    ex_13_6_1_naturalFiltration Y n ≤ ex_13_6_1_naturalFiltration Y m := by
  cases n with
  | zero =>
      exact bot_le
  | succ n =>
      exact (ex_13_6_1_history_measurable_of_le Y h).comap_le



theorem ex_13_6_1_naturalFiltration_sub_ambient {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y (n + 1))) (n : ℕ) :
    ex_13_6_1_naturalFiltration Y n ≤ 𝓕 := by
  cases n with
  | zero =>
      exact bot_le
  | succ n =>
      have hhist : @Measurable Ω (Fin (n + 1) → ℝ) 𝓕 _
          (ex_13_6_1_history Y (n + 1)) := by
        exact measurable_pi_lambda _ fun k => hY k.1
      exact hhist.comap_le



theorem ex_13_6_1_naturalFiltration_isFiltration {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y (n + 1))) :
    def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_1_naturalFiltration Y) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact ex_13_6_1_naturalFiltration_sub_ambient Y hY n
  · intro n m hnm
    exact ex_13_6_1_naturalFiltration_mono Y hnm



def ex_13_6_1_historyTransform {Ω S : Type*}
    (Y : ℕ → Ω → ℝ) (f : (n : ℕ) → (Fin n → ℝ) → S) :
    ℕ → Ω → S :=
  fun n ω => f n (ex_13_6_1_history Y n ω)



theorem ex_13_6_1_historyTransform_adapted {Ω S : Type*}
    [MeasurableSpace S] (Y : ℕ → Ω → ℝ)
    (f : (n : ℕ) → (Fin n → ℝ) → S)
    (hf : ∀ n : ℕ, Measurable (f n)) :
    def_13_6_adapted (ex_13_6_1_naturalFiltration Y)
      (ex_13_6_1_historyTransform Y f) := by
  intro n
  exact (hf n).comp (ex_13_6_1_history_measurable_self Y n)



def ex_13_6_1 {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    (Y : ℕ → Ω → ℝ)
    (f : (n : ℕ) → (Fin n → ℝ) → S) : Prop :=
  (∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y (n + 1))) →
    (∀ n : ℕ, Measurable (f n)) →
      def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_1_naturalFiltration Y) ∧
        def_13_6_adapted (ex_13_6_1_naturalFiltration Y)
          (ex_13_6_1_historyTransform Y f)

theorem ex_13_6_1_holds {Ω S : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S]
    (Y : ℕ → Ω → ℝ)
    (f : (n : ℕ) → (Fin n → ℝ) → S) :
    ex_13_6_1 Y f := by
  intro hY hf
  exact ⟨ex_13_6_1_naturalFiltration_isFiltration Y hY,
    ex_13_6_1_historyTransform_adapted Y f hf⟩



def ex_13_6_1_source_package {Ω S : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S] (Y : ℕ → Ω → ℝ)
    (f : (n : ℕ) → (Fin n → ℝ) → S) : Prop :=
  ex_13_6_1 Y f

theorem ex_13_6_1_source_package_holds {Ω S : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S] (Y : ℕ → Ω → ℝ)
    (f : (n : ℕ) → (Fin n → ℝ) → S) :
    ex_13_6_1_source_package Y f := by
  change ex_13_6_1 Y f
  exact ex_13_6_1_holds Y f
