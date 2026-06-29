/-
TASK ID: prob_14_8
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_14_3
import ToyApollo.Output.thm_14_1
import ToyApollo.Output.thm_14_5

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Uniformity

noncomputable section

theorem prob_14_8_tendsto_of_subseq_subseq_tendsto
    {α : Type*} [TopologicalSpace α] {F : ℕ → α} {g : α}
    (h :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto (fun n : ℕ => F (φ (ψ n))) atTop (𝓝 g)) :
    Tendsto F atTop (𝓝 g) := by
  refine Filter.tendsto_of_subseq_tendsto
    (x := F) (f := 𝓝 g) (l := atTop) ?_
  intro ns hns
  obtain ⟨φ, _hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, _hψ, hconv⟩ := h (ns ∘ φ) hnsφ
  exact ⟨φ ∘ ψ, by simpa [Function.comp_apply, Function.comp_assoc] using hconv⟩

theorem prob_14_8_tendsto_filter_of_subseq_subseq_tendsto
    {α : Type*} {F : ℕ → α} {L : Filter α}
    (h :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto (fun n : ℕ => F (φ (ψ n))) atTop L) :
    Tendsto F atTop L := by
  refine Filter.tendsto_of_subseq_tendsto
    (x := F) (f := L) (l := atTop) ?_
  intro ns hns
  obtain ⟨φ, _hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, _hψ, hconv⟩ := h (ns ∘ φ) hnsφ
  exact ⟨φ ∘ ψ, by simpa [Function.comp_apply, Function.comp_assoc] using hconv⟩

theorem prob_14_8_eventually_of_subseq_subseq_eventually
    {P : ℕ → Prop}
    (h :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ᶠ n : ℕ in atTop, P (φ (ψ n))) :
    ∀ᶠ n : ℕ in atTop, P n := by
  have ht : Tendsto (fun n : ℕ => n) atTop (𝓟 {n : ℕ | P n}) :=
    prob_14_8_tendsto_filter_of_subseq_subseq_tendsto
      (F := fun n : ℕ => n)
      (L := 𝓟 {n : ℕ | P n})
      (fun φ hφ => by
        obtain ⟨ψ, hψ, hP⟩ := h φ hφ
        exact ⟨ψ, hψ, by simpa [tendsto_principal] using hP⟩)
  simpa [tendsto_principal] using ht

theorem prob_14_8_tendstoUniformlyOn_of_subseq_subseq_tendstoUniformlyOn
    {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {g : α → β}
    {s : Set α}
    (h :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          TendstoUniformlyOn
            (fun n : ℕ => F (φ (ψ n))) g atTop s) :
    TendstoUniformlyOn F g atTop s := by
  intro u hu
  exact prob_14_8_eventually_of_subseq_subseq_eventually
    (P := fun n : ℕ => ∀ x : α, x ∈ s → (g x, F n x) ∈ u)
    (fun φ hφ => by
      obtain ⟨ψ, hψ, hconv⟩ := h φ hφ
      exact ⟨ψ, hψ, hconv u hu⟩)

theorem prob_14_8_tendstoLocallyUniformlyOn_of_subseq_subseq_tendstoLocallyUniformlyOn
    {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    [LocallyCompactSpace α] {F : ℕ → α → β} {g : α → β} {s : Set α}
    (hs : IsOpen s)
    (h :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          TendstoLocallyUniformlyOn
            (fun n : ℕ => F (φ (ψ n))) g atTop s) :
    TendstoLocallyUniformlyOn F g atTop s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKs
  exact prob_14_8_tendstoUniformlyOn_of_subseq_subseq_tendstoUniformlyOn
    (F := F) (g := g) (s := K)
    (fun φ hφ => by
      obtain ⟨ψ, hψ, hconv⟩ := h φ hφ
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs] at hconv
      exact ⟨ψ, hψ, hconv K hK hKs⟩)
