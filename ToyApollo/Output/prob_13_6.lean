/-
TASK ID: prob_13_6
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_13_7

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

theorem prob_13_6 {Ω : Type*} [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ} {φ : ℝ → ℝ}
    (hX : Integrable X P) (hφX : Integrable (fun ω => φ (X ω)) P)
    (hφ : ConvexOn ℝ Set.univ φ) :
    (fun ω => φ (P[X | 𝓖] ω)) ≤ᵐ[P] P[fun ω => φ (X ω) | 𝓖] := by
  have hφ_lsc : LowerSemicontinuous φ := by
    have hcontOn : ContinuousOn φ Set.univ := hφ.continuousOn isOpen_univ
    exact (continuousOn_univ.mp hcontOn).lowerSemicontinuous
  let 𝓐 : Set (ℝ → ℝ) :=
    {f | f ≤ φ ∧ ∃ (l : ℝ →L[ℝ] ℝ) (c : ℝ), f = l + ContinuousMap.const ℝ c}
  have h𝓐_lub : IsLUB 𝓐 φ := by
    have h𝓐_nonempty : 𝓐.Nonempty := by
      obtain ⟨l, c, hlc⟩ :=
        ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (s := Set.univ) (φ := φ)
          (x := (0 : ℝ)) (a := φ 0 - 1) (mem_univ 0) (by linarith)
          isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφ_lsc) hφ
      exact ⟨l + ContinuousMap.const ℝ c,
        fun x => by simpa using hlc.1 ⟨x, mem_univ x⟩, l, c, rfl⟩
    have h𝓐_bdd : BddAbove 𝓐 := ⟨φ, fun f hf => hf.1⟩
    exact (ConvexOn.real_univ_sSup_affine_eq (φ := φ) hφ_lsc hφ).symm ▸
      isLUB_csSup h𝓐_nonempty h𝓐_bdd
  have h𝓐_lsc : ∀ f ∈ 𝓐, LowerSemicontinuous f := by
    intro f hf
    rcases hf.2 with ⟨l, c, rfl⟩
    exact Continuous.lowerSemicontinuous (by fun_prop)
  obtain ⟨𝓐', h𝓐'_sub, h𝓐'_count, h𝓐'_lub⟩ :=
    exists_countable_lowerSemicontinuous_isLUB h𝓐_lsc h𝓐_lub
  haveI : Countable 𝓐' := h𝓐'_count.to_subtype
  have hle_aff :
      ∀ f : 𝓐', (fun ω => f.1 (P[X | 𝓖] ω)) ≤ᵐ[P]
        P[fun ω => φ (X ω) | 𝓖] := by
    intro f
    rcases (h𝓐'_sub f.2).2 with ⟨l, c, hf_eq⟩
    have hlin_int : Integrable (fun ω => (l : ℝ → ℝ) (X ω) + c) P := by
      exact (l.integrable_comp hX).add (integrable_const c)
    have hlin_le :
        (fun ω => (l : ℝ → ℝ) (X ω) + c) ≤ᵐ[P] fun ω => φ (X ω) := by
      refine ae_of_all P ?_
      intro ω
      have hminor : (l + ContinuousMap.const ℝ c : ℝ → ℝ) ≤ φ :=
        by simpa [hf_eq] using (h𝓐'_sub f.2).1
      simpa using hminor (X ω)
    have hmono :
        P[fun ω => (l : ℝ → ℝ) (X ω) + c | 𝓖] ≤ᵐ[P]
          P[fun ω => φ (X ω) | 𝓖] :=
      condExp_mono hlin_int hφX hlin_le
    have haff :
        (fun ω => (l : ℝ → ℝ) (P[X | 𝓖] ω) + c) =ᵐ[P]
          P[fun ω => (l : ℝ → ℝ) (X ω) + c | 𝓖] :=
      ContinuousLinearMap.comp_condExp_add_const_comm
        (μ := P) (m := 𝓖) (f := X) h𝓖 hX l c
    have hf_left :
        (fun ω => f.1 (P[X | 𝓖] ω)) =ᵐ[P]
          fun ω => (l : ℝ → ℝ) (P[X | 𝓖] ω) + c := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      simp [hf_eq]
    exact hf_left.trans_le (haff.trans_le hmono)
  have hall : ∀ᵐ ω ∂P, ∀ f : 𝓐',
      f.1 (P[X | 𝓖] ω) ≤ P[fun ω => φ (X ω) | 𝓖] ω := by
    exact ae_all_iff.mpr hle_aff
  filter_upwards [hall] with ω hω
  let y : ℝ := P[X | 𝓖] ω
  let r : ℝ := P[fun ω => φ (X ω) | 𝓖] ω
  let ub : ℝ → ℝ := fun z => if z = y then r else φ z
  have hupper : ∀ f ∈ 𝓐', f ≤ ub := by
    intro f hf z
    by_cases hz : z = y
    · have hfz := hω ⟨f, hf⟩
      simpa [ub, hz, y, r] using hfz
    · have hfφ : f z ≤ φ z := (h𝓐'_lub.1 hf) z
      simpa [ub, hz] using hfφ
  have hφub : φ ≤ ub := h𝓐'_lub.2 hupper
  have hy : φ y ≤ r := by
    simpa [ub] using hφub y
  simpa [y, r] using hy
