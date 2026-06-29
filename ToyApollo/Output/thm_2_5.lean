/-
TASK ID: thm_2_5
TYPE: Theorem_with_Proof
SOURCE PLAN: 42_chap2_measure_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_2_6
import ToyApollo.Output.thm_2_4

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

def thm_2_5_gap {Ω : Type*} (A : ℕ → Set Ω) (i : ℕ) : Set Ω :=
  A 0 \ A i

theorem thm_2_5_gap_increasing {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqDecreasing A) :
    SetSeqIncreasing (thm_2_5_gap A) := by
  change Monotone (thm_2_5_gap A)
  intro i j hij x hx
  exact ⟨hx.1, fun hxAj => hx.2 (hA hij hxAj)⟩

theorem thm_2_5_gap_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hMeas : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet (thm_2_5_gap A i) := by
  intro i
  exact (hMeas 0).diff (hMeas i)

theorem thm_2_5_gap_iUnion_eq {Ω : Type*} (A : ℕ → Set Ω) :
    (⋃ i, thm_2_5_gap A i) = A 0 \ ⋂ i, A i := by
  ext x
  simp [thm_2_5_gap]

theorem thm_2_5_gap_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Set Ω} (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) (i : ℕ) :
    μ (thm_2_5_gap A i) = μ (A 0) - μ (A i) := by
  have hAi_subset : A i ⊆ A 0 := hA (Nat.zero_le i)
  have hAi_fin : μ (A i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hfin) (measure_mono hAi_subset)
  exact measure_diff hAi_subset (hMeas i).nullMeasurableSet hAi_fin

theorem thm_2_5_source_spine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  have hA0_ne_top : μ (A 0) ≠ ⊤ := ne_top_of_lt hfin
  have hInter_subset : (⋂ i, A i) ⊆ A 0 := iInter_subset A 0
  have hInter_fin : μ (⋂ i, A i) ≤ μ (A 0) := measure_mono hInter_subset
  have hsource :
      μ (⋃ i, thm_2_5_gap A i) = ⨆ i, μ (thm_2_5_gap A i) :=
    thm_2_4 μ (thm_2_5_gap A) (thm_2_5_gap_increasing hA)
      (thm_2_5_gap_measurable hMeas)
  rw [← ENNReal.sub_sub_cancel hA0_ne_top (iInf_le (fun i => μ (A i)) 0),
    ENNReal.sub_iInf, ← ENNReal.sub_sub_cancel hA0_ne_top hInter_fin,
    ← measure_diff hInter_subset (.iInter fun i => (hMeas i).nullMeasurableSet)
      (ne_top_of_le_ne_top hA0_ne_top hInter_fin),
    ← thm_2_5_gap_iUnion_eq A, hsource]
  exact congrArg (fun t => μ (A 0) - t)
    (iSup_congr fun i => thm_2_5_gap_measure μ hA hMeas hfin i)

theorem thm_2_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i))
    (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  exact thm_2_5_source_spine μ A hA hMeas hfin

theorem thm_2_5_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋂ i, A i))) := by
  have hanti : Antitone fun i => μ (A i) := fun i j hij => measure_mono (hA hij)
  have hinf : μ (⋂ i, A i) = ⨅ i, μ (A i) := thm_2_5 μ A hA hMeas hfin
  rw [hinf]
  exact tendsto_atTop_iInf hanti
