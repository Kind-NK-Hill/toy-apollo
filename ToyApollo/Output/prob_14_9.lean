import Mathlib
import ToyApollo.Output.def_14_1
import ToyApollo.Output.thm_14_1

/-
TASK ID: prob_14_9
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.9.} (Continuous mapping theorem for convergence in distribution) Let Xn be a

sequence of random variables converging to X in distribution. Let f : R \to R be a

function that is continuous at the set Sf \subseteq R. Show that if P(X \in Sf ) = 1, then

f( Xn)

L

-\to f( X) . (Hint: Apply Levy's continuity theorem.)
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Source-level setup for Problem 14.9, the continuous mapping theorem for
convergence in distribution.

The sequence and limit are represented by their laws.  The mapped laws record
the distributions of `f(X_n)` and `f(X)`. -/
structure prob_14_9_ContinuousMappingSetup where
  sourceLaws : ℕ → ProbabilityMeasure ℝ
  targetLaw : ProbabilityMeasure ℝ
  f : ℝ → ℝ
  Sf : Set ℝ
  Sf_measurable : MeasurableSet Sf
  f_aemeasurable_source :
    ∀ n : ℕ, AEMeasurable f (sourceLaws n : Measure ℝ)
  f_aemeasurable_target :
    AEMeasurable f (targetLaw : Measure ℝ)
  source_convergence : def_14_1 sourceLaws targetLaw
  continuous_on_Sf : ∀ x : ℝ, x ∈ Sf → ContinuousAt f x
  target_hits_Sf : (targetLaw : Measure ℝ) Sf = 1

namespace prob_14_9_ContinuousMappingSetup

def mappedLaws (S : prob_14_9_ContinuousMappingSetup) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n => (S.sourceLaws n).map (S.f_aemeasurable_source n)

def mappedTargetLaw (S : prob_14_9_ContinuousMappingSetup) :
    ProbabilityMeasure ℝ :=
  S.targetLaw.map S.f_aemeasurable_target

end prob_14_9_ContinuousMappingSetup

theorem prob_14_9_mapped_laws_are_pushforwards
    (S : prob_14_9_ContinuousMappingSetup) (n : ℕ) :
    (S.mappedLaws n : Measure ℝ) =
      Measure.map S.f (S.sourceLaws n : Measure ℝ) := by
  apply Measure.ext
  intro A hA
  simp [prob_14_9_ContinuousMappingSetup.mappedLaws,
    Measure.map_apply_of_aemeasurable, S.f_aemeasurable_source n, hA]

theorem prob_14_9_mapped_target_is_pushforward
    (S : prob_14_9_ContinuousMappingSetup) :
    (S.mappedTargetLaw : Measure ℝ) =
      Measure.map S.f (S.targetLaw : Measure ℝ) := by
  apply Measure.ext
  intro A hA
  simp [prob_14_9_ContinuousMappingSetup.mappedTargetLaw,
    Measure.map_apply_of_aemeasurable, S.f_aemeasurable_target, hA]

/-- The original convergence in distribution, restated as convergence of laws. -/
theorem prob_14_9_source_laws_converge
    (S : prob_14_9_ContinuousMappingSetup) :
    Tendsto S.sourceLaws atTop (𝓝 S.targetLaw) :=
  (def_14_1_iff_tendsto).1 S.source_convergence

/-- If `F` is closed, the source-law mass of the preimage of `F` under `f` has
the right Portmanteau limsup bound.  The only continuity used is continuity on
the full-limit-mass set `Sf`. -/
theorem prob_14_9_limsup_preimage_closed_le
    (S : prob_14_9_ContinuousMappingSetup) :
    ∀ F : Set ℝ, IsClosed F →
      limsup (fun n : ℕ => (S.sourceLaws n : Measure ℝ) (S.f ⁻¹' F)) atTop ≤
        (S.targetLaw : Measure ℝ) (S.f ⁻¹' F) := by
  intro F hF
  let A : Set ℝ := S.f ⁻¹' F
  have hSf_compl : (S.targetLaw : Measure ℝ) S.Sfᶜ = 0 := by
    rw [measure_compl S.Sf_measurable (measure_ne_top _ _), S.target_hits_Sf]
    simp
  have hdiff_subset : closure A \ A ⊆ S.Sfᶜ := by
    intro x hx hxSf
    have hxA : x ∈ A := by
      by_contra hx_not_A
      have hpre : S.f ⁻¹' Fᶜ ∈ 𝓝 x := by
        refine (S.continuous_on_Sf x hxSf).preimage_mem_nhds ?_
        exact (isOpen_compl_iff.mpr hF).mem_nhds (by simpa [A] using hx_not_A)
      rcases (mem_closure_iff_nhds.mp hx.1) (S.f ⁻¹' Fᶜ) hpre with ⟨y, hy_comp, hy_A⟩
      exact hy_comp hy_A
    exact hx.2 hxA
  have hdiff_null : (S.targetLaw : Measure ℝ) (closure A \ A) = 0 :=
    measure_mono_null hdiff_subset hSf_compl
  have hclosure_eq : (S.targetLaw : Measure ℝ) (closure A) =
      (S.targetLaw : Measure ℝ) A := by
    apply le_antisymm
    · calc
        (S.targetLaw : Measure ℝ) (closure A)
            ≤ (S.targetLaw : Measure ℝ) (A ∪ (closure A \ A)) := by
              refine measure_mono ?_
              intro x hx
              by_cases hxA : x ∈ A
              · exact Or.inl hxA
              · exact Or.inr ⟨hx, hxA⟩
        _ ≤ (S.targetLaw : Measure ℝ) A +
              (S.targetLaw : Measure ℝ) (closure A \ A) :=
              measure_union_le A (closure A \ A)
        _ = (S.targetLaw : Measure ℝ) A := by simp [hdiff_null]
    · exact measure_mono subset_closure
  calc
    limsup (fun n : ℕ => (S.sourceLaws n : Measure ℝ) A) atTop
        ≤ limsup (fun n : ℕ => (S.sourceLaws n : Measure ℝ) (closure A)) atTop := by
          refine limsup_le_limsup (.of_forall ?_)
          intro n
          exact measure_mono subset_closure
    _ ≤ (S.targetLaw : Measure ℝ) (closure A) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
          (prob_14_9_source_laws_converge S) isClosed_closure
    _ = (S.targetLaw : Measure ℝ) A := hclosure_eq

/-- The mapped laws converge weakly.  This proves the continuous mapping theorem
under the original a.e./`Sf` continuity hypothesis, without strengthening it to
global continuity of `f`. -/
theorem prob_14_9_mapped_laws_converge
    (S : prob_14_9_ContinuousMappingSetup) :
    Tendsto S.mappedLaws atTop (𝓝 S.mappedTargetLaw) := by
  refine tendsto_of_forall_isClosed_limsup_le' ?_
  intro F hF
  let A : Set ℝ := S.f ⁻¹' F
  have hsource :=
    prob_14_9_limsup_preimage_closed_le S F hF
  have hmap_source :
      (fun n : ℕ => (S.mappedLaws n : Measure ℝ) F) =
        fun n : ℕ => (S.sourceLaws n : Measure ℝ) A := by
    funext n
    simp [prob_14_9_ContinuousMappingSetup.mappedLaws, A,
      Measure.map_apply_of_aemeasurable, S.f_aemeasurable_source n,
      hF.measurableSet]
  have hmap_target :
      (S.mappedTargetLaw : Measure ℝ) F =
        (S.targetLaw : Measure ℝ) A := by
    simp [prob_14_9_ContinuousMappingSetup.mappedTargetLaw, A,
      Measure.map_apply_of_aemeasurable, S.f_aemeasurable_target,
      hF.measurableSet]
  simpa [hmap_source, hmap_target] using hsource

/-- The characteristic-function convergence for the mapped sequence, obtained
at theorem level from the continuity-set hypothesis and source convergence. -/
theorem prob_14_9_mapped_characteristic_convergence
    (S : prob_14_9_ContinuousMappingSetup) :
    thm_14_1_pointwiseCharFunConvergence
      S.mappedLaws
      (fun t : ℝ => thm_14_1_characteristicFunction S.mappedTargetLaw t) := by
  intro t
  have h := (ProbabilityMeasure.tendsto_iff_tendsto_charFun
    (μ := S.mappedLaws) (μ₀ := S.mappedTargetLaw)).1
    (prob_14_9_mapped_laws_converge S) t
  simpa [thm_14_1_characteristicFunction] using h

/-- Problem 14.9: if `X_n` converges in distribution to `X`, and `f` is
continuous at a set hit by `X` with probability one, then `f(X_n)` converges in
distribution to `f(X)`. -/
theorem prob_14_9
    (S : prob_14_9_ContinuousMappingSetup) :
    Tendsto S.mappedLaws atTop (𝓝 S.mappedTargetLaw) ∧
      def_14_1 S.mappedLaws S.mappedTargetLaw := by
  have h := prob_14_9_mapped_laws_converge S
  exact ⟨h, (def_14_1_iff_tendsto).2 h⟩
