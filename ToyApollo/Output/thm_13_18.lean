/-
TASK ID: thm_13_18
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_13_18_support

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

noncomputable section

theorem thm_13_18 {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hOptional : thm_13_18_optionalStoppingCases P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hConst :
      ∀ n : ℕ,
        ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
          ∫ ω, X 0 ω ∂P :=
    thm_13_17_expectation_constant hM hT hSigmaFinite
  have hStoppedMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P := by
    intro n
    exact (thm_13_17_stoppedProcess_integrable hM hT n).aestronglyMeasurable
  rcases hOptional with hBounded | hRest
  · exact thm_13_18_bounded_case hConst hBounded
  · rcases hRest with hUniform | hIncrement
    · exact thm_13_18_uniformBound_case hStoppedMeas hConst hUniform
    · exact thm_13_18_boundedIncrement_case hM hStoppedMeas hConst hIncrement

theorem thm_13_18_canonical {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hOptional : thm_13_18_optionalStoppingCasesCanonical P X T) :
    ∫ ω, thm_13_18_stoppedValueReal X T ω ∂P =
      ∫ ω, X 0 ω ∂P :=
  thm_13_18 hM hT hSigmaFinite
    (thm_13_18_optionalStoppingCases_of_canonical hOptional)
