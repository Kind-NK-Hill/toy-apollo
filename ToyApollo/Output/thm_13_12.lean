/-
TASK ID: thm_13_12
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-discrete-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_13_12_support

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

theorem thm_13_12 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (X Y : Ω → ℝ) (A : ℕ → Set Ω)
    (hY : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y)
    (hPartition : thm_13_12_countablePartition A)
    (hGenerated : thm_13_12_generatedByPartition 𝓖 A) :
    Y =ᵐ[P] @thm_13_12_countablePartitionConditionalExpectation Ω 𝓕 P _ A X := by
  have hVersion :
      @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X
        (@thm_13_12_countablePartitionConditionalExpectation Ω 𝓕 P _ A X) :=
    @thm_13_12_countablePartitionVersionSupport Ω 𝓕 P _ 𝓖 h𝓖 A X
      hPartition hGenerated
      (@def_13_3_integrable_original Ω 𝓕 P 𝓖 h𝓖 X Y hY)
  exact @thm_13_4 Ω 𝓕 P _ 𝓖 h𝓖 X Y
    (@thm_13_12_countablePartitionConditionalExpectation Ω 𝓕 P _ A X)
    hY hVersion
