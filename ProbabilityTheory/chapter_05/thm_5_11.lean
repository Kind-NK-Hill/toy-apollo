/-
TASK ID: thm_5_11
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.Probability.Independence.ZeroOne







-- WRITE FINAL LEAN CODE BELOW
open Filter

 
@[reducible]
def tailSigmaAlgebra {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  limsup (fun n => MeasurableSpace.comap (X n) ‹MeasurableSpace β›) atTop



theorem thm_5_11 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) {t : Set Ω}
    (ht_tail : @MeasurableSet Ω (tailSigmaAlgebra X) t) :
    P t = 0 ∨ P t = 1 := by
  let s : ℕ → MeasurableSpace Ω := fun n => MeasurableSpace.comap (X n) ‹MeasurableSpace β›
  have h_le : ∀ n, s n ≤ ‹MeasurableSpace Ω› := fun n => (h_meas n).comap_le
  simpa [s, tailSigmaAlgebra] using
    ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
      (μ := P) h_le h_indep.iIndep ht_tail
