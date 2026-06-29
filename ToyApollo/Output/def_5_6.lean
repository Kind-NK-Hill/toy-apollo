import Mathlib

def def_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) μ)
