/-
TASK ID: etemadi_pairwise_iid_slln
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open scoped Topology
theorem etemadi_pairwise_iid_strong_law_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) P)
  (hpairwise : Pairwise fun i j => X i ⟂ᵢ[P] X j)
  (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
        atTop (nhds P[X 0]) := by
  have h :=
    ProbabilityTheory.strong_law_ae_real X hInt hpairwise hident
  filter_upwards [h] with ω hω
  simpa [div_eq_mul_inv, mul_comm] using hω
