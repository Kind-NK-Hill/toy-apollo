import ToyApollo.Output.thm_3_7
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set MeasurableSpace

/-
Theorem 3.9.
Two probability measures P, Q on ℝ that agree on every left-infinite closed ray
(-∞, x] = Iic x are equal.

Source route (not an adapter one-liner): the class of sets on which P and Q agree
is a λ-system (Dynkin system) — it contains ∅, is closed under complement (using
finiteness of a probability measure so P(Aᶜ)=1-P(A)), and closed under countable
disjoint unions (countable additivity). The rays {Iic x} form a π-system that
generates the Borel σ-algebra, so by the project's π–λ theorem (`thm_3_7`) the
equalizer contains every Borel set, i.e. P = Q.
-/

/-- Theorem 3.9 (Uniqueness from the CDF): probability measures agreeing on all
`Iic x` are equal, proved through the π–λ / Dynkin-equalizer spine. -/
theorem thm_3_9 (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
    P = Q := by
  -- The equalizer set, carrying measurability so complements and unions stay in it.
  let L : DynkinSystem ℝ :=
    { Has := fun s => MeasurableSet s ∧ P s = Q s
      has_empty := ⟨MeasurableSet.empty, by simp⟩
      has_compl := fun {a} ha =>
        ⟨ha.1.compl, by
          rw [measure_compl ha.1 (measure_ne_top P a), measure_compl ha.1 (measure_ne_top Q a),
            measure_univ, measure_univ, ha.2]⟩
      has_iUnion_nat := fun {f} hd hf =>
        ⟨MeasurableSet.iUnion fun i => (hf i).1, by
          rw [measure_iUnion hd fun i => (hf i).1, measure_iUnion hd fun i => (hf i).1]
          exact tsum_congr fun i => (hf i).2⟩ }
  -- (i) the generating rays are a π-system all inside L.
  have hPL : ∀ s ∈ (range Iic : Set (Set ℝ)), L.Has s := by
    rintro s ⟨x, rfl⟩
    exact ⟨measurableSet_Iic, h x⟩
  -- (ii) close via the project's π–λ theorem.
  have key : ∀ s, MeasurableSet[generateFrom (range Iic)] s → L.Has s :=
    thm_3_7 (P := range Iic) (L := L) (isPiSystem_Iic (α := ℝ)) hPL
  -- On ℝ the ambient σ-algebra is Borel = generateFrom (range Iic).
  have e := (@BorelSpace.measurable_eq ℝ _ _ _).trans (borel_eq_generateFrom_Iic ℝ)
  exact Measure.ext fun s hs => (key s (e ▸ hs)).2
