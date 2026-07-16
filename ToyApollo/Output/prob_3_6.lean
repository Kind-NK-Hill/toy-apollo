import ToyApollo.Output.thm_3_8
import Mathlib

open MeasureTheory MeasurableSpace Set

/-- The sample space for problem 3.6 -/
inductive Omega6 : Type
  | a | b | c | d | e | f
  deriving DecidableEq, Fintype

open Omega6

instance : MeasurableSpace Omega6 := ⊤

instance : MeasurableSingletonClass Omega6 where
  measurableSet_singleton _ := trivial

noncomputable def P36 : Measure Omega6 :=
  (1/6 : ENNReal) • Measure.count

noncomputable def Q36 : Measure Omega6 :=
  (1/2 : ENNReal) • Measure.dirac b + (1/2 : ENNReal) • Measure.dirac e

def C36 : Set (Set Omega6) :=
  {{Omega6.a, b, c}, {b, c, d}, {c, d, e}, {d, e, f}, {e, f, Omega6.a}, {f, Omega6.a, b}}

/-
Part (a): generateFrom C = top
-/
theorem prob_3_6a : MeasurableSpace.generateFrom C36 = ⊤ := by
  refine' le_antisymm ( le_top ) _;
  intro s hs; by_cases hs' : s = ∅ <;> simp_all +decide [ Set.ext_iff ] ;
  · convert MeasurableSet.empty;
    exact Set.eq_empty_of_forall_notMem hs';
  · -- Since $s$ is non-empty, we can write it as a union of singletons.
    obtain ⟨x, hx⟩ : ∃ x, x ∈ s := hs'
    have h_union : s = ⋃ x ∈ s, {x} := by
      aesop;
    rw [ h_union ];
    refine' MeasurableSet.biUnion _ _;
    · exact Set.to_countable s;
    · intro y hy; exact (by
      -- Since $y \in s$, we can write $\{y\}$ as an intersection of elements from $C36$.
      have h_inter : ∃ A B : Set Omega6, A ∈ C36 ∧ B ∈ C36 ∧ {y} = A ∩ B := by
        fin_cases y <;> simp +decide [ C36 ];
        all_goals simp +decide [ Set.Subset.antisymm_iff, Set.subset_def ] at *;
      obtain ⟨ A, B, hA, hB, h ⟩ := h_inter; exact h.symm ▸ MeasurableSet.inter ( MeasurableSpace.measurableSet_generateFrom hA ) ( MeasurableSpace.measurableSet_generateFrom hB ) ;);

/-
Part (b): P(A) = Q(A) for all A in C
-/
theorem prob_3_6b : ∀ A ∈ C36, P36 A = Q36 A := by
  unfold C36 P36 Q36;
  simp +decide [ Measure.count_apply, Set.toFinset_card ];
  simp +decide [ Set.encard ];
  rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
  norm_num [ ENNReal.mul_eq_top ]

/-
Part (c): P ≠ Q
-/
theorem prob_3_6c : P36 ≠ Q36 := by
  intro h; have := congr_arg ( · { Omega6.a } ) h; norm_num [ P36, Q36 ] at this;
  simp +decide [ Pi.single_apply ] at this

/-- The family `C36` is not a pi-system: two adjacent members have a
nonempty intersection that is absent from the family. -/
theorem prob_3_6c_not_piSystem : ¬ IsPiSystem C36 := by
  intro hpi
  have hmem := hpi
    ({Omega6.a, b, c} : Set Omega6) (by simp [C36])
    ({b, c, d} : Set Omega6) (by simp [C36])
    ⟨b, by simp⟩
  simpa +decide [C36, Set.ext_iff, Set.subset_def] using hmem

/-- Problem 3.6: `C36` generates the full sigma-algebra and the two measures
agree on `C36`, but they are distinct.  There is no contradiction with the
uniqueness theorem because `C36` is not a pi-system. -/
theorem prob_3_6 :
    MeasurableSpace.generateFrom C36 = ⊤ ∧
      (∀ A ∈ C36, P36 A = Q36 A) ∧
        P36 ≠ Q36 ∧ ¬ IsPiSystem C36 :=
  ⟨prob_3_6a, prob_3_6b, prob_3_6c, prob_3_6c_not_piSystem⟩
