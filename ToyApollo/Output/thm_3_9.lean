/-
TASK ID: thm_3_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_3_8
import ToyApollo.Output.ex_3_1_2
import ToyApollo.Output.ex_3_1_4
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Set ENNReal MeasurableSpace

theorem B0_finite_disjoint_generator_normal_form
    {A : Set ℝ} (hA : A ∈ B0.carrier) :
    ∃ (n : ℕ) (S : Fin n → Set ℝ),
      (∀ i, S i ∈ B0_generators) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      A = ⋃ i, S i := by
  classical
  obtain ⟨P⟩ :=
    (IntervalPremeasure.mem_B0_iff_nonempty_normalForm).mp hA
  let e : Fin P.val.parts.card ≃ P.val.parts := P.val.parts.equivFin.symm
  let S : Fin P.val.parts.card → Set ℝ := fun i => (e i : Set ℝ)
  refine ⟨P.val.parts.card, S, ?_, ?_, ?_⟩
  · intro i
    have hi : S i ∈ IntervalPremeasure.atoms := P.property (e i).property
    simpa only [IntervalPremeasure.atoms_eq_B0_generators] using hi
  · intro i j hij
    apply P.val.disjoint (e i).property (e j).property
    intro hsets
    apply hij
    apply e.injective
    exact Subtype.ext hsets
  · have hparts : ⋃₀ (P.val.parts : Set (Set ℝ)) = A := by
      rw [← sSup_eq_sUnion, ← Finset.sup_id_eq_sSup, P.val.sup_parts]
    ext x
    constructor
    · intro hxA
      have hxparts : x ∈ ⋃₀ (P.val.parts : Set (Set ℝ)) :=
        (Set.ext_iff.mp hparts x).mpr hxA
      rcases mem_sUnion.mp hxparts with ⟨t, ht, hxt⟩
      let t' : P.val.parts := ⟨t, ht⟩
      obtain ⟨i, hi⟩ := e.surjective t'
      refine mem_iUnion.mpr ⟨i, ?_⟩
      change x ∈ (e i : Set ℝ)
      have hi' : (e i : Set ℝ) = t := congrArg Subtype.val hi
      rw [hi']
      exact hxt
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, hxi⟩
      apply (Set.ext_iff.mp hparts x).mp
      exact mem_sUnion_of_mem hxi (e i).property

private theorem measure_eq_on_B0_generator_of_Iic
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ x : ℝ, P (Iic x) = Q (Iic x))
    {s : Set ℝ} (hs : s ∈ B0_generators) :
    P s = Q s := by
  rcases hs with (⟨a, b, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩ | rfl)
  · by_cases hab : a < b
    · have hdis : Disjoint (Iic a) (Ioc a b) := by
        refine Set.disjoint_left.2 ?_
        intro x hxa hxab
        exact (not_lt_of_ge hxa) hxab.1
      have hunion : Iic a ∪ Ioc a b = Iic b := by
        ext x
        simp only [mem_union, mem_Iic, mem_Ioc]
        constructor
        · rintro (hxa | hxab)
          · exact hxa.trans hab.le
          · exact hxab.2
        · intro hxb
          by_cases hxa : x ≤ a
          · exact Or.inl hxa
          · exact Or.inr ⟨lt_of_not_ge hxa, hxb⟩
      have hPsplit :
          P (Iic b) = P (Iic a) + P (Ioc a b) := by
        rw [← hunion]
        exact measure_union hdis measurableSet_Ioc
      have hQsplit :
          Q (Iic b) = Q (Iic a) + Q (Ioc a b) := by
        rw [← hunion]
        exact measure_union hdis measurableSet_Ioc
      apply (ENNReal.add_left_inj (measure_ne_top P (Iic a))).mp
      calc
        P (Ioc a b) + P (Iic a) = P (Iic a) + P (Ioc a b) := add_comm _ _
        _ = P (Iic b) := hPsplit.symm
        _ = Q (Iic b) := h b
        _ = Q (Iic a) + Q (Ioc a b) := hQsplit
        _ = P (Iic a) + Q (Ioc a b) := by rw [h a]
        _ = Q (Ioc a b) + P (Iic a) := add_comm _ _
    · simp only [Ioc_eq_empty hab, measure_empty]
  · exact h b
  · rw [← compl_Iic]
    calc
      P (Iic a)ᶜ = P univ - P (Iic a) :=
        measure_compl measurableSet_Iic (measure_ne_top P (Iic a))
      _ = Q univ - Q (Iic a) := by rw [measure_univ, measure_univ, h a]
      _ = Q (Iic a)ᶜ :=
        (measure_compl measurableSet_Iic (measure_ne_top Q (Iic a))).symm
  · simp only [measure_univ]

theorem measure_eq_on_B0_of_Iic
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
    ∀ A ∈ B0.carrier, P A = Q A := by
  intro A hA
  obtain ⟨n, S, hgen, hdis, hunion⟩ :=
    B0_finite_disjoint_generator_normal_form hA
  have hmeas (i : Fin n) : MeasurableSet (S i) :=
    measurable_of_mem_B0 _ (GeneratedField.basic _ (hgen i))
  have hdis' : PairwiseDisjoint
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)) S :=
    hdis.set_pairwise _
  have hPsum : P (⋃ i, S i) = ∑ i, P (S i) := by
    simpa using
      (measure_biUnion_finset (μ := P) hdis' (fun i _ => hmeas i))
  have hQsum : Q (⋃ i, S i) = ∑ i, Q (S i) := by
    simpa using
      (measure_biUnion_finset (μ := Q) hdis' (fun i _ => hmeas i))
  calc
    P A = P (⋃ i, S i) := congrArg (fun T : Set ℝ => P T) hunion
    _ = ∑ i, P (S i) := hPsum
    _ = ∑ i, Q (S i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact measure_eq_on_B0_generator_of_Iic P Q h (hgen i)
    _ = Q (⋃ i, S i) := hQsum.symm
    _ = Q A := congrArg (fun T : Set ℝ => Q T) hunion.symm

theorem thm_3_9 (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
    P = Q := by
  have hgen : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom B0.carrier :=
    BorelSpace.measurable_eq.trans generateFrom_B0_eq_borel.symm
  let Ωseq : ℕ → Set ℝ := fun n => if n = 0 then univ else ∅
  have hseq_disj :
      Pairwise (fun i j => Disjoint (Ωseq i) (Ωseq j)) := by
    intro i j hij
    rcases i with _ | i
    · rcases j with _ | j
      · exact (hij rfl).elim
      · simp [Ωseq]
    · simp [Ωseq]
  have hseq_mem : ∀ i, Ωseq i ∈ B0.carrier := by
    intro i
    rcases i with _ | i
    · simpa [Ωseq] using B0.compl_mem ∅ B0.empty_mem
    · simpa [Ωseq] using B0.empty_mem
  have hseq_univ : (⋃ i, Ωseq i) = univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact mem_iUnion_of_mem 0 (by simp [Ωseq])
  have hseq_finite : ∀ i,
      P (Ωseq i) = Q (Ωseq i) ∧ P (Ωseq i) < ⊤ := by
    intro i
    rcases i with _ | i
    · constructor
      · simp [Ωseq]
      · simpa [Ωseq] using measure_lt_top P univ
    · simp [Ωseq]
  exact thm_3_8 B0.carrier hgen B0.empty_mem
    (fun s hs => B0.compl_mem s hs)
    (fun s hs t ht => B0.union_mem s t hs ht)
    P Q (measure_eq_on_B0_of_Iic P Q h)
    Ωseq hseq_disj hseq_mem hseq_univ hseq_finite
