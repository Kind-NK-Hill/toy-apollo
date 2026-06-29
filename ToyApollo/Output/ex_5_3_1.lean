/-
TASK ID: ex_5_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

inductive FourOutcome
  | a | b | c | d
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace FourOutcome := ⊤

instance : MeasurableSingletonClass FourOutcome := ⟨by
  intro x
  simp
⟩

noncomputable def fourPointPMF : PMF FourOutcome :=
  PMF.uniformOfFintype FourOutcome

noncomputable def fourPointMeasure : Measure FourOutcome :=
  fourPointPMF.toMeasure

noncomputable instance : IsProbabilityMeasure fourPointMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

def E1f : Finset FourOutcome := {FourOutcome.a, FourOutcome.d}
def E2f : Finset FourOutcome := {FourOutcome.b, FourOutcome.d}
def E3f : Finset FourOutcome := {FourOutcome.c, FourOutcome.d}
def Df : Finset FourOutcome := {FourOutcome.d}

def E1 : Set FourOutcome := E1f
def E2 : Set FourOutcome := E2f
def E3 : Set FourOutcome := E3f

def exampleEvent : Fin 3 → Set FourOutcome
  | 0 => E1
  | 1 => E2
  | 2 => E3

lemma fourPointMeasure_finset (s : Finset FourOutcome) :
    fourPointMeasure (s : Set FourOutcome) = (s.card : ENNReal) * (1 / 4 : ENNReal) := by
  have hcard : Fintype.card FourOutcome = 4 := by decide
  rw [fourPointMeasure, PMF.toMeasure_apply_finset]
  simp [fourPointPMF, PMF.uniformOfFintype_apply, hcard]

lemma quarter_eq_half_mul_half :
    (1 / 4 : ENNReal) = (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [one_div])
    (by
      apply ENNReal.mul_ne_top
      · simp [one_div]
      · simp [one_div])).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma two_mul_quarter_eq_half :
    ((2 : ENNReal) * (1 / 4 : ENNReal)) = (1 / 2 : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by
      simpa [one_div] using
        (show ((2 : ENNReal) * (4 : ENNReal)⁻¹) ≠ ∞ by
          exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top 2)
            ((ENNReal.inv_ne_top).2 (by norm_num))))
    (by
      simpa [one_div] using
        (show ((2 : ENNReal)⁻¹) ≠ ∞ by
          exact (ENNReal.inv_ne_top).2 (by norm_num)))).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma eighth_eq_half_cube :
    (1 / 8 : ENNReal) =
      (1 / 2 : ENNReal) * (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [one_div])
    (by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top <;> simp [one_div]
      · simp [one_div])).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma half_pow_three_eq_eighth :
    ((1 / 2 : ENNReal) ^ 3) = (1 / 8 : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [one_div])
    (by simp [one_div])).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma measure_E1 : fourPointMeasure E1 = (1 / 2 : ENNReal) := by
  rw [E1]
  rw [fourPointMeasure_finset]
  have hcard : E1f.card = 2 := by decide
  rw [hcard]
  simpa using two_mul_quarter_eq_half

lemma measure_E2 : fourPointMeasure E2 = (1 / 2 : ENNReal) := by
  rw [E2]
  rw [fourPointMeasure_finset]
  have hcard : E2f.card = 2 := by decide
  rw [hcard]
  simpa using two_mul_quarter_eq_half

lemma measure_E3 : fourPointMeasure E3 = (1 / 2 : ENNReal) := by
  rw [E3]
  rw [fourPointMeasure_finset]
  have hcard : E3f.card = 2 := by decide
  rw [hcard]
  simpa using two_mul_quarter_eq_half

lemma measure_D : fourPointMeasure (Df : Set FourOutcome) = (1 / 4 : ENNReal) := by
  rw [fourPointMeasure_finset]
  have hcard : Df.card = 1 := by decide
  simp [hcard]

lemma inter_E1_E2 : E1 ∩ E2 = (Df : Set FourOutcome) := by
  ext x
  fin_cases x <;> simp [E1, E2, E1f, E2f, Df]

lemma inter_E1_E3 : E1 ∩ E3 = (Df : Set FourOutcome) := by
  ext x
  fin_cases x <;> simp [E1, E3, E1f, E3f, Df]

lemma inter_E2_E3 : E2 ∩ E3 = (Df : Set FourOutcome) := by
  ext x
  fin_cases x <;> simp [E2, E3, E2f, E3f, Df]

lemma inter_E1_E2_E3 : E1 ∩ E2 ∩ E3 = (Df : Set FourOutcome) := by
  ext x
  fin_cases x <;> simp [E1, E2, E3, E1f, E2f, E3f, Df]

lemma measure_inter_E1_E2 : fourPointMeasure (E1 ∩ E2) = (1 / 4 : ENNReal) := by
  rw [inter_E1_E2, measure_D]

lemma measure_inter_E1_E3 : fourPointMeasure (E1 ∩ E3) = (1 / 4 : ENNReal) := by
  rw [inter_E1_E3, measure_D]

lemma measure_inter_E2_E3 : fourPointMeasure (E2 ∩ E3) = (1 / 4 : ENNReal) := by
  rw [inter_E2_E3, measure_D]

lemma pairwise_indep_E1_E2 :
    ProbabilityTheory.IndepSet E1 E2 fourPointMeasure := by
  have hE1 : MeasurableSet E1 := by simp [E1]
  have hE2 : MeasurableSet E2 := by simp [E2]
  rw [ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hE1 hE2 (μ := fourPointMeasure)]
  rw [measure_inter_E1_E2, measure_E1, measure_E2, quarter_eq_half_mul_half]

lemma pairwise_indep_E1_E3 :
    ProbabilityTheory.IndepSet E1 E3 fourPointMeasure := by
  have hE1 : MeasurableSet E1 := by simp [E1]
  have hE3 : MeasurableSet E3 := by simp [E3]
  rw [ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hE1 hE3 (μ := fourPointMeasure)]
  rw [measure_inter_E1_E3, measure_E1, measure_E3, quarter_eq_half_mul_half]

lemma pairwise_indep_E2_E3 :
    ProbabilityTheory.IndepSet E2 E3 fourPointMeasure := by
  have hE2 : MeasurableSet E2 := by simp [E2]
  have hE3 : MeasurableSet E3 := by simp [E3]
  rw [ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hE2 hE3 (μ := fourPointMeasure)]
  rw [measure_inter_E2_E3, measure_E2, measure_E3, quarter_eq_half_mul_half]

lemma exampleEvent_measurable (i : Fin 3) : MeasurableSet (exampleEvent i) := by
  fin_cases i <;> simp [exampleEvent, E1, E2, E3]

lemma inter_univ_exampleEvent :
    (⋂ i ∈ (Finset.univ : Finset (Fin 3)), exampleEvent i) = (Df : Set FourOutcome) := by
  ext x
  fin_cases x
  · constructor
    · intro hx
      have hbad : FourOutcome.a ∈ exampleEvent 1 := by
        exact Set.mem_iInter₂.mp hx 1 (by simp)
      simpa [exampleEvent, E2, E2f] using hbad
    · intro hx
      simpa [Df] using hx
  · constructor
    · intro hx
      have hbad : FourOutcome.b ∈ exampleEvent 0 := by
        exact Set.mem_iInter₂.mp hx 0 (by simp)
      simpa [exampleEvent, E1, E1f] using hbad
    · intro hx
      simpa [Df] using hx
  · constructor
    · intro hx
      have hbad : FourOutcome.c ∈ exampleEvent 0 := by
        exact Set.mem_iInter₂.mp hx 0 (by simp)
      simpa [exampleEvent, E1, E1f] using hbad
    · intro hx
      simpa [Df] using hx
  · constructor
    · intro _
      simp [Df]
    · intro hd
      rw [Set.mem_iInter₂]
      intro i hi
      fin_cases i <;> simp [exampleEvent, E1, E2, E3, E1f, E2f, E3f, Df] at hd ⊢

lemma not_mutually_indep :
    ¬ ProbabilityTheory.iIndepSet exampleEvent fourPointMeasure := by
  intro hInd
  have hbi := (ProbabilityTheory.iIndepSet_iff_meas_biInter
    (f := exampleEvent) (μ := fourPointMeasure) exampleEvent_measurable).1 hInd
  have htriple := hbi (Finset.univ : Finset (Fin 3))
  have hprod : (∏ i : Fin 3, fourPointMeasure (exampleEvent i)) = (1 / 8 : ENNReal) := by
    rw [Fin.prod_univ_three]
    simpa [exampleEvent, measure_E1, measure_E2, measure_E3, mul_assoc] using
      eighth_eq_half_cube.symm
  rw [inter_univ_exampleEvent, measure_D, hprod] at htriple
  have hreal : ((1 / 4 : ENNReal).toReal) = ((1 / 8 : ENNReal).toReal) := congrArg ENNReal.toReal htriple
  norm_num at hreal

theorem ex_5_3_1 :
    fourPointMeasure E1 = (1 / 2 : ENNReal) ∧
      fourPointMeasure E2 = (1 / 2 : ENNReal) ∧
      fourPointMeasure E3 = (1 / 2 : ENNReal) ∧
      ProbabilityTheory.IndepSet E1 E2 fourPointMeasure ∧
      ProbabilityTheory.IndepSet E1 E3 fourPointMeasure ∧
      ProbabilityTheory.IndepSet E2 E3 fourPointMeasure ∧
      fourPointMeasure (E1 ∩ E2 ∩ E3) = (1 / 4 : ENNReal) ∧
      fourPointMeasure E1 * fourPointMeasure E2 * fourPointMeasure E3 = (1 / 8 : ENNReal) ∧
      ¬ ProbabilityTheory.iIndepSet exampleEvent fourPointMeasure := by
  refine ⟨measure_E1, measure_E2, measure_E3, pairwise_indep_E1_E2, pairwise_indep_E1_E3,
    pairwise_indep_E2_E3, ?_, ?_, not_mutually_indep⟩
  · rw [inter_E1_E2_E3, measure_D]
  · rw [measure_E1, measure_E2, measure_E3, ← eighth_eq_half_cube]
