/-
TASK ID: thm_9_6
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3
import ProbabilityTheory.chapter_09.thm_9_5
import ProbabilityTheory.chapter_03.thm_3_9




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section



abbrev SameDistribution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) : Prop :=
  ProbabilityTheory.IdentDistrib X Y P P



noncomputable def measureCdf (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) : ℝ :=
  μ.real (Iic x)



theorem characteristicFunction_eq_charFun_map
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X P) (t : ℝ) :
    characteristicFunction (P.map X) t = charFun (P.map X) t := by
  rfl



theorem characteristicInversionTruncation_eq_of_charFun_eq
    (μ ν : Measure ℝ) (hchar : charFun μ = charFun ν) (a b T : ℝ) :
    characteristicInversionTruncation μ a b T =
      characteristicInversionTruncation ν a b T := by
  rw [characteristicInversionTruncation, characteristicInversionTruncation, hchar]



theorem characteristicInversionMass_eq_of_charFun_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hchar : charFun μ = charFun ν) {a b : ℝ} (hab : a < b) :
    characteristicInversionMass μ a b =
      characteristicInversionMass ν a b := by
  have hμ :
      Tendsto
        (fun T : ℝ =>
          ((2 * Real.pi : ℂ)⁻¹) *
            characteristicInversionTruncation μ a b T)
        atTop
        (nhds (characteristicInversionMass μ a b)) :=
    (thm_9_5 μ) hab
  have hν :
      Tendsto
        (fun T : ℝ =>
          ((2 * Real.pi : ℂ)⁻¹) *
            characteristicInversionTruncation ν a b T)
        atTop
        (nhds (characteristicInversionMass ν a b)) :=
    (thm_9_5 ν) hab
  have hsame :
      (fun T : ℝ =>
        ((2 * Real.pi : ℂ)⁻¹) *
          characteristicInversionTruncation ν a b T)
        =ᶠ[atTop]
      (fun T : ℝ =>
        ((2 * Real.pi : ℂ)⁻¹) *
          characteristicInversionTruncation μ a b T) := by
    filter_upwards with T
    rw [characteristicInversionTruncation_eq_of_charFun_eq μ ν hchar]
  exact tendsto_nhds_unique hμ (hν.congr' hsame)

 
theorem sameDistribution_of_cdf_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hcdf : ∀ x : ℝ, μ (Iic x) = ν (Iic x)) :
    μ = ν :=
  thm_3_9 μ ν hcdf

 
theorem atom_zero_of_measureCdf_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    μ.real ({x} : Set ℝ) = 0 := by
  have hcont_cdf :
      ContinuousAt (fun y : ℝ => ProbabilityTheory.cdf μ y) x := by
    simpa [measureCdf, ProbabilityTheory.cdf_eq_real] using hcont
  have hleft :
      Function.leftLim (fun y : ℝ => ProbabilityTheory.cdf μ y) x =
        ProbabilityTheory.cdf μ x := by
    exact hcont_cdf.continuousWithinAt.leftLim_eq
  have hzero : μ ({x} : Set ℝ) = 0 := by
    rw [← ProbabilityTheory.measure_cdf μ, StieltjesFunction.measure_singleton]
    simp [hleft]
  simp [Measure.real, hzero]



theorem characteristicInversionMass_eq_measureReal_Ioo_of_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : ContinuousAt (fun x : ℝ => measureCdf μ x) a)
    (hb : ContinuousAt (fun x : ℝ => measureCdf μ x) b) :
    characteristicInversionMass μ a b = (μ.real (Ioo a b) : ℂ) := by
  have ha0 : μ.real ({a} : Set ℝ) = 0 :=
    atom_zero_of_measureCdf_continuous μ ha
  have hb0 : μ.real ({b} : Set ℝ) = 0 :=
    atom_zero_of_measureCdf_continuous μ hb
  simp [characteristicInversionMass, ha0, hb0]



theorem measureReal_Ioo_eq_of_characteristicInversionMass_eq_of_continuous
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ}
    (hMass : characteristicInversionMass μ a b =
      characteristicInversionMass ν a b)
    (haμ : ContinuousAt (fun x : ℝ => measureCdf μ x) a)
    (hbμ : ContinuousAt (fun x : ℝ => measureCdf μ x) b)
    (haν : ContinuousAt (fun x : ℝ => measureCdf ν x) a)
    (hbν : ContinuousAt (fun x : ℝ => measureCdf ν x) b) :
    μ.real (Ioo a b) = ν.real (Ioo a b) := by
  have hμ :=
    characteristicInversionMass_eq_measureReal_Ioo_of_continuous μ haμ hbμ
  have hν :=
    characteristicInversionMass_eq_measureReal_Ioo_of_continuous ν haν hbν
  have hcomplex :
      (μ.real (Ioo a b) : ℂ) = (ν.real (Ioo a b) : ℂ) := by
    simpa [hμ, hν] using hMass
  exact Complex.ofReal_injective hcomplex

 
theorem measureCdf_countable_not_continuousAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Set.Countable {x : ℝ | ¬ ContinuousAt (fun y : ℝ => measureCdf μ y) x} := by
  have hmono : Monotone (fun y : ℝ => measureCdf μ y) := by
    intro a b hab
    exact measureReal_mono (μ := μ) (Iic_subset_Iic.2 hab)
  exact hmono.countable_not_continuousAt

 
theorem dense_common_measureCdf_continuity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Dense {x : ℝ |
      ContinuousAt (fun y : ℝ => measureCdf μ y) x ∧
      ContinuousAt (fun y : ℝ => measureCdf ν y) x} := by
  have hbad : Set.Countable
      ({x : ℝ | ¬ ContinuousAt (fun y : ℝ => measureCdf μ y) x} ∪
       {x : ℝ | ¬ ContinuousAt (fun y : ℝ => measureCdf ν y) x}) :=
    (measureCdf_countable_not_continuousAt μ).union
      (measureCdf_countable_not_continuousAt ν)
  convert hbad.dense_compl ℝ using 1
  ext x
  simp



theorem exists_common_measureCdf_continuity_between
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ,
      a < x ∧ x < b ∧
      ContinuousAt (fun y : ℝ => measureCdf μ y) x ∧
      ContinuousAt (fun y : ℝ => measureCdf ν y) x := by
  rcases (dense_common_measureCdf_continuity μ ν).exists_between hab with
    ⟨x, hxcont, hxab⟩
  exact ⟨x, hxab.1, hxab.2, hxcont.1, hxcont.2⟩



theorem measureReal_Ioo_eq_of_charFun_eq_of_common_continuity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hchar : charFun μ = charFun ν) {a b : ℝ} (hab : a < b)
    (haμ : ContinuousAt (fun x : ℝ => measureCdf μ x) a)
    (hbμ : ContinuousAt (fun x : ℝ => measureCdf μ x) b)
    (haν : ContinuousAt (fun x : ℝ => measureCdf ν x) a)
    (hbν : ContinuousAt (fun x : ℝ => measureCdf ν x) b) :
    μ.real (Ioo a b) = ν.real (Ioo a b) :=
  measureReal_Ioo_eq_of_characteristicInversionMass_eq_of_continuous
    μ ν (characteristicInversionMass_eq_of_charFun_eq μ ν hchar hab)
    haμ hbμ haν hbν



theorem measure_Ioc_eq_of_measureReal_Ioo_eq_of_common_continuity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a < b)
    (hIoo : μ.real (Ioo a b) = ν.real (Ioo a b))
    (hbμ : ContinuousAt (fun x : ℝ => measureCdf μ x) b)
    (hbν : ContinuousAt (fun x : ℝ => measureCdf ν x) b) :
    μ (Ioc a b) = ν (Ioc a b) := by
  have hbμ0 : μ.real ({b} : Set ℝ) = 0 :=
    atom_zero_of_measureCdf_continuous μ hbμ
  have hbν0 : ν.real ({b} : Set ℝ) = 0 :=
    atom_zero_of_measureCdf_continuous ν hbν
  have hμ : μ.real (Ioc a b) = μ.real (Ioo a b) := by
    rw [← Ioo_union_right hab]
    rw [measureReal_union]
    · simp [hbμ0]
    · exact disjoint_singleton_right.2 (by simp)
    · exact measurableSet_singleton b
  have hν : ν.real (Ioc a b) = ν.real (Ioo a b) := by
    rw [← Ioo_union_right hab]
    rw [measureReal_union]
    · simp [hbν0]
    · exact disjoint_singleton_right.2 (by simp)
    · exact measurableSet_singleton b
  exact (measureReal_eq_measureReal_iff
    (μ := μ) (ν := ν) (s := Ioc a b) (t := Ioc a b)
    (measure_Ioc_lt_top.ne) (measure_Ioc_lt_top.ne)).mp (by
      rw [hμ, hν, hIoo])



theorem measure_eq_of_measureReal_Ioo_eq_of_common_continuity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hIoo :
      ∀ ⦃a b : ℝ⦄, a < b →
        ContinuousAt (fun x : ℝ => measureCdf μ x) a →
        ContinuousAt (fun x : ℝ => measureCdf μ x) b →
        ContinuousAt (fun x : ℝ => measureCdf ν x) a →
        ContinuousAt (fun x : ℝ => measureCdf ν x) b →
        μ.real (Ioo a b) = ν.real (Ioo a b)) :
    μ = ν := by
  let D : Set ℝ :=
    {x : ℝ |
      ContinuousAt (fun y : ℝ => measureCdf μ y) x ∧
      ContinuousAt (fun y : ℝ => measureCdf ν y) x}
  let C : Set (Set ℝ) :=
    {S : Set ℝ | ∃ᵉ (l ∈ D) (u ∈ D), l < u ∧ Ioc l u = S}
  have hD : Dense D := dense_common_measureCdf_continuity μ ν
  refine MeasureTheory.ext_of_generate_finite C
    (BorelSpace.measurable_eq.trans hD.borel_eq_generateFrom_Ioc_mem)
    (isPiSystem_Ioc_mem D D) ?_ ?_
  · rintro S ⟨a, haD, b, hbD, hab, rfl⟩
    exact
      measure_Ioc_eq_of_measureReal_Ioo_eq_of_common_continuity μ ν hab
        (hIoo hab haD.1 hbD.1 haD.2 hbD.2) hbD.1 hbD.2
  · simp



theorem probability_law_eq_of_charFun_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hchar : charFun μ = charFun ν) :
    μ = ν := by
  have _hinversionSpine :
      ∀ ⦃a b : ℝ⦄, a < b →
        characteristicInversionMass μ a b =
          characteristicInversionMass ν a b := by
    intro a b hab
    exact characteristicInversionMass_eq_of_charFun_eq μ ν hchar hab
  have _hIntervalsAtCommonContinuity :
      ∀ ⦃a b : ℝ⦄, a < b →
        ContinuousAt (fun x : ℝ => measureCdf μ x) a →
        ContinuousAt (fun x : ℝ => measureCdf μ x) b →
        ContinuousAt (fun x : ℝ => measureCdf ν x) a →
        ContinuousAt (fun x : ℝ => measureCdf ν x) b →
        μ.real (Ioo a b) = ν.real (Ioo a b) := by
    intro a b hab haμ hbμ haν hbν
    exact
      measureReal_Ioo_eq_of_charFun_eq_of_common_continuity
        μ ν hchar hab haμ hbμ haν hbν
  have hmeasure : μ = ν :=
    measure_eq_of_measureReal_Ioo_eq_of_common_continuity
      μ ν _hIntervalsAtCommonContinuity
  have hcdf : ∀ x : ℝ, μ (Iic x) = ν (Iic x) := by
    intro x
    rw [hmeasure]
  exact sameDistribution_of_cdf_eq μ ν hcdf

 
theorem sameDistribution_of_characteristicFunction_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hφ : ∀ t : ℝ, characteristicFunction (P.map X) t =
      characteristicFunction (P.map Y) t) :
    SameDistribution P X Y := by
  haveI : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hX
  haveI : IsProbabilityMeasure (P.map Y) :=
    Measure.isProbabilityMeasure_map hY
  have hLawChar : charFun (P.map X) = charFun (P.map Y) := by
    funext t
    rw [← characteristicFunction_eq_charFun_map (P := P) (X := X) hX t]
    rw [← characteristicFunction_eq_charFun_map (P := P) (X := Y) hY t]
    exact hφ t
  exact ⟨hX, hY,
    probability_law_eq_of_charFun_eq (P.map X) (P.map Y) hLawChar⟩

 
theorem thm_9_6
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hφ : ∀ t : ℝ, characteristicFunction (P.map X) t =
      characteristicFunction (P.map Y) t) :
    SameDistribution P X Y :=
  sameDistribution_of_characteristicFunction_eq hX hY hφ
