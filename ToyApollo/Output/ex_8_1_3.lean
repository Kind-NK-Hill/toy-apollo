/-
TASK ID: ex_8_1_3
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_1
import ToyApollo.Output.def_8_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

noncomputable def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

noncomputable instance : IsProbabilityMeasure unitIntervalMeasure := by
  refine ⟨?_⟩
  simp [unitIntervalMeasure, Real.volume_Icc]

noncomputable abbrev mapUnitIntervalIsProbabilityMeasure
    (f : ℝ → ℝ) (hf : Measurable f) :
    IsProbabilityMeasure (Measure.map f unitIntervalMeasure) := by
  refine ⟨?_⟩
  rw [Measure.map_apply hf MeasurableSet.univ]
  simpa using (IsProbabilityMeasure.measure_univ (μ := unitIntervalMeasure))

noncomputable abbrev inverseCDFCoupling
    (F₁Inv F₂Inv : ℝ → ℝ)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    Coupling P Q := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  exact
    { Ω := ℝ
      instMeasurableSpaceΩ := inferInstance
      μ := unitIntervalMeasure
      instIsProbabilityMeasureμ := inferInstance
      X := F₁Inv
      Y := F₂Inv
      measurable_X := hF₁Inv_meas
      measurable_Y := hF₂Inv_meas
      map_X := rfl
      map_Y := rfl }

structure CouplingMorphism
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  toFun : π.Ω → π'.Ω
  measurable_toFun : Measurable toFun
  comm_X : π.X = π'.X ∘ toFun
  comm_Y : π.Y = π'.Y ∘ toFun
  map_μ : Measure.map toFun π.μ = π'.μ

structure EquivalentCouplings
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  forward : CouplingMorphism π π'
  backward : CouplingMorphism π' π
  left_inv_ae : ∀ᵐ ω ∂π.μ, backward.toFun (forward.toFun ω) = ω
  right_inv_ae : ∀ᵐ ω' ∂π'.μ, forward.toFun (backward.toFun ω') = ω'

noncomputable abbrev inverseCDFDeterministicCoupling
    (F₁ F₁Inv F₂Inv : ℝ → ℝ)
    (hF₁_meas : Measurable F₁)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv)
    (hRightInv₁ : ∀ u ∈ Icc (0 : ℝ) 1, F₁ (F₁Inv u) = u) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    DeterministicCoupling P Q := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  exact
  { toCoupling :=
      { Ω := ℝ
        instMeasurableSpaceΩ := inferInstance
        μ := Measure.map F₁Inv unitIntervalMeasure
        instIsProbabilityMeasureμ := inferInstance
        X := id
        Y := F₂Inv ∘ F₁
        measurable_X := measurable_id
        measurable_Y := hF₂Inv_meas.comp hF₁_meas
        map_X := Measure.map_id
        map_Y := by
          have hAe :
              (F₁ ∘ F₁Inv) =ᵐ[unitIntervalMeasure] id := by
            refine (ae_restrict_iff' measurableSet_Icc).2 ?_
            filter_upwards with u hu
            exact hRightInv₁ u hu
          have hAeComp :
              (fun u => F₂Inv (F₁ (F₁Inv u))) =ᵐ[unitIntervalMeasure] F₂Inv := by
            simpa [Function.comp] using hAe.fun_comp F₂Inv
          calc
            Measure.map (F₂Inv ∘ F₁) (Measure.map F₁Inv unitIntervalMeasure)
                = Measure.map (fun u => F₂Inv (F₁ (F₁Inv u))) unitIntervalMeasure := by
                    simpa [Function.comp] using
                      (Measure.map_map (g := F₂Inv ∘ F₁) (f := F₁Inv)
                        (μ := unitIntervalMeasure) (hg := hF₂Inv_meas.comp hF₁_meas)
                        (hf := hF₁Inv_meas))
            _ = Measure.map F₂Inv unitIntervalMeasure := Measure.map_congr hAeComp
      }
    T := F₂Inv ∘ F₁
    measurable_T := hF₂Inv_meas.comp hF₁_meas
    Y_eq_transport := by
      ext x
      rfl }

theorem ex_8_1_3
    {F₁ F₁Inv F₂Inv : ℝ → ℝ}
    (hF₁_meas : Measurable F₁)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv)
    (hRightInv₁ : ∀ u ∈ Icc (0 : ℝ) 1, F₁ (F₁Inv u) = u) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    ∃ δ : DeterministicCoupling.{0, 0, 0} P Q, δ.T = F₂Inv ∘ F₁ := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  let δ :
      DeterministicCoupling.{0, 0, 0}
        (Measure.map F₁Inv unitIntervalMeasure)
        (Measure.map F₂Inv unitIntervalMeasure) := by
    simpa using
      inverseCDFDeterministicCoupling F₁ F₁Inv F₂Inv hF₁_meas hF₁Inv_meas hF₂Inv_meas hRightInv₁
  exact ⟨δ, rfl⟩
