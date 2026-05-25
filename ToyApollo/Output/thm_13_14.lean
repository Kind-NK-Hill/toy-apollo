/-
TASK ID: thm_13_14
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-continuous-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

def thm_13_14_X (z : ℝ × ℝ) : ℝ :=
  z.1

def thm_13_14_Y (z : ℝ × ℝ) : ℝ :=
  z.2

def thm_13_14_jointDensityLaw
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) : Prop :=
  ∀ B : Set (ℝ × ℝ), MeasurableSet B →
    P B = ∫⁻ z in B, ENNReal.ofReal (fXY z) ∂volume

def thm_13_14_marginalDensity (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, fXY (x, y) ∂volume

def thm_13_14_conditionalDensity
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  fXY (x, y) / thm_13_14_marginalDensity fXY y

def thm_13_14_conditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, g x * thm_13_14_conditionalDensity fXY x y ∂volume

def thm_13_14_identityConditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  thm_13_14_conditionalExpectationKernel fXY (fun x : ℝ => x) y

def thm_13_14_verticalCylinder (S : Set ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ S}

def thm_13_14_closedIntervalCylinder (a b : ℝ) : Set (ℝ × ℝ) :=
  thm_13_14_verticalCylinder (Set.Icc a b)

theorem thm_13_14_verticalCylinder_eq_prod (S : Set ℝ) :
    thm_13_14_verticalCylinder S = (Set.univ : Set ℝ) ×ˢ S := by
  ext z
  simp [thm_13_14_verticalCylinder]

theorem thm_13_14_closedIntervalCylinder_eq_prod (a b : ℝ) :
    thm_13_14_closedIntervalCylinder a b =
      (Set.univ : Set ℝ) ×ˢ (Set.Icc a b) := by
  rw [thm_13_14_closedIntervalCylinder, thm_13_14_verticalCylinder_eq_prod]

def thm_13_14_sigmaYMeasurableSet (C : Set (ℝ × ℝ)) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ C = thm_13_14_verticalCylinder S

def thm_13_14_integralIdentity
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) (C : Set (ℝ × ℝ)) : Prop :=
  (∫ z in C, g z.1 ∂P) = ∫ z in C, h z.2 ∂P

def thm_13_14_intervalFubiniSupport
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g
      (thm_13_14_conditionalExpectationKernel fXY g)
      (thm_13_14_closedIntervalCylinder a b)

def thm_13_14_piLambdaExtensionSupport
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g h
      (thm_13_14_closedIntervalCylinder a b)) →
    ∀ S : Set ℝ, MeasurableSet S →
      thm_13_14_integralIdentity P g h
        (thm_13_14_verticalCylinder S)

def thm_13_14_isConditionalExpectationVersion
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  ∀ C : Set (ℝ × ℝ), thm_13_14_sigmaYMeasurableSet C →
    thm_13_14_integralIdentity P g h C

theorem thm_13_14_marginalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) :
    thm_13_14_marginalDensity fXY y =
      ∫ x : ℝ, fXY (x, y) ∂volume := by
  rfl

theorem thm_13_14_conditionalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) :
    thm_13_14_conditionalDensity fXY x y =
      fXY (x, y) / thm_13_14_marginalDensity fXY y := by
  rfl

private theorem thm_13_14_from_intervalFubini_piLambda
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (_hDensity : thm_13_14_jointDensityLaw P fXY)
    (_hGMeas : Measurable g)
    (_hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P)
    (_hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0)
    (hIntervals : thm_13_14_intervalFubiniSupport P fXY g)
    (hExtend : thm_13_14_piLambdaExtensionSupport P g
      (thm_13_14_conditionalExpectationKernel fXY g)) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) := by
  intro C hC
  rcases hC with ⟨S, hS, rfl⟩
  exact hExtend hIntervals S hS

theorem thm_13_14
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0)
    (hIntervals : ∀ a b : ℝ, a ≤ b →
      thm_13_14_integralIdentity P g
        (thm_13_14_conditionalExpectationKernel fXY g)
        (thm_13_14_closedIntervalCylinder a b))
    (hExtend : (∀ a b : ℝ, a ≤ b →
      thm_13_14_integralIdentity P g
        (thm_13_14_conditionalExpectationKernel fXY g)
        (thm_13_14_closedIntervalCylinder a b)) →
      ∀ S : Set ℝ, MeasurableSet S →
        thm_13_14_integralIdentity P g
          (thm_13_14_conditionalExpectationKernel fXY g)
          (thm_13_14_verticalCylinder S)) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
  thm_13_14_from_intervalFubini_piLambda P fXY g
    hDensity hGMeas hGInt hFY_ne_zero hIntervals hExtend

theorem thm_13_14_identity
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hXMeas : Measurable (fun x : ℝ => x))
    (hXInt : Integrable (fun z : ℝ × ℝ => z.1) P)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0)
    (hIntervals : ∀ a b : ℝ, a ≤ b →
      thm_13_14_integralIdentity P (fun x : ℝ => x)
        (thm_13_14_identityConditionalExpectationKernel fXY)
        (thm_13_14_closedIntervalCylinder a b))
    (hExtend : (∀ a b : ℝ, a ≤ b →
      thm_13_14_integralIdentity P (fun x : ℝ => x)
        (thm_13_14_identityConditionalExpectationKernel fXY)
        (thm_13_14_closedIntervalCylinder a b)) →
      ∀ S : Set ℝ, MeasurableSet S →
        thm_13_14_integralIdentity P (fun x : ℝ => x)
          (thm_13_14_identityConditionalExpectationKernel fXY)
          (thm_13_14_verticalCylinder S)) :
    thm_13_14_isConditionalExpectationVersion P (fun x : ℝ => x)
      (thm_13_14_identityConditionalExpectationKernel fXY) :=
  thm_13_14 P fXY (fun x : ℝ => x)
    hDensity hXMeas hXInt hFY_ne_zero hIntervals hExtend
