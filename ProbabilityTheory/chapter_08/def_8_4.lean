/-
TASK ID: def_8_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions








open MeasureTheory



structure ContinuousPdfCoupling (fX fY : ℝ → ENNReal) where
  jointDensity : ℝ → ℝ → ENNReal
  totalMass : ∫⁻ p : ℝ × ℝ, jointDensity p.1 p.2 ∂(volume.prod volume) = 1
  marginal_X : ∀ x : ℝ, fX x = ∫⁻ y : ℝ, jointDensity x y ∂volume
  marginal_Y : ∀ y : ℝ, fY y = ∫⁻ x : ℝ, jointDensity x y ∂volume

 
structure DiscretePmfCoupling {α β : Type*} [Countable α] [Countable β]
    (pX : PMF α) (pY : PMF β) where
  jointPMF : PMF (α × β)
  marginal_X : jointPMF.map Prod.fst = pX
  marginal_Y : jointPMF.map Prod.snd = pY



def def_8_4 :=
  (ContinuousPdfCoupling, @DiscretePmfCoupling)
