import Mathlib

/-
TASK ID: thm_13_5
TYPE: Theorem_Statement
SOURCE PLAN: chapter13-properties
TASK CONTENT:
\begin{thmbox}{13.5 (Radon-Nikodym)}
\end{thmbox}

Let. \mathcal{G}be a sub-\sigma-field of. \mathcal{F}Suppose. \nu and. \mu are\sigma-finite measures such that

\nu\ll \mu Then there exists a nonnegative \mathcal{G}-measurable function f such that

\nu(B)=

\int

B fd \mu for all B\in \mathcal{G}The function f is unique in the sense that if

g is another\mathcal{G}-measurable function with the same property, then g is equal to

f \mu-almost everywhere.

The function f is called the density or the Radon-Nikodym derivative of

\nu with respect to. \mu. It is represented by the symbol d\nu

d\mu .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The Radon-Nikodym density is measurable. The codomain `ℝ≥0∞`
records the textbook nonnegativity directly. -/
theorem thm_13_5_density_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) : Measurable (ν.rnDeriv μ) :=
  Measure.measurable_rnDeriv ν μ

/-- Under the textbook sigma-finiteness hypothesis on `ν`, the density is
finite `μ`-almost everywhere. -/
theorem thm_13_5_density_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] : ∀ᵐ ω ∂μ, ν.rnDeriv μ ω ≠ ∞ :=
  Measure.rnDeriv_ne_top ν μ

/-- Radon-Nikodym in measure form: if `ν ≪ μ`, then `ν` is obtained by
putting the density `dν/dμ` against `μ`. -/
theorem thm_13_5_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hνμ

/-- The setwise integral formula in Theorem 13.5. -/
theorem thm_13_5_set_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ)
    {B : Set Ω} (hB : MeasurableSet B) :
    ν B = ∫⁻ ω in B, ν.rnDeriv μ ω ∂μ := by
  calc
    ν B = (μ.withDensity (ν.rnDeriv μ)) B := by
      rw [thm_13_5_withDensity ν μ hνμ]
    _ = ∫⁻ ω in B, ν.rnDeriv μ ω ∂μ := withDensity_apply (ν.rnDeriv μ) hB

/-- Full existence and uniqueness form of Theorem 13.5 on the current
measurable space. When that measurable space is the sub-sigma-field `𝒢`,
this is exactly the textbook statement over sets `B ∈ 𝒢`. -/
theorem thm_13_5 {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ) :
    ∃ f : Ω → ℝ≥0∞,
      Measurable f ∧
        (∀ᵐ ω ∂μ, f ω ≠ ∞) ∧
          (∀ ⦃B : Set Ω⦄, MeasurableSet B → ν B = ∫⁻ ω in B, f ω ∂μ) ∧
            ∀ g : Ω → ℝ≥0∞,
              Measurable g →
                (∀ ⦃B : Set Ω⦄, MeasurableSet B → ν B = ∫⁻ ω in B, g ω ∂μ) →
                  g =ᵐ[μ] f := by
  refine ⟨ν.rnDeriv μ, thm_13_5_density_measurable ν μ,
    thm_13_5_density_ne_top ν μ, ?_, ?_⟩
  · intro B hB
    exact thm_13_5_set_lintegral ν μ hνμ hB
  · intro g hg hg_integrals
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg
      (thm_13_5_density_measurable ν μ) ?_
    intro B hB _hB_finite
    rw [← hg_integrals hB, ← thm_13_5_set_lintegral ν μ hνμ hB]
