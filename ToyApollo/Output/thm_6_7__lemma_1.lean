import Mathlib
import ToyApollo.Output.def_6_5
import ToyApollo.Output.def_6_6
import ToyApollo.Output.def_6_7
import ToyApollo.Output.thm_6_6
import ToyApollo.Output.thm_6_7
import ToyApollo.Output.ex_6_4_1

/-
TASK ID: thm_6_7__lemma_1
TYPE: Theorem_with_Proof
SOURCE PLAN: 46_chap6_expectation_integral_translation
TASK CONTENT:
\begin{thmbox}{6.7 Translation}
This translation records the stable interface between the Chapter 6 textbook definitions of real Lebesgue integral and expectation, and the standard Mathlib Bochner integral interface. It should not introduce a new expectation or integral definition. It should only re-export or wrap the existing translation facts from Definition 6.5, Definition 6.7, Theorem 6.7, and Example 6.4.1 so later chapters can move from textbook notation such as $E[X]$ to Mathlib notation such as $\int \omega, X\,\omega\,\partial P$.
\end{thmbox}

\textit{Implementation rule.} Reuse `def_6_5.textbookIntegral`, `def_6_5.textbookIntegrable`, `def_6_7.expectation`, `thm_6_7` support lemmas, and `ex_6_4_1.expectation_eq_textbookIntegral`. Do not define a new expectation, a new integral, or another local copy of `textbookIntegrable`.
-/

-- WRITE FINAL LEAN CODE BELOW

universe u

/-
Source proof spine:
1. `chapter6_expectation_eq_textbookIntegral` re-exports the Definition 6.7
   expectation-as-textbook-integral identity from Example 6.4.1.
2. `chapter6_textbookIntegral_eq_integral` and `chapter6_expectation_eq_integral`
   expose the Theorem 6.7 real-integral-to-Bochner-integral bridge.
3. `chapter6_mathlib_integrable_to_textbookIntegrable` and
   `chapter6_expectation_real_eq_integral` provide the downstream real-valued
   `E[X]` to Mathlib `integral` translation.
4. `chapter6_complexTextbookIntegral_eq_integral` provides the complex-valued
   analogue through the existing Chapter 6 support lemma.
-/

theorem chapter6_expectation_eq_textbookIntegral
    {Ω : Type u} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → EReal) :
    expectation P X = textbookIntegral P X :=
  expectation_eq_textbookIntegral P X

theorem thm_6_7__lemma_1
    {Ω : Type u} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → EReal) :
    expectation P X = textbookIntegral P X :=
  chapter6_expectation_eq_textbookIntegral P X

theorem chapter6_textbookIntegral_eq_integral
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {X : Ω → EReal}
    (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    textbookIntegral μ X = some (Real.toEReal (∫ ω, (X ω).toReal ∂μ)) :=
  Thm67Support.textbookIntegral_eq_some_toRealIntegral hXm hX

theorem chapter6_expectation_eq_integral
    {Ω : Type u} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {X : Ω → EReal}
    (hXm : Measurable X) (hX : textbookIntegrable P X) :
    expectation P X = some (Real.toEReal (∫ ω, (X ω).toReal ∂P)) := by
  rw [chapter6_expectation_eq_textbookIntegral]
  exact chapter6_textbookIntegral_eq_integral hXm hX

theorem chapter6_mathlib_integrable_to_textbookIntegrable
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {f : Ω → ℝ}
    (hfm : Measurable f) (hf : MeasureTheory.Integrable f μ) :
    textbookIntegrable μ (fun ω => (f ω : EReal)) :=
  Thm67Support.textbookIntegrable_realCoe_of_integrable hfm hf

theorem chapter6_expectation_real_eq_integral
    {Ω : Type u} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {f : Ω → ℝ}
    (hfm : Measurable f) (hf : MeasureTheory.Integrable f P) :
    expectation P (fun ω => (f ω : EReal)) =
      some (Real.toEReal (∫ ω, f ω ∂P)) := by
  have hTextbook :
      textbookIntegrable P (fun ω => (f ω : EReal)) :=
    chapter6_mathlib_integrable_to_textbookIntegrable hfm hf
  have hfmE : Measurable (fun ω => (f ω : EReal)) := hfm.coe_real_ereal
  simpa using
    (chapter6_expectation_eq_integral
      (P := P) (X := fun ω => (f ω : EReal)) hfmE hTextbook)

theorem chapter6_complexTextbookIntegral_eq_integral
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {Z : Ω → ℂ}
    (hZm : Measurable Z) (hZ : complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) :=
  Thm67Support.complexTextbookIntegral_eq_some_integral hZm hZ
