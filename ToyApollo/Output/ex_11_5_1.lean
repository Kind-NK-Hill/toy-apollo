/-
TASK ID: ex_11_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_11_5
import ToyApollo.Output.thm_11_8

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory

noncomputable section

def empiricalCDFIndicator {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => if X k ω ≤ x then 1 else 0

def empiricalCDFAt {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) : Ω → ℝ :=
  thm_11_5_sampleMean (fun k => empiricalCDFIndicator X x k) n

theorem ex_11_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hInt : Integrable (empiricalCDFIndicator X x 0) P)
    (hpairwise :
      Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j)
    (hident :
      ∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P)
    (hmean : P[empiricalCDFIndicator X x 0] = F x) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ => F x) := by
  simpa [empiricalCDFAt] using
    thm_11_8 P (fun k => empiricalCDFIndicator X x k) (F x)
      hInt hpairwise hident hmean
