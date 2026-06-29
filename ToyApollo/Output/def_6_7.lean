/-
TASK ID: def_6_7
TYPE: Definition
SOURCE PLAN: 22_chap6_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Def67Support

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂P

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂P

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  if posLIntegral P X = ⊤ ∧ negLIntegral P X = ⊤ then
    none
  else
    some ((posLIntegral P X : EReal) - (negLIntegral P X : EReal))

end Def67Support

noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

noncomputable def def_6_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  expectation P X
