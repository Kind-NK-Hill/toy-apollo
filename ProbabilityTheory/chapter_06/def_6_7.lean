/-
TASK ID: def_6_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_06.def_6_5








open MeasureTheory

namespace Def67Support

noncomputable abbrev textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  _root_.textbookIntegral P X

end Def67Support





noncomputable def expectation {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

 
noncomputable def def_6_7 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  expectation P X
