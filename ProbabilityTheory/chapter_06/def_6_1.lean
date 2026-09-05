/-
TASK ID: def_6_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.SimpleFunc









open MeasureTheory
open scoped BigOperators



abbrev SimpleFunction (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  MeasureTheory.SimpleFunc Ω EReal

 
def def_6_1 (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  SimpleFunction Ω

namespace SimpleFunction

variable {Ω : Type*} [MeasurableSpace Ω]

 
theorem measurable_of_simpleFunction (X : SimpleFunction Ω) : Measurable X :=
  MeasureTheory.SimpleFunc.measurable X

 
theorem finite_range_of_simpleFunction (X : SimpleFunction Ω) : (Set.range X).Finite :=
  MeasureTheory.SimpleFunc.finite_range X

 
theorem measurableSet_fiber (X : SimpleFunction Ω) (x : EReal) :
    MeasurableSet (X ⁻¹' {x}) := by
  exact X.measurable (measurableSet_singleton x)

 
theorem setOf_eq_eq_preimage (X : SimpleFunction Ω) (x : EReal) :
    {ω | X ω = x} = X ⁻¹' {x} := by
  ext ω
  simp

 
theorem disjoint_fiber_of_ne (X : SimpleFunction Ω) {x y : EReal}
  (hxy : x ≠ y) :
    Disjoint (X ⁻¹' {x}) (X ⁻¹' {y}) := by
  refine Set.disjoint_left.2 ?_
  intro ω hx hy
  exact hxy <| by
    have hx' : X ω = x := by simpa using hx
    have hy' : X ω = y := by simpa using hy
    exact hx'.symm.trans hy'

 
theorem iUnion_fiber_range (X : SimpleFunction Ω) :
    (⋃ x ∈ X.range, X ⁻¹' ({x} : Set EReal)) = Set.univ := by
  ext ω
  simp



theorem sum_indicator_fiber (X : SimpleFunction Ω) :
    X = fun ω => ∑ x ∈ X.range, Set.indicator (X ⁻¹' ({x} : Set EReal)) (fun _ => x) ω := by
  classical
  funext ω
  rw [Finset.sum_eq_single (X ω)]
  · simp [Set.indicator_of_mem]
  · intro y hy hy_ne
    have hω : ω ∉ X ⁻¹' ({y} : Set EReal) := by
      intro h_mem
      exact hy_ne ((by simpa using h_mem) : X ω = y).symm
    simp [Set.indicator_of_notMem, hω]
  · intro h_not_mem
    exact (h_not_mem (X.mem_range_self ω)).elim

 
theorem map_fst_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.fst = X := by
  simp [MeasureTheory.SimpleFunc.map_fst_pair X Y]

 
theorem map_snd_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.snd = Y := by
  simp [MeasureTheory.SimpleFunc.map_snd_pair X Y]

 
theorem add_eq_map_pair (X Y : SimpleFunction Ω) :
    X + Y = (X.pair Y).map (fun p => p.1 + p.2) := by
  simpa using MeasureTheory.SimpleFunc.add_eq_map₂ X Y

end SimpleFunction
