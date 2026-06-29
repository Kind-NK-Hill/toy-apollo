/-
TASK ID: ex_2_4_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_2_7

open Set
open scoped Classical

noncomputable section

inductive SixPoint
  | a | b | c | d | e | f
  deriving DecidableEq, Repr

open SixPoint

instance : Fintype SixPoint where
  elems := {a, b, c, d, e, f}
  complete := by
    intro x
    cases x <;> simp

def A1 : Set SixPoint := {a, b, c}
def A2 : Set SixPoint := {c, d, e}

def atomAB : Set SixPoint := {a, b}
def atomC : Set SixPoint := {c}
def atomDE : Set SixPoint := {d, e}
def atomF : Set SixPoint := {f}

def generatingAtoms : Finset (Set SixPoint) :=
  {atomAB, atomC, atomDE, atomF}

def generatedMembers : Finset (Set SixPoint) :=
  { (∅ : Set SixPoint),
    Set.univ,
    A1,
    A1ᶜ,
    A2,
    A2ᶜ,
    ({a, b, c, d, e} : Set SixPoint),
    ({f} : Set SixPoint),
    ({c} : Set SixPoint),
    ({a, b, d, e, f} : Set SixPoint),
    ({a, b, c, f} : Set SixPoint),
    ({d, e} : Set SixPoint),
    ({a, b} : Set SixPoint),
    ({c, d, e, f} : Set SixPoint),
    ({a, b, d, e} : Set SixPoint),
    ({c, f} : Set SixPoint) }

structure FiniteGeneratedSigmaFieldExample where
  sampleSpace : Set SixPoint
  generators : Finset (Set SixPoint)
  atoms : Finset (Set SixPoint)
  generatedMembers : Finset (Set SixPoint)

def ex_2_4_1 : FiniteGeneratedSigmaFieldExample where
  sampleSpace := Set.univ
  generators := {A1, A2}
  atoms := generatingAtoms
  generatedMembers := generatedMembers

theorem ex_2_4_1_generators_mem :
    A1 ∈ ex_2_4_1.generatedMembers ∧ A2 ∈ ex_2_4_1.generatedMembers := by
  simp [ex_2_4_1, generatedMembers]

theorem ex_2_4_1_symmDiff_mem :
    ({a, b, d, e} : Set SixPoint) ∈ ex_2_4_1.generatedMembers := by
  simp [ex_2_4_1, generatedMembers]
