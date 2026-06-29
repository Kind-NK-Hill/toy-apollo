/-
TASK ID: ex_8_1_1
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Finset

def dieToBernoulli : Fin 6 → Bool :=
  fun i => 4 ≤ i.1

structure BernoulliByDieDeterministicCoupling where
  transport : Fin 6 → Bool
  zeroCount : (Finset.univ.filter fun i => transport i = false).card = 4
  oneCount : (Finset.univ.filter fun i => transport i = true).card = 2
  probZero : ℚ
  probOne : ℚ
  probZero_eq : probZero = 2 / 3
  probOne_eq : probOne = 1 / 3

noncomputable def ex_8_1_1 : BernoulliByDieDeterministicCoupling where
  transport := dieToBernoulli
  zeroCount := by native_decide
  oneCount := by native_decide
  probZero := 2 / 3
  probOne := 1 / 3
  probZero_eq := rfl
  probOne_eq := rfl
