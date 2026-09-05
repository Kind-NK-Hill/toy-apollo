/-
TASK ID: ex_12_4_3
TYPE: Example_Proof
SOURCE PLAN: chapter12-mmse-estimation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

noncomputable section

 
inductive ex_12_4_3_Ω where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype

open ex_12_4_3_Ω

 
def ex_12_4_3_X : ex_12_4_3_Ω → ℝ
  | a => 1
  | b => 1
  | c => 2
  | d => 2

 
def ex_12_4_3_Y : ex_12_4_3_Ω → ℝ
  | a => 1
  | b => 2
  | c => 3
  | d => 4

 
def ex_12_4_3_uniformExpectation (Z : ex_12_4_3_Ω → ℝ) : ℝ :=
  (Z a + Z b + Z c + Z d) / 4

 
def ex_12_4_3_atomAB (ω : ex_12_4_3_Ω) : Prop :=
  ω = a ∨ ω = b

 
def ex_12_4_3_atomCD (ω : ex_12_4_3_Ω) : Prop :=
  ω = c ∨ ω = d

 
def ex_12_4_3_indicatorAB : ex_12_4_3_Ω → ℝ
  | a => 1
  | b => 1
  | c => 0
  | d => 0

 
def ex_12_4_3_indicatorCD : ex_12_4_3_Ω → ℝ
  | a => 0
  | b => 0
  | c => 1
  | d => 1

 
def ex_12_4_3_estimator (α β : ℝ) : ex_12_4_3_Ω → ℝ
  | a => α
  | b => α
  | c => β
  | d => β

 
def ex_12_4_3_g (x : ℝ) : ℝ :=
  if x = 1 then (3 / 2 : ℝ) else if x = 2 then (7 / 2 : ℝ) else 0

 
def ex_12_4_3_mse (α β : ℝ) : ℝ :=
  ex_12_4_3_uniformExpectation
    (fun ω => (ex_12_4_3_Y ω - ex_12_4_3_estimator α β ω) ^ 2)

 
def ex_12_4_3_objective (α β : ℝ) : ℝ :=
  ((1 - α) ^ 2 + (2 - α) ^ 2 + (3 - β) ^ 2 + (4 - β) ^ 2) / 4

theorem ex_12_4_3_X_eq_one_iff (ω : ex_12_4_3_Ω) :
    ex_12_4_3_X ω = 1 ↔ ex_12_4_3_atomAB ω := by
  cases ω <;> simp [ex_12_4_3_X, ex_12_4_3_atomAB]

theorem ex_12_4_3_X_eq_two_iff (ω : ex_12_4_3_Ω) :
    ex_12_4_3_X ω = 2 ↔ ex_12_4_3_atomCD ω := by
  cases ω <;> simp [ex_12_4_3_X, ex_12_4_3_atomCD]

theorem ex_12_4_3_mse_eq_objective (α β : ℝ) :
    ex_12_4_3_mse α β = ex_12_4_3_objective α β := by
  unfold ex_12_4_3_mse ex_12_4_3_uniformExpectation ex_12_4_3_objective
    ex_12_4_3_Y ex_12_4_3_estimator
  ring

theorem ex_12_4_3_objective_sub_min (α β : ℝ) :
    ex_12_4_3_objective α β - ex_12_4_3_objective (3 / 2) (7 / 2) =
      (α - 3 / 2) ^ 2 / 2 + (β - 7 / 2) ^ 2 / 2 := by
  unfold ex_12_4_3_objective
  ring

theorem ex_12_4_3_objective_minimal (α β : ℝ) :
    ex_12_4_3_objective (3 / 2) (7 / 2) ≤ ex_12_4_3_objective α β := by
  have h := ex_12_4_3_objective_sub_min α β
  nlinarith [sq_nonneg (α - 3 / 2), sq_nonneg (β - 7 / 2)]

theorem ex_12_4_3_mse_minimal (α β : ℝ) :
    ex_12_4_3_mse (3 / 2) (7 / 2) ≤ ex_12_4_3_mse α β := by
  simpa [ex_12_4_3_mse_eq_objective] using ex_12_4_3_objective_minimal α β

theorem ex_12_4_3_E_Y_indicatorAB :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorAB ω) = 3 / 4 := by
  norm_num [ex_12_4_3_uniformExpectation, ex_12_4_3_Y, ex_12_4_3_indicatorAB]

theorem ex_12_4_3_E_estimator_indicatorAB (α β : ℝ) :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorAB ω) = α / 2 := by
  unfold ex_12_4_3_uniformExpectation ex_12_4_3_estimator ex_12_4_3_indicatorAB
  ring

theorem ex_12_4_3_alpha_of_atomAB_equation (α β : ℝ)
    (h :
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorAB ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorAB ω)) :
    α = 3 / 2 := by
  rw [ex_12_4_3_E_Y_indicatorAB, ex_12_4_3_E_estimator_indicatorAB] at h
  nlinarith

theorem ex_12_4_3_E_Y_indicatorCD :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorCD ω) = 7 / 4 := by
  norm_num [ex_12_4_3_uniformExpectation, ex_12_4_3_Y, ex_12_4_3_indicatorCD]

theorem ex_12_4_3_E_estimator_indicatorCD (α β : ℝ) :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorCD ω) = β / 2 := by
  unfold ex_12_4_3_uniformExpectation ex_12_4_3_estimator ex_12_4_3_indicatorCD
  ring

theorem ex_12_4_3_beta_of_atomCD_equation (α β : ℝ)
    (h :
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorCD ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorCD ω)) :
    β = 7 / 2 := by
  rw [ex_12_4_3_E_Y_indicatorCD, ex_12_4_3_E_estimator_indicatorCD] at h
  nlinarith

theorem ex_12_4_3_orthogonal_principle_values (α β : ℝ)
    (hAB :
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorAB ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorAB ω))
    (hCD :
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorCD ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator α β ω * ex_12_4_3_indicatorCD ω)) :
    α = 3 / 2 ∧ β = 7 / 2 :=
  ⟨ex_12_4_3_alpha_of_atomAB_equation α β hAB,
    ex_12_4_3_beta_of_atomCD_equation α β hCD⟩

theorem ex_12_4_3_estimator_eq_g_comp_X :
    ex_12_4_3_estimator (3 / 2) (7 / 2) =
      fun ω => ex_12_4_3_g (ex_12_4_3_X ω) := by
  funext ω
  cases ω <;> norm_num [ex_12_4_3_estimator, ex_12_4_3_g, ex_12_4_3_X]

theorem ex_12_4_3_optimal_atomAB :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorAB ω) =
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_estimator (3 / 2) (7 / 2) ω *
        ex_12_4_3_indicatorAB ω) := by
  rw [ex_12_4_3_E_Y_indicatorAB, ex_12_4_3_E_estimator_indicatorAB]
  norm_num

theorem ex_12_4_3_optimal_atomCD :
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorCD ω) =
    ex_12_4_3_uniformExpectation
      (fun ω => ex_12_4_3_estimator (3 / 2) (7 / 2) ω *
        ex_12_4_3_indicatorCD ω) := by
  rw [ex_12_4_3_E_Y_indicatorCD, ex_12_4_3_E_estimator_indicatorCD]
  norm_num



theorem ex_12_4_3 :
    (∀ α β : ℝ, ex_12_4_3_mse (3 / 2) (7 / 2) ≤ ex_12_4_3_mse α β) ∧
      (ex_12_4_3_estimator (3 / 2) (7 / 2) =
        fun ω => ex_12_4_3_g (ex_12_4_3_X ω)) ∧
      (ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorAB ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator (3 / 2) (7 / 2) ω *
          ex_12_4_3_indicatorAB ω)) ∧
      (ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_Y ω * ex_12_4_3_indicatorCD ω) =
      ex_12_4_3_uniformExpectation
        (fun ω => ex_12_4_3_estimator (3 / 2) (7 / 2) ω *
          ex_12_4_3_indicatorCD ω)) := by
  constructor
  · exact fun α β => ex_12_4_3_mse_minimal α β
  constructor
  · exact ex_12_4_3_estimator_eq_g_comp_X
  constructor
  · exact ex_12_4_3_optimal_atomAB
  · exact ex_12_4_3_optimal_atomCD
