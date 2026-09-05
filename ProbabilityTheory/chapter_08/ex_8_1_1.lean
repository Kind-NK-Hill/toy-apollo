/-
TASK ID: ex_8_1_1
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators ENNReal
open ProbabilityTheory

 
def dieToBernoulli : Fin 6 → Bool :=
  fun i => 4 ≤ i.1

 
noncomputable def fairDiePMF : PMF (Fin 6) :=
  PMF.uniformOfFintype (Fin 6)

 
noncomputable def dieBernoulliPMF : PMF Bool :=
  fairDiePMF.map dieToBernoulli

 
noncomputable def dieBernoulliJointPMF : PMF (Fin 6 × Bool) :=
  fairDiePMF.map fun i => (i, dieToBernoulli i)

 
structure PMFDeterministicCoupling {alpha beta : Type*}
    (source : PMF alpha) (target : PMF beta) where
  transport : alpha → beta
  map_eq : source.map transport = target

 
theorem fairDiePMF_apply (i : Fin 6) :
    fairDiePMF i = (1 / 6 : ℝ≥0∞) := by
  simp [fairDiePMF, PMF.uniformOfFintype_apply]

 
theorem fairDiePMF_total_mass :
    ∑' i, fairDiePMF i = 1 :=
  PMF.tsum_coe fairDiePMF

 
theorem dieBernoulliPMF_false :
    dieBernoulliPMF false = (2 / 3 : ℝ≥0∞) := by
  rw [dieBernoulliPMF, PMF.map_apply, tsum_fintype]
  norm_num [fairDiePMF, PMF.uniformOfFintype_apply,
    dieToBernoulli, Fin.sum_univ_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

 
theorem dieBernoulliPMF_true :
    dieBernoulliPMF true = (1 / 3 : ℝ≥0∞) := by
  rw [dieBernoulliPMF, PMF.map_apply, tsum_fintype]
  norm_num [fairDiePMF, PMF.uniformOfFintype_apply,
    dieToBernoulli, Fin.sum_univ_succ]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (by norm_num) ((ENNReal.inv_ne_top).2 (by norm_num)))
    (by simp)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

 
theorem dieBernoulliJointPMF_total_mass :
    ∑' z, dieBernoulliJointPMF z = 1 :=
  PMF.tsum_coe dieBernoulliJointPMF

 
theorem dieBernoulliJoint_fst :
    dieBernoulliJointPMF.map Prod.fst = fairDiePMF := by
  rw [dieBernoulliJointPMF, PMF.map_comp]
  have hcomp :
      (Prod.fst ∘ fun i : Fin 6 => (i, dieToBernoulli i)) = id := by
    funext i
    rfl
  rw [hcomp, PMF.map_id]

 
theorem dieBernoulliJoint_snd :
    dieBernoulliJointPMF.map Prod.snd = dieBernoulliPMF := by
  rw [dieBernoulliJointPMF, PMF.map_comp]
  have hcomp :
      (Prod.snd ∘ fun i : Fin 6 => (i, dieToBernoulli i)) =
        dieToBernoulli := by
    funext i
    rfl
  rw [hcomp]
  rfl

 
noncomputable def ex_8_1_1 :
    PMFDeterministicCoupling fairDiePMF dieBernoulliPMF where
  transport := dieToBernoulli
  map_eq := rfl
