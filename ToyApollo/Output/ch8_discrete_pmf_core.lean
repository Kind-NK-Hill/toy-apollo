import Mathlib

open Real
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section

namespace Ch8DiscretePMFCore

/-- The Poisson PMF as a real-valued function on `ℕ`. -/
def Poi (lam : ℝ) (k : ℕ) : ℝ :=
  exp (-lam) * lam ^ k / (k.factorial : ℝ)

/-- Bernoulli PMF as a real-valued function on `ℕ`. -/
def Ber (p : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - p
  else if k = 1 then p
  else 0

/-- Bernoulli law on `ℕ`, obtained by mapping `true ↦ 1` and `false ↦ 0`. -/
noncomputable def bernoulliNatPMF (lam : NNReal) (hlam : lam ≤ 1) : PMF ℕ :=
  (PMF.bernoulli lam hlam).map fun b : Bool => if b then 1 else 0

lemma bernoulliNatPMF_zero (lam : NNReal) (hlam : lam ≤ 1) :
    ((bernoulliNatPMF lam hlam) 0).toReal = 1 - (lam : ℝ) := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  norm_num [PMF.bernoulli_apply, hlam]

lemma bernoulliNatPMF_one (lam : NNReal) (hlam : lam ≤ 1) :
    ((bernoulliNatPMF lam hlam) 1).toReal = (lam : ℝ) := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  norm_num [PMF.bernoulli_apply, hlam]

lemma bernoulliNatPMF_ge_two (lam : NNReal) (hlam : lam ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    ((bernoulliNatPMF lam hlam) n).toReal = 0 := by
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  simp [PMF.bernoulli_apply, hlam, hne0, hne1]

lemma poissonPMF_toReal (lam : NNReal) (n : ℕ) :
    ((ProbabilityTheory.poissonPMF lam) n).toReal = ProbabilityTheory.poissonPMFReal lam n := by
  symm
  simpa [ProbabilityTheory.poissonPMFReal_nonneg] using
    congrArg ENNReal.toReal (ProbabilityTheory.poissonPMFReal_ofReal_eq_poissonPMF lam n)

lemma bernoulliNatPMF_toReal_eq_Ber (lam : NNReal) (hlam : lam ≤ 1) :
    (fun n => ((bernoulliNatPMF lam hlam) n).toReal) = Ber (lam : ℝ) := by
  funext n
  rcases n with (_ | n)
  · simp [Ber, bernoulliNatPMF_zero, hlam]
  · rcases n with (_ | n)
    · simp [Ber, bernoulliNatPMF_one, hlam]
    · have hge : 2 ≤ n.succ.succ := by omega
      simp [Ber, bernoulliNatPMF_ge_two lam hlam hge]

lemma poissonPMF_toReal_eq_Poi (lam : NNReal) :
    (fun n => ((ProbabilityTheory.poissonPMF lam) n).toReal) = Poi (lam : ℝ) := by
  funext n
  rw [poissonPMF_toReal]
  simp [Poi, ProbabilityTheory.poissonPMFReal, mul_comm, mul_left_comm, mul_assoc]

end Ch8DiscretePMFCore

end
