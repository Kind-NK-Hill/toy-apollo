import ToyApollo.Output.prob_8_6_basic_support

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

-- ============================================================================
-- Part (a): mismatch events for sums
-- ============================================================================

/-- If two coordinatewise sums differ, then some coordinate must differ. -/
theorem prob_8_6_part_a_event_subset
    {Ω ι : Type*} [Fintype ι] (X Y : ι → Ω → ℕ) :
    {ω : Ω | (∑ i, X i ω) ≠ ∑ i, Y i ω} ⊆ ⋃ i, {ω : Ω | X i ω ≠ Y i ω} := by
  intro ω hω
  by_contra hmem
  have hcoord : ∀ i, X i ω = Y i ω := by
    intro i
    by_contra hxy
    exact hmem <| mem_iUnion.2 ⟨i, hxy⟩
  apply hω
  simp [hcoord]

/-- The mismatch probability of the sums is bounded by the sum of coordinate mismatch
probabilities. -/
theorem prob_8_6_part_a_measure_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : ι → Ω → ℕ) :
    μ.real {ω : Ω | (∑ i, X i ω) ≠ ∑ i, Y i ω}
      ≤ ∑ i, μ.real {ω : Ω | X i ω ≠ Y i ω} := by
  let mismatch : Set Ω := {ω : Ω | (∑ i, X i ω) ≠ ∑ i, Y i ω}
  let coord : ι → Set Ω := fun i => {ω : Ω | X i ω ≠ Y i ω}
  have hsubset : mismatch ⊆ ⋃ i, coord i := by
    simpa [mismatch, coord] using (prob_8_6_part_a_event_subset X Y)
  exact (MeasureTheory.measureReal_mono hsubset).trans <| by
    simpa [coord] using MeasureTheory.measureReal_iUnion_fintype_le (μ := μ) coord

/-- Turn a discrete-pmf coupling into a textbook-style coupling of the associated probability
measures. -/
noncomputable def discretePmfCouplingToCoupling
    {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {pX : PMF α} {pY : PMF β}
    (piC : DiscretePmfCoupling pX pY) :
    Coupling pX.toMeasure pY.toMeasure where
  Ω := α × β
  instMeasurableSpaceΩ := inferInstance
  μ := piC.jointPMF.toMeasure
  instIsProbabilityMeasureμ := inferInstance
  X := Prod.fst
  Y := Prod.snd
  measurable_X := measurable_fst
  measurable_Y := measurable_snd
  map_X := by
    calc
      Measure.map Prod.fst piC.jointPMF.toMeasure
          = (piC.jointPMF.map Prod.fst).toMeasure := by
              simpa using PMF.toMeasure_map Prod.fst piC.jointPMF measurable_fst
      _ = pX.toMeasure := by simpa [piC.marginal_X]
  map_Y := by
    calc
      Measure.map Prod.snd piC.jointPMF.toMeasure
          = (piC.jointPMF.map Prod.snd).toMeasure := by
              simpa using PMF.toMeasure_map Prod.snd piC.jointPMF measurable_snd
      _ = pY.toMeasure := by simpa [piC.marginal_Y]

/-- The mismatch mass of a discrete coupling, measured on the off-diagonal. -/
noncomputable def discretePmfCouplingMismatchMassENN
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {pX pY : PMF α} (piC : DiscretePmfCoupling pX pY) : ENNReal :=
  piC.jointPMF.toMeasure {xy : α × α | xy.1 ≠ xy.2}

/-- Real-valued version of the mismatch mass of a discrete coupling. -/
noncomputable def discretePmfCouplingMismatchMass
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {pX pY : PMF α} (piC : DiscretePmfCoupling pX pY) : ℝ :=
  (discretePmfCouplingMismatchMassENN piC).toReal

-- ============================================================================
-- Part (b): Bernoulli/Poisson TV-facing exports
-- ============================================================================

/-- Conditional probability of keeping the Bernoulli value at `0` given that the Poisson
coordinate is `0`. -/
noncomputable def berPoiStayAtZeroMass (lam : NNReal) : ENNReal :=
  ((1 - lam : NNReal) : ENNReal) / (ProbabilityTheory.poissonPMF lam 0)

lemma prob_8_6_poisson_zero_ge_ber_zero (lam : NNReal) :
    ((1 - lam : NNReal) : ENNReal) ≤ (ProbabilityTheory.poissonPMF lam 0) := by
  have hreal :
      (((1 - lam : NNReal) : ENNReal).toReal)
        ≤ (((ProbabilityTheory.poissonPMF lam 0)).toReal) := by
    rw [poissonPMF_toReal]
    by_cases hlam : lam ≤ 1
    · have hcast : (((1 - lam : NNReal) : ENNReal).toReal) = 1 - (lam : ℝ) := by
        simp [hlam]
      rw [hcast]
      simpa [ProbabilityTheory.poissonPMFReal] using Real.one_sub_le_exp_neg (lam : ℝ)
    · have hle : (1 : NNReal) ≤ lam := le_of_not_ge hlam
      have hzero : (((1 - lam : NNReal) : ENNReal).toReal) = 0 := by
        simp [tsub_eq_zero_of_le hle]
      rw [hzero]
      simpa [ProbabilityTheory.poissonPMFReal] using le_of_lt (Real.exp_pos (-(lam : ℝ)))
  exact (ENNReal.toReal_le_toReal (by simp) ((ProbabilityTheory.poissonPMF lam).apply_ne_top 0)).1 hreal

lemma prob_8_6_poisson_zero_ne_zero (lam : NNReal) :
    (ProbabilityTheory.poissonPMF lam 0) ≠ 0 := by
  intro hzero
  have hreal : (((ProbabilityTheory.poissonPMF lam 0)).toReal) = 0 := by
    simpa [hzero]
  have hpos : 0 < (((ProbabilityTheory.poissonPMF lam 0)).toReal) := by
    rw [poissonPMF_toReal]
    simpa [ProbabilityTheory.poissonPMFReal] using Real.exp_pos (-(lam : ℝ))
  exact (ne_of_gt hpos) hreal

lemma berPoiStayAtZeroMass_le_one (lam : NNReal) :
    berPoiStayAtZeroMass lam ≤ 1 := by
  unfold berPoiStayAtZeroMass
  have hle : ((1 - lam : NNReal) : ENNReal) ≤ ProbabilityTheory.poissonPMF lam 0 :=
    prob_8_6_poisson_zero_ge_ber_zero lam
  have hq0_ne : (ProbabilityTheory.poissonPMF lam 0) ≠ 0 :=
    prob_8_6_poisson_zero_ne_zero lam
  have hq0_ne_top : ProbabilityTheory.poissonPMF lam 0 ≠ ⊤ :=
    (ProbabilityTheory.poissonPMF lam).apply_ne_top 0
  rw [ENNReal.div_le_iff hq0_ne hq0_ne_top]
  simpa using hle

/-- When the Poisson coordinate is `0`, split the Bernoulli coordinate between `0` and `1`
with the exact amount needed to recover the Bernoulli marginal. -/
noncomputable def berPoiZeroSplitBool (lam : NNReal) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then 1 - berPoiStayAtZeroMass lam else berPoiStayAtZeroMass lam)
    (by
      rw [Fintype.sum_bool]
      simp [berPoiStayAtZeroMass_le_one lam, add_comm])

lemma berPoiZeroSplitBool_false (lam : NNReal) :
    berPoiZeroSplitBool lam false = berPoiStayAtZeroMass lam := by
  simp [berPoiZeroSplitBool, PMF.ofFintype]

lemma berPoiZeroSplitBool_true (lam : NNReal) :
    berPoiZeroSplitBool lam true = 1 - berPoiStayAtZeroMass lam := by
  simp [berPoiZeroSplitBool, PMF.ofFintype]

/-- The `Y = 0` branch, viewed on `ℕ`, only takes the values `0` and `1`. -/
noncomputable def berPoiZeroSplitNat (lam : NNReal) : PMF ℕ :=
  (berPoiZeroSplitBool lam).map fun b : Bool => if b then 1 else 0

lemma berPoiZeroSplitNat_zero (lam : NNReal) :
    berPoiZeroSplitNat lam 0 = berPoiStayAtZeroMass lam := by
  rw [berPoiZeroSplitNat, PMF.map_apply, tsum_fintype]
  simp [berPoiZeroSplitBool_false, berPoiZeroSplitBool_true]

lemma berPoiZeroSplitNat_one (lam : NNReal) :
    berPoiZeroSplitNat lam 1 = 1 - berPoiStayAtZeroMass lam := by
  rw [berPoiZeroSplitNat, PMF.map_apply, tsum_fintype]
  simp [berPoiZeroSplitBool_false, berPoiZeroSplitBool_true]

lemma berPoiZeroSplitNat_ge_two (lam : NNReal) {n : ℕ} (hn : 2 ≤ n) :
    berPoiZeroSplitNat lam n = 0 := by
  rw [berPoiZeroSplitNat, PMF.map_apply, tsum_fintype]
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  simp [hne0, hne1, berPoiZeroSplitBool_false, berPoiZeroSplitBool_true]

/-- Conditional law of the Bernoulli coordinate given the Poisson coordinate in the explicit
part (b) maximal coupling. At `Y = 0` we split between `0` and `1`; once `Y ≥ 1`, the
Bernoulli coordinate is forced to be `1`. -/
noncomputable def berPoiCondX (lam : NNReal) : ℕ → PMF ℕ
  | 0 => berPoiZeroSplitNat lam
  | _ + 1 => PMF.pure 1

lemma berPoiCondX_zero_zero (lam : NNReal) :
    berPoiCondX lam 0 0 = berPoiStayAtZeroMass lam := by
  simp [berPoiCondX, berPoiZeroSplitNat_zero]

lemma berPoiCondX_zero_one (lam : NNReal) :
    berPoiCondX lam 0 1 = 1 - berPoiStayAtZeroMass lam := by
  simp [berPoiCondX, berPoiZeroSplitNat_one]

lemma berPoiCondX_succ_zero (lam : NNReal) (y : ℕ) :
    berPoiCondX lam (y + 1) 0 = 0 := by
  simp [berPoiCondX]

lemma berPoiCondX_succ_one (lam : NNReal) (y : ℕ) :
    berPoiCondX lam (y + 1) 1 = 1 := by
  simp [berPoiCondX]

lemma berPoiCondX_ge_two (lam : NNReal) (y n : ℕ) (hn : 2 ≤ n) :
    berPoiCondX lam y n = 0 := by
  rcases y with _ | y
  · simpa [berPoiCondX] using berPoiZeroSplitNat_ge_two lam hn
  · have hne1 : n ≠ 1 := by omega
    simp [berPoiCondX, hne1]

/-- Pushing the explicit joint branch forward along `Prod.snd` recovers the original `y`. -/
lemma prob_8_6_part_b_inner_map_snd (lam : NNReal) (a : ℕ) :
    ((berPoiCondX lam a).map fun x => (x, a)).map Prod.snd = PMF.pure a := by
  calc
    ((berPoiCondX lam a).map fun x => (x, a)).map Prod.snd
      = (berPoiCondX lam a).map (Prod.snd ∘ fun x => (x, a)) := by
          simpa using
            (PMF.map_comp (p := berPoiCondX lam a) (f := fun x => (x, a)) (g := Prod.snd))
    _ = (berPoiCondX lam a).map (Function.const ℕ a) := by
          rfl
    _ = PMF.pure a := PMF.map_const _ _

/-- Pushing the explicit joint branch forward along `Prod.fst` recovers the conditional Bernoulli
coordinate. -/
lemma prob_8_6_part_b_inner_map_fst (lam : NNReal) (y : ℕ) :
    ((berPoiCondX lam y).map fun x => (x, y)).map Prod.fst = berPoiCondX lam y := by
  calc
    ((berPoiCondX lam y).map fun x => (x, y)).map Prod.fst
      = (berPoiCondX lam y).map (Prod.fst ∘ fun x => (x, y)) := by
          simpa using
            (PMF.map_comp (p := berPoiCondX lam y) (f := fun x => (x, y)) (g := Prod.fst))
    _ = (berPoiCondX lam y).map id := by
          rfl
    _ = berPoiCondX lam y := PMF.map_id _

/-- Explicit joint pmf for the part (b) Bernoulli/Poisson maximal coupling. -/
noncomputable def prob_8_6_part_b_joint (lam : NNReal) : PMF (ℕ × ℕ) :=
  (ProbabilityTheory.poissonPMF lam).bind fun y =>
    (berPoiCondX lam y).map fun x => (x, y)

lemma prob_8_6_part_b_joint_map_snd (lam : NNReal) :
    (prob_8_6_part_b_joint lam).map Prod.snd = ProbabilityTheory.poissonPMF lam := by
  unfold prob_8_6_part_b_joint
  rw [PMF.map_bind]
  have hfun :
      (fun a => ((berPoiCondX lam a).map fun x => (x, a)).map Prod.snd)
        = fun a => PMF.pure a := by
          funext a
          exact prob_8_6_part_b_inner_map_snd lam a
  rw [hfun]
  simpa using (PMF.bind_pure (ProbabilityTheory.poissonPMF lam))

lemma prob_8_6_part_b_joint_map_fst_apply (lam : NNReal) (n : ℕ) :
    ((prob_8_6_part_b_joint lam).map Prod.fst) n
      = ∑' y, ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y n := by
  unfold prob_8_6_part_b_joint
  rw [PMF.map_bind]
  have hfun :
      (fun y => ((berPoiCondX lam y).map fun x => (x, y)).map Prod.fst)
        = fun y => berPoiCondX lam y := by
          funext y
          exact prob_8_6_part_b_inner_map_fst lam y
  rw [hfun]
  rw [PMF.bind_apply]

lemma prob_8_6_part_b_joint_map_fst_zero (lam : NNReal) (hlam : lam ≤ 1) :
    ((prob_8_6_part_b_joint lam).map Prod.fst) 0 = bernoulliNatPMF lam hlam 0 := by
  rw [prob_8_6_part_b_joint_map_fst_apply]
  rw [tsum_eq_single 0]
  · have hq0_ne : ProbabilityTheory.poissonPMF lam 0 ≠ 0 :=
      prob_8_6_poisson_zero_ne_zero lam
    have hq0_ne_top : ProbabilityTheory.poissonPMF lam 0 ≠ ⊤ :=
      (ProbabilityTheory.poissonPMF lam).apply_ne_top 0
    rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
    simp [PMF.bernoulli_apply, hlam, berPoiCondX_zero_zero, berPoiStayAtZeroMass,
      ENNReal.mul_div_cancel hq0_ne hq0_ne_top]
  · intro y hy
    rcases y with _ | y
    · contradiction
    · simp [berPoiCondX_succ_zero, hy]

lemma prob_8_6_part_b_joint_map_fst_ge_two (lam : NNReal) {n : ℕ} (hn : 2 ≤ n) :
    ((prob_8_6_part_b_joint lam).map Prod.fst) n = 0 := by
  rw [prob_8_6_part_b_joint_map_fst_apply]
  apply ENNReal.tsum_eq_zero.2
  intro y
  rcases y with _ | y
  · simp [berPoiCondX_ge_two, hn]
  · simp [berPoiCondX_ge_two, hn]

lemma prob_8_6_part_b_joint_rest_mass (lam : NNReal) :
    ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y)
      = 1 - ProbabilityTheory.poissonPMF lam 0 := by
  have hg_ne_top : ∑' y, (if y = 0 then ProbabilityTheory.poissonPMF lam y else 0) ≠ ⊤ := by
    rw [tsum_ite_eq 0]
    exact (ProbabilityTheory.poissonPMF lam).apply_ne_top 0
  have hg_le :
      (fun y => if y = 0 then ProbabilityTheory.poissonPMF lam y else 0)
        ≤ ProbabilityTheory.poissonPMF lam := by
    intro y
    by_cases hy : y = 0 <;> simp [hy]
  calc
    ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y)
      = ∑' y, (ProbabilityTheory.poissonPMF lam y - (if y = 0 then ProbabilityTheory.poissonPMF lam y else 0)) := by
          refine tsum_congr ?_
          intro y
          by_cases hy : y = 0 <;> simp [hy]
    _ = ∑' y, ProbabilityTheory.poissonPMF lam y
          - ∑' y, (if y = 0 then ProbabilityTheory.poissonPMF lam y else 0) := by
            exact ENNReal.tsum_sub hg_ne_top hg_le
    _ = 1 - ProbabilityTheory.poissonPMF lam 0 := by
          simp [tsum_ite_eq 0]

lemma prob_8_6_part_b_joint_map_fst_one (lam : NNReal) (hlam : lam ≤ 1) :
    ((prob_8_6_part_b_joint lam).map Prod.fst) 1 = bernoulliNatPMF lam hlam 1 := by
  rw [prob_8_6_part_b_joint_map_fst_apply]
  have hq0_ne : ProbabilityTheory.poissonPMF lam 0 ≠ 0 :=
    prob_8_6_poisson_zero_ne_zero lam
  have hq0_ne_top : ProbabilityTheory.poissonPMF lam 0 ≠ ⊤ :=
    (ProbabilityTheory.poissonPMF lam).apply_ne_top 0
  have hber : bernoulliNatPMF lam hlam 1 = (lam : ENNReal) := by
    rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
    simp [PMF.bernoulli_apply, hlam]
  have hsplit :
      ∑' y, ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1
        = ProbabilityTheory.poissonPMF lam 0 * (1 - berPoiStayAtZeroMass lam)
            + ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y) := by
    calc
      ∑' y, ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1
        = ∑' y,
            ((if y = 0 then ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1 else 0)
              + (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1)) := by
                refine tsum_congr ?_
                intro y
                by_cases hy : y = 0 <;> simp [hy]
      _ = (∑' y, if y = 0 then ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1 else 0)
            + ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1) := by
              rw [ENNReal.tsum_add]
      _ = ProbabilityTheory.poissonPMF lam 0 * (1 - berPoiStayAtZeroMass lam)
            + ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y 1) := by
              rw [tsum_ite_eq 0]
              simp [berPoiCondX_zero_one]
      _ = ProbabilityTheory.poissonPMF lam 0 * (1 - berPoiStayAtZeroMass lam)
            + ∑' y, (if y = 0 then 0 else ProbabilityTheory.poissonPMF lam y) := by
              congr 1
              refine tsum_congr ?_
              intro y
              by_cases hy : y = 0
              · simp [hy]
              · rcases y with _ | y
                · contradiction
                · simp [hy, berPoiCondX_succ_one]
  rw [hsplit, prob_8_6_part_b_joint_rest_mass]
  have hfirst :
      ProbabilityTheory.poissonPMF lam 0 * (1 - berPoiStayAtZeroMass lam)
        = ProbabilityTheory.poissonPMF lam 0 - ((1 - lam : NNReal) : ENNReal) := by
    rw [ENNReal.mul_sub (by
      intro hc0 hc1
      exact hq0_ne_top), mul_one, berPoiStayAtZeroMass]
    simp [ENNReal.mul_div_cancel hq0_ne hq0_ne_top]
  rw [hfirst]
  have hcombine :
      (ProbabilityTheory.poissonPMF lam 0 - ((1 - lam : NNReal) : ENNReal))
        + (1 - ProbabilityTheory.poissonPMF lam 0)
        = 1 - ((1 - lam : NNReal) : ENNReal) := by
    let p0 : ENNReal := ProbabilityTheory.poissonPMF lam 0
    let b : ENNReal := ((1 - lam : NNReal) : ENNReal)
    have hb_le_p0 : b ≤ p0 := prob_8_6_poisson_zero_ge_ber_zero lam
    have hp0_le_one : p0 ≤ 1 := (ProbabilityTheory.poissonPMF lam).coe_le_one 0
    have hp0_ne_top : p0 ≠ ⊤ := (ProbabilityTheory.poissonPMF lam).apply_ne_top 0
    have hleft_ne_top : (p0 - b) + (1 - p0) ≠ ⊤ := by
      exact ENNReal.add_ne_top.2 ⟨ENNReal.sub_ne_top hp0_ne_top, ENNReal.sub_ne_top (by simp)⟩
    have hright_ne_top : 1 - b ≠ ⊤ := ENNReal.sub_ne_top (by simp)
    apply (ENNReal.toReal_eq_toReal hleft_ne_top hright_ne_top).mp
    rw [ENNReal.toReal_add (ENNReal.sub_ne_top hp0_ne_top) (ENNReal.sub_ne_top (by simp))]
    rw [ENNReal.toReal_sub_of_le hb_le_p0 hp0_ne_top]
    rw [ENNReal.toReal_sub_of_le hp0_le_one (by simp)]
    rw [ENNReal.toReal_sub_of_le (by simp [b]) (by simp)]
    ring
  rw [hcombine]
  have hcast :
      (1 : ENNReal) - ((1 - lam : NNReal) : ENNReal) = (lam : ENNReal) := by
    simpa using congrArg (fun x : NNReal => (x : ENNReal)) (tsub_tsub_cancel_of_le hlam)
  rw [hber]
  exact hcast

lemma prob_8_6_part_b_joint_map_fst (lam : NNReal) (hlam : lam ≤ 1) :
    (prob_8_6_part_b_joint lam).map Prod.fst = bernoulliNatPMF lam hlam := by
  ext n
  rcases n with (_ | n)
  · exact prob_8_6_part_b_joint_map_fst_zero lam hlam
  · rcases n with (_ | n)
    · exact prob_8_6_part_b_joint_map_fst_one lam hlam
    · have hge : 2 ≤ n.succ.succ := by omega
      rw [prob_8_6_part_b_joint_map_fst_ge_two lam hge]
      rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
      have hne0 : n.succ.succ ≠ 0 := by omega
      have hne1 : n.succ.succ ≠ 1 := by omega
      simp [PMF.bernoulli_apply, hlam, hne0, hne1]

/-- Explicit maximal-coupling object for part (b). -/
noncomputable def prob_8_6_part_b_coupling (lam : NNReal) (hlam : lam ≤ 1) :
    DiscretePmfCoupling (bernoulliNatPMF lam hlam) (ProbabilityTheory.poissonPMF lam) where
  jointPMF := prob_8_6_part_b_joint lam
  marginal_X := prob_8_6_part_b_joint_map_fst lam hlam
  marginal_Y := prob_8_6_part_b_joint_map_snd lam

lemma prob_8_6_part_b_joint_apply (lam : NNReal) (x y : ℕ) :
    prob_8_6_part_b_joint lam (x, y)
      = ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y x := by
  unfold prob_8_6_part_b_joint
  rw [PMF.bind_apply, tsum_eq_single y]
  · rw [PMF.map_apply, tsum_eq_single x]
    · simp
    · intro x' hx'
      by_cases hxx' : x = x'
      · exact (hx' hxx'.symm).elim
      · simp [Prod.mk.injEq, hxx']
  · intro a ha
    rw [PMF.map_apply]
    have hmap :
        ∑' a_1 : ℕ,
          (if (x, y) = (a_1, a) then (berPoiCondX lam a a_1) else (0 : ENNReal)) = 0 := by
      apply ENNReal.tsum_eq_zero.2
      intro a_1
      by_cases hxy : (x, y) = (a_1, a)
      · have : y = a := by simpa using congrArg Prod.snd hxy
        exact (ha this.symm).elim
      · simp [hxy]
    have hmul :=
      congrArg (fun t : ENNReal => (ProbabilityTheory.poissonPMF lam) a * t) hmap
    simpa using hmul

lemma prob_8_6_part_b_joint_zero_succ (lam : NNReal) (y : ℕ) :
    prob_8_6_part_b_joint lam (0, y + 1) = 0 := by
  calc
    prob_8_6_part_b_joint lam (0, y + 1)
      = ProbabilityTheory.poissonPMF lam (y + 1) * berPoiCondX lam (y + 1) 0 := by
          exact prob_8_6_part_b_joint_apply lam 0 (y + 1)
    _ = 0 := by simp [berPoiCondX_succ_zero]

lemma prob_8_6_part_b_joint_ge_two (lam : NNReal) (x y : ℕ) (hx : 2 ≤ x) :
    prob_8_6_part_b_joint lam (x, y) = 0 := by
  calc
    prob_8_6_part_b_joint lam (x, y)
      = ProbabilityTheory.poissonPMF lam y * berPoiCondX lam y x := by
          exact prob_8_6_part_b_joint_apply lam x y
    _ = 0 := by simp [berPoiCondX_ge_two, hx]

lemma prob_8_6_part_b_joint_one_one (lam : NNReal) :
    prob_8_6_part_b_joint lam (1, 1) = ProbabilityTheory.poissonPMF lam 1 := by
  rw [prob_8_6_part_b_joint_apply]
  simp [berPoiCondX_succ_one]

lemma prob_8_6_part_b_joint_map_fst_one_eq_lam (lam : NNReal) (hlam : lam ≤ 1) :
    (prob_8_6_part_b_joint lam).map Prod.fst 1 = (lam : ENNReal) := by
  rw [prob_8_6_part_b_joint_map_fst_one lam hlam]
  rw [bernoulliNatPMF, PMF.map_apply, tsum_fintype]
  simp [PMF.bernoulli_apply, hlam]

lemma prob_8_6_part_b_mismatch_indicator_split (lam : NNReal) (xy : ℕ × ℕ) :
    ({z : ℕ × ℕ | z.1 ≠ z.2}.indicator (fun z => prob_8_6_part_b_joint lam z) xy)
      + (if xy = (1, 1) then prob_8_6_part_b_joint lam xy else 0)
      = if 1 = xy.1 then prob_8_6_part_b_joint lam xy else 0 := by
  rcases xy with ⟨x, y⟩
  rcases x with _ | x
  · rcases y with _ | y
    · simp [Set.indicator]
    · have hzero : prob_8_6_part_b_joint lam (0, y + 1) = 0 :=
          prob_8_6_part_b_joint_zero_succ lam y
      simp [Set.indicator, hzero]
  · rcases x with _ | x
    · rcases y with _ | y
      · simp [Set.indicator]
      · rcases y with _ | y
        · simp [Set.indicator, prob_8_6_part_b_joint_one_one]
        · simp [Set.indicator]
    · have hx : 2 ≤ x.succ.succ := by omega
      have hzero : prob_8_6_part_b_joint lam (x.succ.succ, y) = 0 :=
        prob_8_6_part_b_joint_ge_two lam x.succ.succ y hx
      simp [Set.indicator, hzero]

lemma prob_8_6_part_b_mismatchMassENN_add_diag (lam : NNReal) (hlam : lam ≤ 1) :
    discretePmfCouplingMismatchMassENN (prob_8_6_part_b_coupling lam hlam)
      + prob_8_6_part_b_joint lam (1, 1)
      = (prob_8_6_part_b_joint lam).map Prod.fst 1 := by
  classical
  unfold discretePmfCouplingMismatchMassENN
  have hdiag :
      prob_8_6_part_b_joint lam (1, 1)
        = ∑' xy : ℕ × ℕ, if xy = (1, 1) then prob_8_6_part_b_joint lam xy else 0 := by
    symm
    exact tsum_eq_single (1, 1) fun xy hxy => by simp [hxy]
  rw [PMF.toMeasure_apply_eq_tsum, PMF.map_apply, hdiag, ← ENNReal.tsum_add]
  have htsum :
      ∑' a : ℕ × ℕ,
          ({xy : ℕ × ℕ | xy.1 ≠ xy.2}.indicator (fun z => prob_8_6_part_b_joint lam z) a
            + (if a = (1, 1) then prob_8_6_part_b_joint lam a else 0))
        = ∑' a : ℕ × ℕ,
            @ite ENNReal (1 = a.1) (Classical.propDecidable (1 = a.1))
              (prob_8_6_part_b_joint lam a) 0 := by
    apply tsum_congr
    intro a
    by_cases h1 : 1 = a.1
    · simpa [Set.indicator, h1] using prob_8_6_part_b_mismatch_indicator_split lam a
    · simpa [Set.indicator, h1] using prob_8_6_part_b_mismatch_indicator_split lam a
  simpa [prob_8_6_part_b_coupling, Set.indicator, Classical.propDecidable] using htsum

lemma prob_8_6_part_b_mismatchMassENN_eq (lam : NNReal) (hlam : lam ≤ 1) :
    discretePmfCouplingMismatchMassENN (prob_8_6_part_b_coupling lam hlam)
      = (lam : ENNReal) - ProbabilityTheory.poissonPMF lam 1 := by
  have hadd := prob_8_6_part_b_mismatchMassENN_add_diag lam hlam
  rw [prob_8_6_part_b_joint_map_fst_one_eq_lam lam hlam, prob_8_6_part_b_joint_one_one] at hadd
  exact ENNReal.eq_sub_of_add_eq ((ProbabilityTheory.poissonPMF lam).apply_ne_top 1) hadd

lemma prob_8_6_part_b_poisson_one_le_lam (lam : NNReal) (hlam : lam ≤ 1) :
    ProbabilityTheory.poissonPMF lam 1 ≤ (lam : ENNReal) := by
  calc
    ProbabilityTheory.poissonPMF lam 1
        ≤ discretePmfCouplingMismatchMassENN (prob_8_6_part_b_coupling lam hlam)
            + ProbabilityTheory.poissonPMF lam 1 := by
              simpa [add_comm] using
                self_le_add_left (ProbabilityTheory.poissonPMF lam 1)
                  (discretePmfCouplingMismatchMassENN (prob_8_6_part_b_coupling lam hlam))
    _ = (lam : ENNReal) := by
          simpa [prob_8_6_part_b_joint_map_fst_one_eq_lam lam hlam, prob_8_6_part_b_joint_one_one] using
            prob_8_6_part_b_mismatchMassENN_add_diag lam hlam

lemma prob_8_6_part_b_mismatchMass_eq_formula (lam : NNReal) (hlam : lam ≤ 1) :
    discretePmfCouplingMismatchMass (prob_8_6_part_b_coupling lam hlam)
      = (lam : ℝ) - ProbabilityTheory.poissonPMFReal lam 1 := by
  unfold discretePmfCouplingMismatchMass
  rw [prob_8_6_part_b_mismatchMassENN_eq lam hlam]
  rw [ENNReal.toReal_sub_of_le (prob_8_6_part_b_poisson_one_le_lam lam hlam) (by simp)]
  rw [poissonPMF_toReal]
  simp

lemma prob_8_6_part_b_tv_le_mismatchMass (lam : NNReal) (hlam : lam ≤ 1) :
    totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure
      ≤ discretePmfCouplingMismatchMass (prob_8_6_part_b_coupling lam hlam) := by
  let piC : Coupling (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure :=
    discretePmfCouplingToCoupling (prob_8_6_part_b_coupling lam hlam)
  simpa [piC, discretePmfCouplingToCoupling, discretePmfCouplingMismatchMass]
    using thm_8_7 piC

lemma prob_8_6_part_b_tv_ge_singleton_one (lam : NNReal) (hlam : lam ≤ 1) :
    (lam : ℝ) - ProbabilityTheory.poissonPMFReal lam 1
      ≤ totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure := by
  have hq1_le :
      ProbabilityTheory.poissonPMFReal lam 1 ≤ (lam : ℝ) := by
    rw [← poissonPMF_toReal]
    exact
      (ENNReal.toReal_le_toReal ((ProbabilityTheory.poissonPMF lam).apply_ne_top 1) (by simp)).2
        (prob_8_6_part_b_poisson_one_le_lam lam hlam)
  have hber :
      (bernoulliNatPMF lam hlam).toMeasure.real ({1} : Set ℕ) = (lam : ℝ) := by
    rw [MeasureTheory.measureReal_def]
    simpa [bernoulliNatPMF_one] using
      congrArg ENNReal.toReal (PMF.toMeasure_apply_finset (bernoulliNatPMF lam hlam) ({1} : Finset ℕ))
  have hpoi :
      (ProbabilityTheory.poissonPMF lam).toMeasure.real ({1} : Set ℕ) = ProbabilityTheory.poissonPMFReal lam 1 := by
    rw [MeasureTheory.measureReal_def]
    simpa [poissonPMF_toReal] using
      congrArg ENNReal.toReal (PMF.toMeasure_apply_finset (ProbabilityTheory.poissonPMF lam) ({1} : Finset ℕ))
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set ℕ, MeasurableSet A ∧
      d = |(bernoulliNatPMF lam hlam).toMeasure.real A - (ProbabilityTheory.poissonPMF lam).toMeasure.real A|}
  have hber_univ : (bernoulliNatPMF lam hlam).toMeasure.real (Set.univ : Set ℕ) = 1 := by
    rw [MeasureTheory.measureReal_def, PMF.toMeasure_apply_eq_tsum]
    simpa using congrArg ENNReal.toReal (PMF.tsum_coe (bernoulliNatPMF lam hlam))
  have hpoi_univ : (ProbabilityTheory.poissonPMF lam).toMeasure.real (Set.univ : Set ℕ) = 1 := by
    rw [MeasureTheory.measureReal_def, PMF.toMeasure_apply_eq_tsum]
    simpa using congrArg ENNReal.toReal (PMF.tsum_coe (ProbabilityTheory.poissonPMF lam))
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    have hsub : A ⊆ (Set.univ : Set ℕ) := by
      intro x hx
      trivial
    have hber_le : (bernoulliNatPMF lam hlam).toMeasure.real A ≤ 1 := by
      refine (MeasureTheory.measureReal_mono (μ := (bernoulliNatPMF lam hlam).toMeasure) hsub).trans ?_
      simpa using hber_univ
    have hpoi_le : (ProbabilityTheory.poissonPMF lam).toMeasure.real A ≤ 1 := by
      refine (MeasureTheory.measureReal_mono (μ := (ProbabilityTheory.poissonPMF lam).toMeasure) hsub).trans ?_
      simpa using hpoi_univ
    have hber_nn : 0 ≤ (bernoulliNatPMF lam hlam).toMeasure.real A := MeasureTheory.measureReal_nonneg
    have hpoi_nn : 0 ≤ (ProbabilityTheory.poissonPMF lam).toMeasure.real A := MeasureTheory.measureReal_nonneg
    rw [abs_sub_le_iff]
    constructor <;> linarith
  change (lam : ℝ) - ProbabilityTheory.poissonPMFReal lam 1 ≤ sSup S
  refine le_csSup hbounded ?_
  refine ⟨({1} : Set ℕ), MeasurableSet.singleton 1, ?_⟩
  rw [hber, hpoi, abs_of_nonneg (sub_nonneg.mpr hq1_le)]

/-- The explicit part (b) coupling is maximal: its mismatch mass is exactly the TV distance
between `Ber(λ)` and `Poi(λ)`. -/
theorem prob_8_6_part_b_coupling_is_maximal (lam : NNReal) (hlam : lam ≤ 1) :
    totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure
      = discretePmfCouplingMismatchMass (prob_8_6_part_b_coupling lam hlam) := by
  apply le_antisymm
  · exact prob_8_6_part_b_tv_le_mismatchMass lam hlam
  · rw [prob_8_6_part_b_mismatchMass_eq_formula lam hlam]
    exact prob_8_6_part_b_tv_ge_singleton_one lam hlam

/-- The part (b) Bernoulli/Poisson TV distance is bounded by `λ²`. -/
theorem prob_8_6_part_b_tv_le_sq (lam : NNReal) (hlam : lam ≤ 1) :
    totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure
      ≤ (lam : ℝ) ^ 2 := by
  have h_formula :=
    thm_8_6_discrete_pmf (bernoulliNatPMF lam hlam) (ProbabilityTheory.poissonPMF lam)
  have h_local :
      d_TV
          (fun n => ((bernoulliNatPMF lam hlam) n).toReal)
          (fun n => ((ProbabilityTheory.poissonPMF lam) n).toReal)
        ≤ (lam : ℝ) ^ 2 := by
    rw [bernoulliNatPMF_toReal_eq_Ber, poissonPMF_toReal_eq_Poi]
    exact ber_poi_tv_le_sq (p := (lam : ℝ)) (by exact_mod_cast lam.2)
  rw [h_formula]
  simpa [d_TV] using h_local

/-- The mismatch mass of the explicit part (b) maximal coupling is bounded by `λ²`. -/
theorem prob_8_6_part_b_mismatchMass_le_sq (lam : NNReal) (hlam : lam ≤ 1) :
    discretePmfCouplingMismatchMass (prob_8_6_part_b_coupling lam hlam) ≤ (lam : ℝ) ^ 2 := by
  rw [← prob_8_6_part_b_coupling_is_maximal lam hlam]
  exact prob_8_6_part_b_tv_le_sq lam hlam

/-
============================================================================
Convolution contraction for d_TV
============================================================================

The convolution difference equals a weighted sum of differences.
-/
