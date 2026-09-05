/-
TASK ID: thm_10_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_10.def_10_4




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

 
theorem tendstoInMeasure_of_convergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInMeasure μ Xn atTop X := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hprob_half := hProb.2.2 (ε / 2) hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob_half
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hnorm : ε ≤ |Xn n ω - X ω| := by
    simpa [Real.norm_eq_abs] using hω
  have hstrict : ε / 2 < |Xn n ω - X ω| := by linarith
  simpa [deviationEvent] using hstrict

 
def thm_10_7_cdfValue {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (a : ℝ) : ℝ :=
  μ.real {ω : Ω | Y ω ≤ a}

 
def thm_10_7_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) : ProbabilityMeasure ℝ :=
  ⟨μ.map Y, Measure.isProbabilityMeasure_map hY.aemeasurable⟩

 
theorem thm_10_7_measureCdf_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (a : ℝ) :
    measureCdf (thm_10_7_law μ Y hY) a = thm_10_7_cdfValue μ Y a := by
  rw [measureCdf, thm_10_7_cdfValue]
  change (μ.map Y).real (Iic a) = μ.real {ω : Ω | Y ω ≤ a}
  rw [map_measureReal_apply hY measurableSet_Iic]
  rfl

 
theorem thm_10_7_upper_event_subset {Ω : Type*}
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (a δ : ℝ) :
    {ω : Ω | Xn n ω ≤ a} ⊆
      {ω : Ω | X ω ≤ a + δ} ∪ deviationEvent Xn X n δ := by
  intro ω hω
  by_cases hdev : δ < |Xn n ω - X ω|
  · exact Or.inr (by simpa [deviationEvent] using hdev)
  · left
    have habs : |Xn n ω - X ω| ≤ δ := le_of_not_gt hdev
    have hlower : -δ ≤ Xn n ω - X ω := (abs_le.mp habs).1
    change Xn n ω ≤ a at hω
    change X ω ≤ a + δ
    linarith

 
theorem thm_10_7_lower_event_subset {Ω : Type*}
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (a δ : ℝ) :
    {ω : Ω | X ω ≤ a - δ} ⊆
      {ω : Ω | Xn n ω ≤ a} ∪ deviationEvent Xn X n δ := by
  intro ω hω
  by_cases hdev : δ < |Xn n ω - X ω|
  · exact Or.inr (by simpa [deviationEvent] using hdev)
  · left
    have habs : |Xn n ω - X ω| ≤ δ := le_of_not_gt hdev
    have hupper : Xn n ω - X ω ≤ δ := (abs_le.mp habs).2
    change X ω ≤ a - δ at hω
    change Xn n ω ≤ a
    linarith

 
theorem thm_10_7_cdf_upper_inequality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (a δ : ℝ) :
    thm_10_7_cdfValue μ (Xn n) a ≤
      thm_10_7_cdfValue μ X (a + δ) + μ.real (deviationEvent Xn X n δ) := by
  unfold thm_10_7_cdfValue
  calc
    μ.real {ω : Ω | Xn n ω ≤ a} ≤
        μ.real ({ω : Ω | X ω ≤ a + δ} ∪ deviationEvent Xn X n δ) :=
      measureReal_mono (thm_10_7_upper_event_subset Xn X n a δ)
    _ ≤ μ.real {ω : Ω | X ω ≤ a + δ} + μ.real (deviationEvent Xn X n δ) :=
      measureReal_union_le _ _

 
theorem thm_10_7_cdf_lower_inequality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (a δ : ℝ) :
    thm_10_7_cdfValue μ X (a - δ) ≤
      thm_10_7_cdfValue μ (Xn n) a + μ.real (deviationEvent Xn X n δ) := by
  unfold thm_10_7_cdfValue
  calc
    μ.real {ω : Ω | X ω ≤ a - δ} ≤
        μ.real ({ω : Ω | Xn n ω ≤ a} ∪ deviationEvent Xn X n δ) :=
      measureReal_mono (thm_10_7_lower_event_subset Xn X n a δ)
    _ ≤ μ.real {ω : Ω | Xn n ω ≤ a} + μ.real (deviationEvent Xn X n δ) :=
      measureReal_union_le _ _

 
theorem thm_10_7_deviation_measureReal_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => μ.real (deviationEvent Xn X n δ)) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hProb.2.2 δ hδ)
  change Tendsto (fun n : ℕ => μ.real (deviationEvent Xn X n δ)) atTop (𝓝 (0 : ℝ)) at h
  exact h

 
theorem thm_10_7_limsup_cdf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X)
    (a δ : ℝ) (hδ : 0 < δ) :
    limsup (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop ≤
      thm_10_7_cdfValue μ X (a + δ) := by
  have hdev := thm_10_7_deviation_measureReal_tendsto_zero μ Xn X hProb δ hδ
  have hsum :
      Tendsto
        (fun n : ℕ =>
          thm_10_7_cdfValue μ X (a + δ) + μ.real (deviationEvent Xn X n δ))
        atTop (𝓝 (thm_10_7_cdfValue μ X (a + δ))) := by
    simpa using (tendsto_const_nhds.add hdev)
  have hcobounded :
      atTop.IsCoboundedUnder (· ≤ ·)
        (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) :=
    isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg)
  calc
    limsup (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop ≤
        limsup
          (fun n : ℕ =>
            thm_10_7_cdfValue μ X (a + δ) + μ.real (deviationEvent Xn X n δ))
          atTop :=
      limsup_le_limsup
        (Eventually.of_forall fun n => thm_10_7_cdf_upper_inequality μ Xn X n a δ)
        hcobounded hsum.isBoundedUnder_le
    _ = thm_10_7_cdfValue μ X (a + δ) := hsum.limsup_eq

 
theorem thm_10_7_cdf_le_liminf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X)
    (a δ : ℝ) (hδ : 0 < δ) :
    thm_10_7_cdfValue μ X (a - δ) ≤
      liminf (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop := by
  have hdev := thm_10_7_deviation_measureReal_tendsto_zero μ Xn X hProb δ hδ
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          thm_10_7_cdfValue μ X (a - δ) - μ.real (deviationEvent Xn X n δ))
        atTop (𝓝 (thm_10_7_cdfValue μ X (a - δ))) := by
    simpa using (tendsto_const_nhds.sub hdev)
  have hbounded :
      atTop.IsCoboundedUnder (· ≥ ·)
        (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) :=
    isCoboundedUnder_ge_of_le atTop (fun _ => measureReal_le_one)
  calc
    thm_10_7_cdfValue μ X (a - δ) =
        liminf
          (fun n : ℕ =>
            thm_10_7_cdfValue μ X (a - δ) - μ.real (deviationEvent Xn X n δ))
          atTop := hdiff.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop :=
      liminf_le_liminf
        (Eventually.of_forall fun n => by
          have h := thm_10_7_cdf_lower_inequality μ Xn X n a δ
          linarith)
        hdiff.isBoundedUnder_ge hbounded

 
theorem thm_10_7_cdf_tendsto_at_continuityPoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X)
    (a : ℝ) (hcont : ContinuousAt (thm_10_7_cdfValue μ X) a) :
    Tendsto (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop
      (𝓝 (thm_10_7_cdfValue μ X a)) := by
  let δ : ℕ → ℝ := fun k : ℕ => 1 / ((k : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hminus : Tendsto (fun k : ℕ => a - δ k) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds.sub hδ)
  have hplus : Tendsto (fun k : ℕ => a + δ k) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds.add hδ)
  have hinf :
      thm_10_7_cdfValue μ X a ≤
        liminf (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop := by
    apply le_of_tendsto' (hcont.tendsto.comp hminus)
    intro k
    exact thm_10_7_cdf_le_liminf μ Xn X hProb a (δ k) (by
      dsimp [δ]
      positivity)
  have hsup :
      limsup (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) atTop ≤
        thm_10_7_cdfValue μ X a := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds (hcont.tendsto.comp hplus)
    intro k
    exact thm_10_7_limsup_cdf_le μ Xn X hProb a (δ k) (by
      dsimp [δ]
      positivity)
  have hbddAbove :
      atTop.IsBoundedUnder (· ≤ ·)
        (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) :=
    isBoundedUnder_of_eventually_le
      (f := atTop)
      (u := fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a)
      (a := (1 : ℝ))
      (Eventually.of_forall fun n => by
        simpa [thm_10_7_cdfValue] using
          (measureReal_le_one (μ := μ) (s := {ω : Ω | Xn n ω ≤ a})))
  have hbddBelow :
      atTop.IsBoundedUnder (· ≥ ·)
        (fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a) :=
    isBoundedUnder_of_eventually_ge
      (f := atTop)
      (u := fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a)
      (a := (0 : ℝ))
      (Eventually.of_forall fun n => by
        simpa [thm_10_7_cdfValue] using
          (measureReal_nonneg (μ := μ) (s := {ω : Ω | Xn n ω ≤ a})))
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hbddAbove hbddBelow

 
theorem thm_10_7_measureCdf_tendsto_of_convergesInProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X)
    (a : ℝ)
    (hcont : ContinuousAt (measureCdf (thm_10_7_law μ X hProb.2.1)) a) :
    Tendsto
      (fun n : ℕ => measureCdf (thm_10_7_law μ (Xn n) (hProb.1 n)) a)
      atTop (𝓝 (measureCdf (thm_10_7_law μ X hProb.2.1) a)) := by
  have hlimit_fun :
      measureCdf (thm_10_7_law μ X hProb.2.1) = thm_10_7_cdfValue μ X := by
    funext x
    exact thm_10_7_measureCdf_law μ X hProb.2.1 x
  have hseq_fun :
      (fun n : ℕ => measureCdf (thm_10_7_law μ (Xn n) (hProb.1 n)) a) =
        fun n : ℕ => thm_10_7_cdfValue μ (Xn n) a := by
    funext n
    exact thm_10_7_measureCdf_law μ (Xn n) (hProb.1 n) a
  rw [hlimit_fun] at hcont ⊢
  rw [hseq_fun]
  exact thm_10_7_cdf_tendsto_at_continuityPoint μ Xn X hProb a hcont



theorem thm_10_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ := by
  let μn : ℕ → ProbabilityMeasure ℝ :=
    fun n : ℕ => thm_10_7_law μ (Xn n) (hProb.1 n)
  let μX : ProbabilityMeasure ℝ := thm_10_7_law μ X hProb.2.1
  have hCdf : CdfConvergesInDistribution μn μX := by
    intro a hcont
    exact thm_10_7_measureCdf_tendsto_of_convergesInProbability μ Xn X hProb a hcont
  have hLaw : MeasuresConvergeInDistribution μn μX :=
    (measuresConvergeInDistribution_iff_cdf μn μX).2 hCdf
  have hRV :
      RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xn μ X := by
    rw [randomVariablesConvergeInDistribution_iff_laws]
    refine ⟨hXn, hProb.2.1.aemeasurable, ?_⟩
    simpa [μn, μX, thm_10_7_law] using hLaw
  exact hRV
