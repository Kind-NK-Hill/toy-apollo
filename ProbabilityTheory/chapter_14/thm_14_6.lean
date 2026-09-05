/-
TASK ID: thm_14_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-prokhorov-sequential-compactness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.def_14_3
import ProbabilityTheory.chapter_10.thm_10_8
import ProbabilityTheory.chapter_14.thm_14_3
import ProbabilityTheory.chapter_09.thm_9_5




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section



def thm_14_6_cdfSubsequenceConvergesInDistribution
    (Fseq : ℕ → ℝ → ℝ) (index : ℕ → ℕ) (P : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (def_14_3_cdfOfMeasure P) x →
    Tendsto (fun k : ℕ => Fseq (index k) x) atTop
      (𝓝 (def_14_3_cdfOfMeasure P x))



structure thm_14_6_ProkhorovSubsequence
    (Fseq : ℕ → ℝ → ℝ) where
  index : ℕ → ℕ
  strictMono_index : StrictMono index
  limitMeasure : ProbabilityMeasure ℝ
  converges_at_continuity_points :
    thm_14_6_cdfSubsequenceConvergesInDistribution
      Fseq index limitMeasure



def thm_14_6_prokhorovStatement
    (Fseq : ℕ → ℝ → ℝ) : Prop :=
  def_14_3_tightCdfs Fseq →
    Nonempty (thm_14_6_ProkhorovSubsequence Fseq)



theorem thm_14_6_tightCdfs_subsequence
    {Fseq : ℕ → ℝ → ℝ} (hF : def_14_3_tightCdfs Fseq)
    (index : ℕ → ℕ) :
    def_14_3_tightCdfs (fun k : ℕ => Fseq (index k)) := by
  intro ε hε
  rcases hF ε hε with ⟨M, hM_nonneg, hM⟩
  exact ⟨M, hM_nonneg, fun k => hM (index k)⟩



def thm_14_6_weaklyConvergentSubsequence
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∃ P : ProbabilityMeasure ℝ, ∃ index : ℕ → ℕ,
    StrictMono index ∧ def_14_1 (fun k : ℕ => Pseq (index k)) P



def thm_14_6_characteristicFunction
    (P : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (P : Measure ℝ) t



def thm_14_6_characteristicConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => thm_14_6_characteristicFunction (Pseq n) t)
      atTop (𝓝 (φ t))



def thm_14_6_everySubsequenceHasSubsubsequenceLimit
    (α : ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ index : ℕ → ℕ, StrictMono index →
    ∃ subindex : ℕ → ℕ, StrictMono subindex ∧
      Tendsto (fun k : ℕ => α (index (subindex k))) atTop (𝓝 β)



theorem thm_14_6_subsequence_inherits_characteristic_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (index : ℕ → ℕ) (hindex : StrictMono index) :
    ∀ t : ℝ,
      Tendsto (fun k : ℕ =>
        thm_14_6_characteristicFunction (Pseq (index k)) t)
        atTop (𝓝 (φ t)) := by
  intro t
  exact (hφ t).comp hindex.tendsto_atTop



theorem thm_14_6_cdfSubsequenceConvergence_to_weak
    {Pseq : ℕ → ProbabilityMeasure ℝ} {index : ℕ → ℕ}
    {Q : ProbabilityMeasure ℝ}
    (h :
      thm_14_6_cdfSubsequenceConvergesInDistribution
        (def_14_3_cdfsOfMeasures Pseq) index Q) :
    Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) := by
  let Fseq : ℕ → thm_10_8_ProbabilityCdf := fun k : ℕ =>
    thm_10_8_probabilityCdfOfMeasure
      (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ))
  let F : thm_10_8_ProbabilityCdf :=
    thm_10_8_probabilityCdfOfMeasure ((Q : ProbabilityMeasure ℝ) : Measure ℝ)
  let Yn : ℕ → ℝ → ℝ := fun k : ℕ =>
    thm_10_8_lowerQuantileVariable (Fseq k)
  let Y : ℝ → ℝ := thm_10_8_lowerQuantileVariable F
  have hCdfConv :
      ∀ x : ℝ, ContinuousAt (F.stieltjes : ℝ → ℝ) x →
        Tendsto (fun k : ℕ => (Fseq k).stieltjes x) atTop
          (𝓝 (F.stieltjes x)) := by
    have hDist :
        CdfConvergesInDistribution (fun k : ℕ => Pseq (index k)) Q := by
      change
        thm_14_6_cdfSubsequenceConvergesInDistribution
          (def_14_3_cdfsOfMeasures Pseq) index Q
      exact h
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf Q) x := by
      have hfun :
          (fun y : ℝ => measureCdf Q y) =
            (fun y : ℝ => F.stieltjes y) := by
        funext y
        simp [F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
          ProbabilityTheory.cdf_eq_real]
      change ContinuousAt
        (fun y : ℝ => measureCdf Q y) x
      rw [hfun]
      exact hcont
    have htendsto := hDist x hcont_measure
    simpa [Fseq, F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
      ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto (fun k : ℕ => Yn k ω) atTop (nhds (Y ω)) := by
    simpa [Yn, Y, Fseq, F] using
      thm_10_8_almost_sure_lowerQuantile_tendsto Fseq F hCdfConv
  have hYnMeas : ∀ k : ℕ, Measurable (Yn k) := by
    intro k
    exact thm_10_8_lowerQuantileVariable_measurable (Fseq k)
  have hInMeasure : TendstoInMeasure thm_10_8_unitIntervalMeasure Yn atTop Y :=
    tendstoInMeasure_of_tendsto_ae
      (fun k : ℕ => (hYnMeas k).aestronglyMeasurable)
      hAlmostSure
  have hInDistribution :
      TendstoInDistribution Yn atTop Y
        (fun _ : ℕ => thm_10_8_unitIntervalMeasure)
        thm_10_8_unitIntervalMeasure :=
    hInMeasure.tendstoInDistribution
      (fun k : ℕ => (hYnMeas k).aemeasurable)
  have hYnLaw :
      ∀ k : ℕ,
        Measure.map (Yn k) thm_10_8_unitIntervalMeasure =
          ((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ) := by
    intro k
    haveI : IsProbabilityMeasure
        (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      (Pseq (index k)).property
    simpa [Yn, Fseq] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ))
        (Pseq (index k)).property)
  have hYLaw :
      Measure.map Y thm_10_8_unitIntervalMeasure =
        ((Q : ProbabilityMeasure ℝ) : Measure ℝ) := by
    haveI : IsProbabilityMeasure (((Q : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      Q.property
    simpa [Y, F] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((Q : ProbabilityMeasure ℝ) : Measure ℝ))
        Q.property)
  have hLawTendsto : Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) := by
    have hPseq :
        (fun k : ℕ =>
          (⟨Measure.map (Yn k) thm_10_8_unitIntervalMeasure,
            Measure.isProbabilityMeasure_map
              (hInDistribution.forall_aemeasurable k)⟩ :
            ProbabilityMeasure ℝ)) = fun k : ℕ => Pseq (index k) := by
      funext k
      apply Subtype.ext
      simpa using hYnLaw k
    have hP :
        (⟨Measure.map Y thm_10_8_unitIntervalMeasure,
          Measure.isProbabilityMeasure_map hInDistribution.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) = Q := by
      apply Subtype.ext
      simpa using hYLaw
    rw [← hPseq, ← hP]
    exact hInDistribution.tendsto
  exact hLawTendsto



theorem thm_14_6_theorem_14_3_characteristic_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (Q : ProbabilityMeasure ℝ) (index : ℕ → ℕ) (_hindex : StrictMono index)
    (hCdf :
      thm_14_6_cdfSubsequenceConvergesInDistribution
        (def_14_3_cdfsOfMeasures Pseq) index Q) :
    ∀ t : ℝ,
      Tendsto (fun k : ℕ =>
        thm_14_6_characteristicFunction (Pseq (index k)) t)
        atTop (𝓝 (thm_14_6_characteristicFunction Q t)) := by
  have hWeak :
      Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) :=
    thm_14_6_cdfSubsequenceConvergence_to_weak hCdf
  have hChar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := fun k : ℕ => Pseq (index k)) (μ₀ := Q)).mp hWeak
  intro t
  simpa [thm_14_6_characteristicFunction] using hChar t



theorem thm_14_6_inversion_formula_identifies_limit
    (P Q : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      thm_14_6_characteristicFunction Q t =
        thm_14_6_characteristicFunction P t) :
    Q = P := by
  have hmeasure : (Q : Measure ℝ) = (P : Measure ℝ) := by
    exact Measure.ext_of_charFun (funext hchar)
  exact ProbabilityMeasure.toMeasure_injective hmeasure



theorem thm_14_6_real_analysis_subsequence_principle
    (α : ℕ → ℝ) (β : ℝ)
    (h : thm_14_6_everySubsequenceHasSubsubsequenceLimit α β) :
    Tendsto α atTop (𝓝 β) := by
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  rcases strictMono_subseq_of_tendsto_atTop hns with ⟨φ, _hφ, hnsφ⟩
  rcases h (ns ∘ φ) hnsφ with ⟨subindex, _hsubindex, hlim⟩
  exact ⟨φ ∘ subindex, by simpa [Function.comp_def] using hlim⟩



theorem thm_14_6_subsubsequence_test_integral_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (hφP : ∀ t : ℝ, φ t = thm_14_6_characteristicFunction P t) :
    ∀ h : BoundedContinuousFunction ℝ ℝ,
      thm_14_6_everySubsequenceHasSubsubsequenceLimit
        (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
        (∫ x, h x ∂(P : Measure ℝ)) := by
  have hWeak : Tendsto Pseq atTop (𝓝 P) := by
    exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := Pseq) (μ₀ := P)).mpr (fun t : ℝ => by
        simpa [thm_14_6_characteristicFunction, hφP t] using hφ t)
  intro h index hindex
  refine ⟨id, (fun _ _ hlt => hlt), ?_⟩
  have hSubWeak : Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 P) :=
    hWeak.comp hindex.tendsto_atTop
  exact ((def_14_1_iff_tendsto).2 hSubWeak) h



structure thm_14_6_LevyCompletionSpine
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ) : Prop where
  tight_cdfs :
    def_14_3_tightCdfs (def_14_3_cdfsOfMeasures Pseq)
  prokhorov_subsubsequence :
    ∀ index : ℕ → ℕ, StrictMono index →
      Nonempty (thm_14_6_ProkhorovSubsequence
        (fun j : ℕ => def_14_3_cdfOfMeasure (Pseq (index j))))
  subsubsequence_test_integral_limit :
    ∀ h : BoundedContinuousFunction ℝ ℝ,
      thm_14_6_everySubsequenceHasSubsubsequenceLimit
        (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
        (∫ x, h x ∂(P : Measure ℝ))

 
theorem thm_14_6_cdf_of_reference
    (Fseq : ℕ → ℝ → ℝ)
    (hF : def_14_3_tightCdfs Fseq)
    (hProkhorov_reference : thm_14_6_prokhorovStatement Fseq) :
    Nonempty (thm_14_6_ProkhorovSubsequence Fseq) :=
  hProkhorov_reference hF



theorem thm_14_6
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3_mathlibTight Pseq) :
    thm_14_6_weaklyConvergentSubsequence Pseq := by
  have hcompact : IsCompact (closure (range Pseq)) := by
    refine isCompact_closure_of_isTightMeasureSet (S := range Pseq) ?_
    have hset :
        {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ range Pseq} =
          range (fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ)) := by
      ext μ
      constructor
      · rintro ⟨P, hP, rfl⟩
        rcases hP with ⟨n, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨Pseq n, ⟨n, rfl⟩, rfl⟩
    rw [hset]
    exact hTight
  rcases hcompact.tendsto_subseq
      (x := Pseq)
      (fun n : ℕ => subset_closure (mem_range_self n)) with
    ⟨P, _hP, index, hindex, hconv⟩
  refine ⟨P, index, hindex, ?_⟩
  exact (def_14_1_iff_tendsto).2 (by
    simpa [Function.comp_def] using hconv)



theorem thm_14_6_of_interval_tight
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3 Pseq) :
    thm_14_6_weaklyConvergentSubsequence Pseq :=
  thm_14_6 Pseq (def_14_3_to_mathlibTight Pseq hTight)



private theorem thm_14_6_levy_completion
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (hspine : thm_14_6_LevyCompletionSpine Pseq P φ hφ) :
    def_14_1 Pseq P := by
  intro h
  exact thm_14_6_real_analysis_subsequence_principle
    (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
    (∫ x, h x ∂(P : Measure ℝ))
    (hspine.subsubsequence_test_integral_limit h)
