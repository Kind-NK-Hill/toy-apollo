/-
TASK ID: thm_7_9_reverse_bound_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_7_9_finite_abs_bridge_support
import ToyApollo.Output.thm_7_9_mct_support

open MeasureTheory Set

noncomputable section

lemma thm_7_9_setIntegral_abs_trunc_eq_integral
    (μ : Measure ℝ) (g : ℝ → ℝ) (n : ℕ) :
    (∫ x in Icc (-(n : ℝ)) (n : ℝ),
        thm_7_9_trunc (fun y => |g y|) n x ∂μ) =
      ∫ x, thm_7_9_trunc (fun y => |g y|) n x ∂μ := by
  rw [← integral_indicator (μ := μ)
    (f := thm_7_9_trunc (fun y => |g y|) n) measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simp [thm_7_9_trunc, hx]
  · simp [thm_7_9_trunc, hx]

lemma thm_7_9_nat_Ioc_subset {n m : ℕ} (hnm : n ≤ m) :
    Ioc (-(n : ℝ)) (n : ℝ) ⊆ Ioc (-(m : ℝ)) (m : ℝ) := by
  intro x hx
  have hnmR : (n : ℝ) ≤ m := by
    exact_mod_cast hnm
  constructor
  · linarith [hx.1]
  · exact le_trans hx.2 hnmR

noncomputable def thm_7_9_symmetric_abs_rsIntegrable
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {n : ℕ} (hn : 0 < n) :
    RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) := by
  exact h.to_source_regular.finite_abs_rs (by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    linarith)

theorem thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {n : ℕ} (hn : 0 < n) :
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        (thm_7_9_symmetric_abs_rsIntegrable F h hn) =
      ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := by
  have hlt : -(n : ℝ) < (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  let hOrig : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) :=
    thm_7_9_symmetric_abs_rsIntegrable F h hn
  have hEqOn : ∀ x ∈ Icc (-(n : ℝ)) (n : ℝ), f x = |g x| := by
    intro x hx
    dsimp [f]
    exact Set.indicator_of_mem hx (fun y => |g y|)
  let hTrunc : RSIntegrable f F (-(n : ℝ)) (n : ℝ) :=
    rsIntegrable_congr_integrand_Icc hOrig hEqOn
  have hTruncOrig :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    exact rsIntegral_congr_integrand_Icc hOrig hEqOn
  have hfMeas : Measurable f := by
    dsimp [f]
    exact thm_7_9_trunc_measurable h.measurable.abs n
  have hfMeasRestrict :
      Measurable ((Icc (-(n : ℝ)) (n : ℝ)).restrict f) := by
    exact hfMeas.comp measurable_subtype_coe
  have hAbsBounds := h.finite_abs_bounds hlt
  have hAbove : BddAbove (f '' Icc (-(n : ℝ)) (n : ℝ)) := by
    rcases hAbsBounds.1 with ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hfx : f x = |g x| := hEqOn x hx
    rw [hfx]
    exact hU ⟨x, hx, rfl⟩
  have hBelow : BddBelow (f '' Icc (-(n : ℝ)) (n : ℝ)) := by
    rcases hAbsBounds.2 with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hfx : f x = |g x| := hEqOn x hx
    rw [hfx]
    exact hL ⟨x, hx, rfl⟩
  have hIoc :=
    thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
      F hfMeasRestrict hAbove hBelow hTrunc
  rcases hIoc with ⟨_hIntIoc, hEqIoc⟩
  rcases hEqIoc with ⟨hRSIoc, hIocEq⟩
  have hIocEqAbs :
      (∫ x in Ioc (-(n : ℝ)) (n : ℝ), f x ∂F.measure) =
        ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro x hx
    exact hEqOn x (Ioc_subset_Icc_self hx)
  have hRSIocTrunc :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSIoc =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSIoc) (rsIntegral_spec hTrunc)
  calc
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        (thm_7_9_symmetric_abs_rsIntegrable F h hn)
        = rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig :=
          rsTruncIntegral_proof_irrel _ _
    _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := hTruncOrig.symm
    _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSIoc := hRSIocTrunc.symm
    _ = ∫ x in Ioc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := hIocEq.symm
    _ = ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := hIocEqAbs

theorem thm_7_9_symmetric_abs_rs_bound_by_total_ls
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) {n : ℕ} (hn : 0 < n) :
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        (thm_7_9_symmetric_abs_rsIntegrable F h hn) ≤
      ∫ x, |g x| ∂F.measure := by
  have hlt : -(n : ℝ) < (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  let hOrig : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) :=
    thm_7_9_symmetric_abs_rsIntegrable F h hn
  have hEqOn : ∀ x ∈ Icc (-(n : ℝ)) (n : ℝ), f x = |g x| := by
    intro x hx
    dsimp [f]
    exact Set.indicator_of_mem hx (fun y => |g y|)
  let hTrunc : RSIntegrable f F (-(n : ℝ)) (n : ℝ) :=
    rsIntegrable_congr_integrand_Icc hOrig hEqOn
  have hTruncOrig :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    exact rsIntegral_congr_integrand_Icc hOrig hEqOn
  rcases
      thm_7_9_finite_abs_bridge
        F h hn with
    ⟨_hIcc, hBridge⟩
  rcases hBridge with ⟨hRSBridge, hBridgeEq⟩
  have hBridgeTrunc :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSBridge) (rsIntegral_spec hTrunc)
  have hRsTruncBridge :
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
          (thm_7_9_symmetric_abs_rsIntegrable F h hn) =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge := by
    calc
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
          (thm_7_9_symmetric_abs_rsIntegrable F h hn)
          = rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig :=
            rsTruncIntegral_proof_irrel _ _
      _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := hTruncOrig.symm
      _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge :=
            hBridgeTrunc.symm
  have hEndpointNonneg :
      0 ≤ (F.measure {-(n : ℝ)}).toReal * f (-(n : ℝ)) := by
    exact mul_nonneg ENNReal.toReal_nonneg (by
      dsimp [f]
      exact thm_7_9_abs_trunc_nonneg g n (-(n : ℝ)))
  have hBridgeValueLeSet :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge ≤
        ∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := by
    rw [hBridgeEq]
    linarith
  have hSetEqGlobal :
      (∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure) =
        ∫ x, f x ∂F.measure := by
    dsimp [f]
    exact thm_7_9_setIntegral_abs_trunc_eq_integral F.measure g n
  have hGlobalLe :
      (∫ x, f x ∂F.measure) ≤ ∫ x, |g x| ∂F.measure := by
    dsimp [f]
    exact thm_7_9_integral_abs_trunc_le_integral_abs
      F.measure h.measurable hAbs n
  calc
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        (thm_7_9_symmetric_abs_rsIntegrable F h hn)
        = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge := hRsTruncBridge
    _ ≤ ∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := hBridgeValueLeSet
    _ = ∫ x, f x ∂F.measure := hSetEqGlobal
    _ ≤ ∫ x, |g x| ∂F.measure := hGlobalLe

noncomputable def thm_7_9_symmetric_abs_rsTrunc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) (n : ℕ) : ℝ :=
  rsTruncIntegral (fun x => |g x|) F
    (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)
    (thm_7_9_symmetric_abs_rsIntegrable F h (Nat.succ_pos n))

theorem thm_7_9_symmetric_abs_rsTrunc_eq_integral_Ioc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) (n : ℕ) :
    thm_7_9_symmetric_abs_rsTrunc F h n =
      ∫ x in Ioc (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ),
        |g x| ∂F.measure := by
  exact thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc F h (Nat.succ_pos n)

theorem thm_7_9_symmetric_abs_rs_bddAbove_by_total_ls
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    ∃ C : ℝ, ∀ n : ℕ,
      thm_7_9_symmetric_abs_rsTrunc F h n ≤ C := by
  refine ⟨∫ x, |g x| ∂F.measure, ?_⟩
  intro n
  exact thm_7_9_symmetric_abs_rs_bound_by_total_ls
    F h hAbs (Nat.succ_pos n)

theorem thm_7_9_symmetric_abs_rs_monotone
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    Monotone (thm_7_9_symmetric_abs_rsTrunc F h) := by
  intro n m hnm
  rw [thm_7_9_symmetric_abs_rsTrunc_eq_integral_Ioc,
    thm_7_9_symmetric_abs_rsTrunc_eq_integral_Ioc]
  have hnm' : n + 1 ≤ m + 1 := Nat.add_le_add_right hnm 1
  have hsubset :
      Ioc (-((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ⊆
        Ioc (-((m + 1 : ℕ) : ℝ)) ((m + 1 : ℕ) : ℝ) :=
    thm_7_9_nat_Ioc_subset hnm'
  exact setIntegral_mono_set hAbs.integrableOn
    (Filter.Eventually.of_forall fun x => abs_nonneg (g x))
    (Filter.Eventually.of_forall fun x hx => hsubset hx)
