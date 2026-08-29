/-
TASK ID: thm_6_5
TYPE: Theorem_with_Proof
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_6_4

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter

theorem thm_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hX : Measurable X) (hY : Measurable Y) (c : ENNReal) :
    ∫⁻ ω, X ω + Y ω ∂μ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ ∧
      ∫⁻ ω, c * X ω ∂μ = c * ∫⁻ ω, X ω ∂μ := by
  have mct_eq_iSup (f : ℕ → Ω → ENNReal) (F : Ω → ENNReal)
      (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f)
      (h_sup : ∀ ω, (⨆ n, f n ω) = F ω) :
      ∫⁻ ω, F ω ∂μ = ⨆ n, ∫⁻ ω, f n ω ∂μ := by
    have h_int_mono : Monotone fun n => ∫⁻ ω, f n ω ∂μ := by
      intro i j hij
      exact lintegral_mono (fun ω => h_mono hij ω)
    exact tendsto_nhds_unique
      (thm_6_4 μ f F hf h_mono h_sup)
      (tendsto_atTop_iSup h_int_mono)
  have hX_mct :
      ∫⁻ ω, X ω ∂μ = ⨆ n, (SimpleFunc.eapprox X n).lintegral μ := by
    calc
      ∫⁻ ω, X ω ∂μ =
          ⨆ n, ∫⁻ ω, (SimpleFunc.eapprox X n : Ω → ENNReal) ω ∂μ := by
        apply mct_eq_iSup
        · exact fun n => (SimpleFunc.eapprox X n).measurable
        · intro i j hij ω
          exact SimpleFunc.monotone_eapprox X hij ω
        · exact SimpleFunc.iSup_eapprox_apply hX
      _ = ⨆ n, (SimpleFunc.eapprox X n).lintegral μ := by
        congr
        funext n
        rw [SimpleFunc.lintegral_eq_lintegral]
  have hY_mct :
      ∫⁻ ω, Y ω ∂μ = ⨆ n, (SimpleFunc.eapprox Y n).lintegral μ := by
    calc
      ∫⁻ ω, Y ω ∂μ =
          ⨆ n, ∫⁻ ω, (SimpleFunc.eapprox Y n : Ω → ENNReal) ω ∂μ := by
        apply mct_eq_iSup
        · exact fun n => (SimpleFunc.eapprox Y n).measurable
        · intro i j hij ω
          exact SimpleFunc.monotone_eapprox Y hij ω
        · exact SimpleFunc.iSup_eapprox_apply hY
      _ = ⨆ n, (SimpleFunc.eapprox Y n).lintegral μ := by
        congr
        funext n
        rw [SimpleFunc.lintegral_eq_lintegral]
  refine ⟨?_, ?_⟩
  · have h_add_mct :
        ∫⁻ ω, X ω + Y ω ∂μ =
          ⨆ n, ∫⁻ ω,
            (SimpleFunc.eapprox X n : Ω → ENNReal) ω +
              (SimpleFunc.eapprox Y n : Ω → ENNReal) ω ∂μ := by
      apply mct_eq_iSup
      · intro n
        exact (SimpleFunc.eapprox X n).measurable.add (SimpleFunc.eapprox Y n).measurable
      · intro i j hij ω
        exact add_le_add
          (SimpleFunc.monotone_eapprox X hij ω)
          (SimpleFunc.monotone_eapprox Y hij ω)
      · intro ω
        have hX_mono : Monotone fun n => (SimpleFunc.eapprox X n) ω := by
          intro i j hij
          exact SimpleFunc.monotone_eapprox X hij ω
        have hY_mono : Monotone fun n => (SimpleFunc.eapprox Y n) ω := by
          intro i j hij
          exact SimpleFunc.monotone_eapprox Y hij ω
        calc
          (⨆ n, (SimpleFunc.eapprox X n) ω + (SimpleFunc.eapprox Y n) ω) =
              (⨆ n, (SimpleFunc.eapprox X n) ω) +
                ⨆ n, (SimpleFunc.eapprox Y n) ω :=
            (ENNReal.iSup_add_iSup_of_monotone hX_mono hY_mono).symm
          _ = X ω + Y ω := by
            rw [SimpleFunc.iSup_eapprox_apply hX, SimpleFunc.iSup_eapprox_apply hY]
    calc
      ∫⁻ ω, X ω + Y ω ∂μ =
          ⨆ n, ∫⁻ ω,
            (SimpleFunc.eapprox X n : Ω → ENNReal) ω +
              (SimpleFunc.eapprox Y n : Ω → ENNReal) ω ∂μ := h_add_mct
      _ = ⨆ n,
          (SimpleFunc.eapprox X n).lintegral μ +
            (SimpleFunc.eapprox Y n).lintegral μ := by
        congr
        funext n
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [Pi.add_apply, SimpleFunc.coe_add]
      _ = (⨆ n, (SimpleFunc.eapprox X n).lintegral μ) +
          ⨆ n, (SimpleFunc.eapprox Y n).lintegral μ := by
        refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm
        · intro i j hij
          exact SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox X hij) le_rfl
        · intro i j hij
          exact SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox Y hij) le_rfl
      _ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ := by
        rw [← hX_mct, ← hY_mct]
  · have h_mul_mct :
        ∫⁻ ω, c * X ω ∂μ =
          ⨆ n, ∫⁻ ω, c * (SimpleFunc.eapprox X n : Ω → ENNReal) ω ∂μ := by
      apply mct_eq_iSup
      · intro n
        exact measurable_const.mul (SimpleFunc.eapprox X n).measurable
      · intro i j hij ω
        exact mul_le_mul_left' (SimpleFunc.monotone_eapprox X hij ω) c
      · intro ω
        rw [← SimpleFunc.iSup_eapprox_apply hX ω, ENNReal.mul_iSup]
    calc
      ∫⁻ ω, c * X ω ∂μ =
          ⨆ n, ∫⁻ ω, c * (SimpleFunc.eapprox X n : Ω → ENNReal) ω ∂μ := h_mul_mct
      _ = ⨆ n, c * (SimpleFunc.eapprox X n).lintegral μ := by
        congr
        funext n
        rw [← SimpleFunc.const_mul_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [SimpleFunc.coe_mul, SimpleFunc.coe_const, Pi.mul_apply,
          Function.const_apply]
      _ = c * ⨆ n, (SimpleFunc.eapprox X n).lintegral μ := by
        rw [ENNReal.mul_iSup]
      _ = c * ∫⁻ ω, X ω ∂μ := by
        rw [← hX_mct]
