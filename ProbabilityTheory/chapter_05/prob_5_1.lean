/-
TASK ID: prob_5_1
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set ProbabilityTheory

theorem prob_5_1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (g h : ℝ → ENNReal) (hg : Measurable g) (hh : Measurable h)
    [HasPDF (fun ω => (X ω, Y ω)) P (volume : Measure (ℝ × ℝ))]
    (h_factor : ∀ z : ℝ × ℝ, pdf (fun ω => (X ω, Y ω)) P volume z = g z.1 * h z.2) :
    IndepFun X Y P := by
  let μg : Measure ℝ := volume.withDensity g
  let μh : Measure ℝ := volume.withDensity h
  have h_joint : Measure.map (fun ω => (X ω, Y ω)) P = μg.prod μh := by
    have h_pdf :
        Measure.map (fun ω => (X ω, Y ω)) P =
          volume.withDensity (fun z : ℝ × ℝ ↦ pdf (fun ω => (X ω, Y ω)) P volume z) := by
      exact map_eq_withDensity_pdf (fun ω => (X ω, Y ω)) P volume
    calc
      Measure.map (fun ω => (X ω, Y ω)) P =
          volume.withDensity (fun z : ℝ × ℝ ↦ pdf (fun ω => (X ω, Y ω)) P volume z) := h_pdf
      _ = volume.withDensity (fun z : ℝ × ℝ ↦ g z.1 * h z.2) := by
        congr with z
        exact h_factor z
      _ = μg.prod μh := by
        rw [Measure.volume_eq_prod]
        simpa [μg, μh] using
          (prod_withDensity₀ (μ := volume) (ν := volume)
            hg.aemeasurable hh.aemeasurable).symm
  have h_mapX : Measure.map X P = μh Set.univ • μg := by
    have h_map :
        Measure.map X P = Measure.map Prod.fst (Measure.map (fun ω => (X ω, Y ω)) P) := by
      rw [Measure.map_map]
      exacts [rfl, measurable_fst, hX.prodMk hY]
    calc
      Measure.map X P = Measure.map Prod.fst (Measure.map (fun ω => (X ω, Y ω)) P) := h_map
      _ = Measure.map Prod.fst (μg.prod μh) := by rw [h_joint]
      _ = μh Set.univ • μg := by simpa [μg, μh]
  have h_mapY : Measure.map Y P = μg Set.univ • μh := by
    have h_map :
        Measure.map Y P = Measure.map Prod.snd (Measure.map (fun ω => (X ω, Y ω)) P) := by
      rw [Measure.map_map]
      exacts [rfl, measurable_snd, hX.prodMk hY]
    calc
      Measure.map Y P = Measure.map Prod.snd (Measure.map (fun ω => (X ω, Y ω)) P) := h_map
      _ = Measure.map Prod.snd (μg.prod μh) := by rw [h_joint]
      _ = μg Set.univ • μh := by simpa [μg, μh]
  have h_norm : μh Set.univ * (μg Set.univ) = 1 := by
    have h_left : Measure.map (fun ω => (X ω, Y ω)) P Set.univ = 1 := by
      rw [Measure.map_apply (hX.prodMk hY) MeasurableSet.univ]
      simp
    have h_right : (μg.prod μh) Set.univ = μg Set.univ * μh Set.univ := by
      simp [μg, μh, Measure.prod_apply, MeasurableSet.univ, mul_comm]
    rw [← h_left, h_joint, h_right, mul_comm]
  refine (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).2 ?_
  rw [h_mapX, h_mapY, Measure.prod_smul_left, Measure.prod_smul_right]
  rw [← smul_assoc, smul_eq_mul, h_norm, one_smul]
  exact h_joint
