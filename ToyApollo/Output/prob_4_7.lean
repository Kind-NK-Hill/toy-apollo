import Mathlib

open Set
open MeasureTheory
open Topology

noncomputable section

private def ratInterval : Set (Set ℝ) :=
  {s | ∃ a b : ℚ, s = Set.Ioo (a : ℝ) (b : ℝ)}

private def ratRect : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun u v => u ×ˢ v) ratInterval ratInterval

private lemma ratInterval_basis : TopologicalSpace.IsTopologicalBasis ratInterval := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro u hu
    rcases hu with ⟨a, b, rfl⟩
    exact isOpen_Ioo
  · intro x u hx hu
    have hu_nhds : u ∈ 𝓝 x := hu.mem_nhds hx
    rw [mem_nhds_iff_exists_Ioo_subset] at hu_nhds
    rcases hu_nhds with ⟨l, r, hxIoo, hsub⟩
    rcases exists_rat_btwn hxIoo.1 with ⟨a, hla, hax⟩
    rcases exists_rat_btwn hxIoo.2 with ⟨b, hxb, hbr⟩
    refine ⟨Set.Ioo (a : ℝ) (b : ℝ), ?_, ?_, ?_⟩
    · exact ⟨a, b, rfl⟩
    · exact ⟨hax, hxb⟩
    · intro y hy
      apply hsub
      exact ⟨lt_trans hla hy.1, lt_trans hy.2 hbr⟩

private lemma ratRect_basis : TopologicalSpace.IsTopologicalBasis ratRect := by
  have hprod := TopologicalSpace.IsTopologicalBasis.prod ratInterval_basis ratInterval_basis
  simpa [ratRect] using hprod

private lemma borel_prod_eq_generateFrom_ratRect :
    borel (ℝ × ℝ) = MeasurableSpace.generateFrom ratRect := by
  exact borel_eq_generateFrom_of_subbasis ratRect_basis.eq_generateFrom

private lemma measurable_of_open_ratRect {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    @MeasurableSet (ℝ × ℝ) (MeasurableSpace.generateFrom ratRect) U := by
  have hInst : (inferInstance : MeasurableSpace (ℝ × ℝ)) = borel (ℝ × ℝ) := BorelSpace.measurable_eq
  have hMeas : @MeasurableSet (ℝ × ℝ) inferInstance U := hU.measurableSet
  have hBorel : @MeasurableSet (ℝ × ℝ) (borel (ℝ × ℝ)) U := by
    rwa [← hInst]
  exact borel_prod_eq_generateFrom_ratRect ▸ hBorel

theorem prob_4_7 :
    let mF : MeasurableSpace (ℝ × ℝ) := MeasurableSpace.generateFrom ratRect
    (∀ p q r s : ℝ, @MeasurableSet (ℝ × ℝ) mF (Set.Ioo p q ×ˢ Set.Ioo r s)) ∧
      (∀ a b : ℚ, @MeasurableSet (ℝ × ℝ) mF (Set.Iio (a : ℝ) ×ˢ Set.Iio (b : ℝ))) ∧
      (∀ a b c : ℝ, @MeasurableSet (ℝ × ℝ) mF {z : ℝ × ℝ | a * z.1 + b * z.2 < c}) := by
  dsimp
  constructor
  · intro p q r s
    exact measurable_of_open_ratRect (isOpen_Ioo.prod isOpen_Ioo)
  · constructor
    · intro a b
      exact measurable_of_open_ratRect (isOpen_Iio.prod isOpen_Iio)
    · intro a b c
      have hOpen : IsOpen {z : ℝ × ℝ | a * z.1 + b * z.2 < c} := by
        have hcont : Continuous fun z : ℝ × ℝ => a * z.1 + b * z.2 := by
          continuity
        exact isOpen_lt hcont continuous_const
      exact measurable_of_open_ratRect hOpen
