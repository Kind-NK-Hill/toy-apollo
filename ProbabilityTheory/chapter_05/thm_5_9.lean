/-
TASK ID: thm_5_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Probability.BorelCantelli
import ProbabilityTheory.chapter_05.thm_5_6







-- WRITE FINAL LEAN CODE BELOW
open Filter
open scoped ENNReal Topology



theorem thm_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P)
    (h_series : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 := by
  classical
  -- This is the countable-index version of the complement replacement used
  -- in `thm_5_6`: `generateFrom {A nᶜ}` is contained in
  -- `generateFrom {A n}`, so the original independent family remains
  -- independent after every event is complemented.
  have h_compl_indep : ProbabilityTheory.iIndepSet (fun n => (A n)ᶜ) P := by
    rw [ProbabilityTheory.iIndepSet_iff_iIndep] at h_indep ⊢
    apply ProbabilityTheory.iIndep_of_iIndep_of_le h_indep
    intro n
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    exact
      (MeasurableSpace.measurableSet_generateFrom
        (show A n ∈ ({A n} : Set (Set Ω)) by simp)).compl
  -- Thus the finite complement intersections in the textbook proof are
  -- products.  In particular this records the exact finite event route,
  -- rather than treating the second Borel--Cantelli conclusion as an
  -- unanalysed interface.
  have h_finite_compl_product (s : Finset ℕ) :
      P (⋂ n ∈ (s : Set ℕ), (A n)ᶜ) = ∏ n ∈ s, P ((A n)ᶜ) := by
    simpa using h_compl_indep.meas_biInter s
  have h_tail_finite_product (k m : ℕ) :
      P (⋂ n ∈ (Finset.range m : Set ℕ), (A (k + n))ᶜ) =
        ∏ n ∈ Finset.range m, P ((A (k + n))ᶜ) := by
    simpa using h_finite_compl_product ((Finset.range m).image (k + ·))
  -- The numerical inputs are also recorded in their textbook form.  Each
  -- tail still diverges (remove finitely many finite probabilities), and the
  -- one-event estimate is `1 - p ≤ exp (-p)` after taking `toReal`.
  have h_tail_series : ∀ k : ℕ, (∑' n, P (A (k + n))) = ∞ := by
    intro k
    induction k with
    | zero => simpa using h_series
    | succ k ih =>
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ENNReal.tsum_add_one_eq_top ih (MeasureTheory.measure_ne_top P _)
  have h_one_sub_exp (n : ℕ) :
      1 - (P (A n)).toReal ≤ Real.exp (-(P (A n)).toReal) :=
    Real.one_sub_le_exp_neg _
  have h_compl_toReal (n : ℕ) :
      (P ((A n)ᶜ)).toReal = 1 - (P (A n)).toReal := by
    rw [MeasureTheory.measure_compl (h_meas n) (by finiteness)]
    rw [ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono (Set.subset_univ _))
      (MeasureTheory.measure_ne_top P Set.univ)]
    simp
  -- Every infinite tail of complements has probability zero.  It is
  -- contained in each finite initial block of that tail; independence turns
  -- the block measure into a product, and `1-p ≤ exp (-p)` squeezes the
  -- fixed tail measure to zero as the partial probability sums diverge.
  have h_tail_compl_zero (k : ℕ) :
      P (⋂ j : ℕ, (A (k + j))ᶜ) = 0 := by
    have h_tail_subset (m : ℕ) :
        (⋂ j : ℕ, (A (k + j))ᶜ) ⊆
          ⋂ j ∈ (Finset.range m : Set ℕ), (A (k + j))ᶜ := by
      intro ω hω
      simp only [Set.mem_iInter] at hω ⊢
      intro j _hj
      exact hω j
    have h_block_bound (m : ℕ) :
        (P (⋂ j : ℕ, (A (k + j))ᶜ)).toReal ≤
          Real.exp (-(∑ j ∈ Finset.range m, (P (A (k + j))).toReal)) := by
      calc
        (P (⋂ j : ℕ, (A (k + j))ᶜ)).toReal
            ≤ (P (⋂ j ∈ (Finset.range m : Set ℕ), (A (k + j))ᶜ)).toReal := by
              exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top P _)
                (MeasureTheory.measure_mono (h_tail_subset m))
        _ = ∏ j ∈ Finset.range m, (P ((A (k + j))ᶜ)).toReal := by
              rw [h_tail_finite_product k m, ENNReal.toReal_prod]
        _ = ∏ j ∈ Finset.range m, (1 - (P (A (k + j))).toReal) := by
              apply Finset.prod_congr rfl
              intro j _hj
              exact h_compl_toReal (k + j)
        _ ≤ ∏ j ∈ Finset.range m,
              Real.exp (-(P (A (k + j))).toReal) := by
              refine Finset.prod_le_prod ?_ ?_
              · intro j _hj
                rw [← h_compl_toReal (k + j)]
                exact ENNReal.toReal_nonneg
              · intro j _hj
                exact h_one_sub_exp (k + j)
        _ = Real.exp (-(∑ j ∈ Finset.range m, (P (A (k + j))).toReal)) := by
              rw [← Real.exp_sum]
              congr 1
              rw [Finset.sum_neg_distrib]
    have h_ennreal_partial :
        Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, P (A (k + j)))
          atTop (𝓝 ∞) := by
      simpa [h_tail_series k] using
        (ENNReal.tendsto_nat_tsum (fun j => P (A (k + j))))
    have h_real_partial :
        Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (P (A (k + j))).toReal)
          atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨q : ℕ, hq : b < q⟩ := exists_nat_gt b
      let x : NNReal := q
      have hx : b < (x : ℝ) := by exact_mod_cast hq
      have hx_eventually :
          ∀ᶠ m : ℕ in atTop,
            (x : ℝ≥0∞) < ∑ j ∈ Finset.range m, P (A (k + j)) :=
        (ENNReal.tendsto_nhds_top_iff_nnreal.mp h_ennreal_partial) x
      rw [Filter.eventually_atTop] at hx_eventually
      obtain ⟨N, hN⟩ := hx_eventually
      refine ⟨N, fun m hm => le_of_lt (hx.trans ?_)⟩
      have hsum_ne_top :
          (∑ j ∈ Finset.range m, P (A (k + j))) ≠ ∞ := by
        exact ENNReal.sum_ne_top.mpr fun j _hj => MeasureTheory.measure_ne_top P _
      have hlt :
          (x : ℝ) < (∑ j ∈ Finset.range m, P (A (k + j))).toReal :=
        (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hsum_ne_top).2 (hN m hm)
      simpa only [ENNReal.toReal_sum
        (fun j _hj => MeasureTheory.measure_ne_top P (A (k + j)))] using hlt
    have h_exp_zero :
        Tendsto
          (fun m : ℕ => Real.exp
            (-(∑ j ∈ Finset.range m, (P (A (k + j))).toReal)))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h_real_partial)
    have h_toReal_nonpos :
        (P (⋂ j : ℕ, (A (k + j))ᶜ)).toReal ≤ 0 :=
      ge_of_tendsto' h_exp_zero h_block_bound
    have h_toReal_zero :
        (P (⋂ j : ℕ, (A (k + j))ᶜ)).toReal = 0 :=
      le_antisymm h_toReal_nonpos ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).mp h_toReal_zero with hzero | htop
    · exact hzero
    · exact ((MeasureTheory.measure_ne_top P _) htop).elim
  -- The complement of the limsup is the countable union of those null tail
  -- intersections.  Countable subadditivity therefore makes it null, and
  -- the probability-complement identity gives measure one to the limsup.
  have h_limsup_compl :
      (limsup A atTop)ᶜ = ⋃ k : ℕ, ⋂ j : ℕ, (A (k + j))ᶜ := by
    ext ω
    simp [Filter.limsup_eq_iInf_iSup_of_nat', Nat.add_comm]
  have h_compl_zero : P ((limsup A atTop)ᶜ) = 0 := by
    rw [h_limsup_compl]
    exact MeasureTheory.measure_iUnion_null h_tail_compl_zero
  have h_limsup_meas : MeasurableSet (limsup A atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat']
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => h_meas (j + k)
  rw [MeasureTheory.measure_compl h_limsup_meas (MeasureTheory.measure_ne_top P _),
    MeasureTheory.measure_univ] at h_compl_zero
  apply le_antisymm
  · have hmono : P (limsup A atTop) ≤ P (Set.univ : Set Ω) :=
      MeasureTheory.measure_mono (Set.subset_univ (limsup A atTop))
    simpa [MeasureTheory.measure_univ] using hmono
  · exact tsub_eq_zero_iff_le.mp h_compl_zero
