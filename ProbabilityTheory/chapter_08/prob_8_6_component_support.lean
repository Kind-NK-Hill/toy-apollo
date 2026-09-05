/-
TASK ID: prob_8_6_component_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_08.prob_8_6_convolution_support

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

 
def pmfConvList : List (ℕ → ℝ) → ℕ → ℝ
  | [] => fun k => if k = 0 then 1 else 0
  | f :: fs => pmfConv f (pmfConvList fs)

lemma pmfConvList_nonneg :
    ∀ (fs : List (ℕ → ℝ)),
      (∀ f ∈ fs, ∀ k, 0 ≤ f k) →
      ∀ k, 0 ≤ pmfConvList fs k
  | [], _, k => by
      cases k <;> simp [pmfConvList]
  | f :: fs, hnn, k => by
      have h_tail :
          ∀ g ∈ fs, ∀ m, 0 ≤ g m := by
        intro g hg m
        exact hnn g (by simp [hg]) m
      exact pmfConv_nonneg f (pmfConvList fs)
        (hnn f (by simp)) (pmfConvList_nonneg fs h_tail) k

lemma pmfConvList_sum_one :
    ∀ (fs : List (ℕ → ℝ)),
      (∀ f ∈ fs, ∀ k, 0 ≤ f k) →
      (∀ f ∈ fs, HasSum f 1) →
      HasSum (pmfConvList fs) 1
  | [], _, _ => by
      exact hasSum_ite_eq 0 1
  | f :: fs, hnn, hsum => by
      have h_tail_nn :
          ∀ g ∈ fs, ∀ k, 0 ≤ g k := by
        intro g hg k
        exact hnn g (by simp [hg]) k
      have h_tail_sum :
          ∀ g ∈ fs, HasSum g 1 := by
        intro g hg
        exact hsum g (by simp [hg])
      exact pmfConv_hasSum f (pmfConvList fs)
        (hnn f (by simp)) (hsum f (by simp))
        (pmfConvList_nonneg fs h_tail_nn)
        (pmfConvList_sum_one fs h_tail_nn h_tail_sum)

 
def unitIntervalPointToNNReal (p : Set.Icc (0 : ℝ) 1) : NNReal :=
  ⟨p.1, p.2.1⟩

lemma unitIntervalPointToNNReal_le_one (p : Set.Icc (0 : ℝ) 1) :
    unitIntervalPointToNNReal p ≤ 1 := by
  exact_mod_cast p.2.2

 
noncomputable def prob_8_6_part_c_componentCoupling
    (lam : List (Set.Icc (0 : ℝ) 1)) (i : Fin lam.length) :
    DiscretePmfCoupling
      (bernoulliNatPMF (unitIntervalPointToNNReal (lam.get i))
        (unitIntervalPointToNNReal_le_one (lam.get i)))
      (ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal (lam.get i))) := by
  let p := lam.get i
  exact prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)



def prob_8_6_part_c_hatXLaw (lam : List (Set.Icc (0 : ℝ) 1)) : ℕ → ℝ :=
  pmfConvList (lam.map fun p => Ber p.1)



def prob_8_6_part_c_hatYLaw (lam : List (Set.Icc (0 : ℝ) 1)) : ℕ → ℝ :=
  pmfConvList (lam.map fun p => Poi p.1)

 
def prob_8_6_part_c_componentMismatchMasses (lam : List (Set.Icc (0 : ℝ) 1)) : List ℝ :=
  lam.map fun p =>
    discretePmfCouplingMismatchMass
      (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p))

lemma prob_8_6_part_c_head_tv_le_mismatchMass (p : Set.Icc (0 : ℝ) 1) :
    d_TV (Ber p.1) (Poi p.1)
      ≤ discretePmfCouplingMismatchMass
          (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) := by
  calc
    d_TV (Ber p.1) (Poi p.1)
        =
          d_TV
            (fun n => ((bernoulliNatPMF (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) n).toReal)
            (fun n => ((ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal p)) n).toReal) := by
          change
            d_TV (Ber (unitIntervalPointToNNReal p : ℝ)) (Poi (unitIntervalPointToNNReal p : ℝ))
              =
                d_TV
                  (fun n =>
                    ((bernoulliNatPMF (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) n).toReal)
                  (fun n => ((ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal p)) n).toReal)
          rw [bernoulliNatPMF_toReal_eq_Ber (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)]
          rw [poissonPMF_toReal_eq_Poi (unitIntervalPointToNNReal p)]
    _ =
        totalVariationDistance
          (bernoulliNatPMF (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)).toMeasure
          (ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal p)).toMeasure := by
          symm
          simpa [d_TV] using
            thm_8_6_discrete_pmf
              (bernoulliNatPMF (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p))
              (ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal p))
    _ ≤ discretePmfCouplingMismatchMass
          (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) :=
        prob_8_6_part_b_tv_le_mismatchMass (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)



theorem prob_8_6_part_c_coupling_bound (lam : List (Set.Icc (0 : ℝ) 1)) :
    d_TV
        (prob_8_6_part_c_hatXLaw lam)
        (prob_8_6_part_c_hatYLaw lam)
      ≤ List.sum (prob_8_6_part_c_componentMismatchMasses lam) := by
  unfold prob_8_6_part_c_hatXLaw prob_8_6_part_c_hatYLaw
  unfold prob_8_6_part_c_componentMismatchMasses
  induction lam with
  | nil =>
      simp [pmfConvList, d_TV_self]
  | cons p ps ih =>
      let f := Ber p.1
      let g := Poi p.1
      let fs := ps.map fun q => Ber q.1
      let gs := ps.map fun q => Poi q.1
      have hfs_nn : ∀ h ∈ fs, ∀ k, 0 ≤ h k := by
        intro h hh k
        rcases List.mem_map.1 hh with ⟨q, hq, rfl⟩
        exact ber_nonneg q.1 q.2.1 q.2.2 k
      have hgs_nn : ∀ h ∈ gs, ∀ k, 0 ≤ h k := by
        intro h hh k
        rcases List.mem_map.1 hh with ⟨q, hq, rfl⟩
        exact poi_nonneg q.1 q.2.1 k
      have hfs_sum : ∀ h ∈ fs, HasSum h 1 := by
        intro h hh
        rcases List.mem_map.1 hh with ⟨q, hq, rfl⟩
        exact ber_sum_one q.1
      have hgs_sum : ∀ h ∈ gs, HasSum h 1 := by
        intro h hh
        rcases List.mem_map.1 hh with ⟨q, hq, rfl⟩
        exact poi_sum_one q.1 q.2.1
      have hFs_sum : HasSum (pmfConvList fs) 1 :=
        pmfConvList_sum_one fs hfs_nn hfs_sum
      have hGs_sum : HasSum (pmfConvList gs) 1 :=
        pmfConvList_sum_one gs hgs_nn hgs_sum
      have hFs_nn : ∀ k, 0 ≤ pmfConvList fs k :=
        pmfConvList_nonneg fs hfs_nn
      have hGs_nn : ∀ k, 0 ≤ pmfConvList gs k :=
        pmfConvList_nonneg gs hgs_nn
      have h_triangle :
          d_TV (pmfConv f (pmfConvList fs)) (pmfConv g (pmfConvList gs))
            ≤ d_TV (pmfConv f (pmfConvList fs)) (pmfConv f (pmfConvList gs))
                + d_TV (pmfConv f (pmfConvList gs)) (pmfConv g (pmfConvList gs)) := by
        apply d_TV_triangle
        · exact pmfConv_summable f (pmfConvList fs) (ber_sum_one p.1).summable hFs_sum.summable
        · exact pmfConv_summable f (pmfConvList gs) (ber_sum_one p.1).summable hGs_sum.summable
        · exact pmfConv_summable g (pmfConvList gs) (poi_sum_one p.1 p.2.1).summable hGs_sum.summable
      have h_left :
          d_TV (pmfConv f (pmfConvList fs)) (pmfConv f (pmfConvList gs))
            ≤ d_TV (pmfConvList fs) (pmfConvList gs) := by
        have h_abs :
            Summable (fun k => |pmfConvList fs k - pmfConvList gs k|) :=
          (hFs_sum.summable.sub hGs_sum.summable).abs
        exact d_TV_conv_contract_left f _ _ (ber_nonneg p.1 p.2.1 p.2.2) (ber_sum_one p.1) h_abs
      have h_right :
          d_TV (pmfConv f (pmfConvList gs)) (pmfConv g (pmfConvList gs))
            ≤ d_TV f g := by
        have h_abs : Summable (fun k => |f k - g k|) :=
          ((ber_sum_one p.1).summable.sub (poi_sum_one p.1 p.2.1).summable).abs
        exact d_TV_conv_contract_right f g (pmfConvList gs) hGs_nn hGs_sum h_abs
      have h_head :
          d_TV f g
            ≤ discretePmfCouplingMismatchMass
                (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) := by
        simpa [f, g] using prob_8_6_part_c_head_tv_le_mismatchMass p
      have h_tail :
          d_TV (pmfConvList fs) (pmfConvList gs)
            ≤ List.sum
                (ps.map fun q =>
                  discretePmfCouplingMismatchMass
                    (prob_8_6_part_b_coupling (unitIntervalPointToNNReal q) (unitIntervalPointToNNReal_le_one q))) := by
        simpa [fs, gs] using ih
      have h_bound :
          d_TV (pmfConv f (pmfConvList fs)) (pmfConv g (pmfConvList gs))
            ≤ List.sum
                (ps.map fun q =>
                  discretePmfCouplingMismatchMass
                    (prob_8_6_part_b_coupling (unitIntervalPointToNNReal q) (unitIntervalPointToNNReal_le_one q)))
              + discretePmfCouplingMismatchMass
                  (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)) := by
        exact h_triangle.trans <| add_le_add (le_trans h_left h_tail) (le_trans h_right h_head)
      change
        d_TV (pmfConv f (pmfConvList fs)) (pmfConv g (pmfConvList gs))
          ≤ discretePmfCouplingMismatchMass
                (prob_8_6_part_b_coupling
                  (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p))
              + List.sum
                  (ps.map fun q =>
                    discretePmfCouplingMismatchMass
                      (prob_8_6_part_b_coupling
                        (unitIntervalPointToNNReal q) (unitIntervalPointToNNReal_le_one q)))
      simpa only [add_comm] using h_bound

lemma prob_8_6_part_c_componentMismatchMass_le_sq (p : Set.Icc (0 : ℝ) 1) :
    discretePmfCouplingMismatchMass
        (prob_8_6_part_b_coupling (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p))
      ≤ p.1 ^ 2 := by
  exact
    prob_8_6_part_b_mismatchMass_le_sq
      (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)

 
theorem prob_8_6_part_c_componentMismatchMasses_le_sq (lam : List (Set.Icc (0 : ℝ) 1)) :
    List.sum (prob_8_6_part_c_componentMismatchMasses lam)
      ≤ List.sum (lam.map fun p => p.1 ^ 2) := by
  unfold prob_8_6_part_c_componentMismatchMasses
  induction lam with
  | nil =>
      simp
  | cons p ps ih =>
      simpa using add_le_add (prob_8_6_part_c_componentMismatchMass_le_sq p) ih



theorem prob_8_6_part_c (lam : List (Set.Icc (0 : ℝ) 1)) :
    d_TV
        (prob_8_6_part_c_hatXLaw lam)
        (prob_8_6_part_c_hatYLaw lam)
      ≤ List.sum (lam.map fun p => p.1 ^ 2) := by
  exact
    (prob_8_6_part_c_coupling_bound lam).trans
      (prob_8_6_part_c_componentMismatchMasses_le_sq lam)



theorem prob_8_6_part_c_componentCoupling_is_maximal
    (lam : List (Set.Icc (0 : ℝ) 1)) (i : Fin lam.length) :
    totalVariationDistance
        ((bernoulliNatPMF (unitIntervalPointToNNReal (lam.get i))
          (unitIntervalPointToNNReal_le_one (lam.get i))).toMeasure)
        (ProbabilityTheory.poissonPMF (unitIntervalPointToNNReal (lam.get i))).toMeasure
      = discretePmfCouplingMismatchMass (prob_8_6_part_c_componentCoupling lam i) := by
  let p := lam.get i
  simpa [prob_8_6_part_c_componentCoupling, p] using
    prob_8_6_part_b_coupling_is_maximal (unitIntervalPointToNNReal p) (unitIntervalPointToNNReal_le_one p)



theorem prob_8_6_part_c_uniform (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    d_TV (pmfConvN (Ber p.1) n) (pmfConvN (Poi p.1) n) ≤ ↑n * p.1 ^ 2 := by
  have h1 := d_TV_convN_bound (Ber p.1) (Poi p.1)
    (ber_nonneg p.1 p.2.1 p.2.2) (ber_sum_one p.1)
    (poi_nonneg p.1 p.2.1) (poi_sum_one p.1 p.2.1) n
  have h2 := ber_poi_tv_le_sq p.1 p.2.1
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n))

-- ============================================================================
-- Auxiliary arithmetic lemma
-- ============================================================================
