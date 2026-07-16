import Mathlib
import ToyApollo.Output.thm_2_8
import ToyApollo.Output.thm_4_3
import ToyApollo.Output.thm_4_4

/-!
# Arithmetic operations on measurable real-valued functions

The proof follows the textbook generator/composition route.  In particular,
the pair map is checked on open rectangles, operation maps are proved Borel
measurable, and the totalized inverse is handled by explicit level sets.
-/

open Set MeasureTheory Topology

noncomputable section

def thm46RealOpenBalls : Set (Set ℝ) :=
  {A | ∃ c : ℝ, ∃ r : ℝ, 0 < r ∧ A = Metric.ball c r}

theorem thm46_realOpenBalls_generateFrom_eq_borel :
    MeasurableSpace.generateFrom thm46RealOpenBalls = borel ℝ := by
  simpa [thm46RealOpenBalls] using
    (metricOpenBalls_isTopologicalBasis (α := ℝ)).borel_eq_generateFrom.symm

theorem thm46_continuous_real_valued_measurable_from_openBalls
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (φ : X → ℝ) (hφ : Continuous φ) :
    Measurable φ := by
  have hgen :
      (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom thm46RealOpenBalls := by
    calc
      (inferInstance : MeasurableSpace ℝ) = borel ℝ := BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom thm46RealOpenBalls :=
        thm46_realOpenBalls_generateFrom_eq_borel.symm
  have hsrc :
      @Measurable X ℝ inferInstance (MeasurableSpace.generateFrom thm46RealOpenBalls) φ := by
    exact (thm_4_4 φ).2 (by
      rintro A ⟨c, r, _hr, rfl⟩
      exact (Metric.isOpen_ball.preimage hφ).measurableSet)
  convert hsrc using 1

def thm46OpenRectangles : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun u v => u ×ˢ v) realOpenIntervals realOpenIntervals

theorem thm46_realOpenIntervals_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis realOpenIntervals := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨a, b, _hab, rfl⟩
    exact isOpen_Ioo
  · intro x U hx hU
    have hUnhds : U ∈ 𝓝 x := hU.mem_nhds hx
    rw [mem_nhds_iff_exists_Ioo_subset] at hUnhds
    rcases hUnhds with ⟨a, b, hxIoo, hsub⟩
    exact ⟨Ioo a b, ⟨a, b, lt_trans hxIoo.1 hxIoo.2, rfl⟩, hxIoo, hsub⟩

theorem thm46_openRectangles_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis thm46OpenRectangles := by
  have hprod := TopologicalSpace.IsTopologicalBasis.prod
    thm46_realOpenIntervals_isTopologicalBasis thm46_realOpenIntervals_isTopologicalBasis
  simpa [thm46OpenRectangles] using hprod

theorem thm46_borel_prod_eq_generateFrom_openRectangles :
    borel (ℝ × ℝ) = MeasurableSpace.generateFrom thm46OpenRectangles := by
  exact borel_eq_generateFrom_of_subbasis thm46_openRectangles_isTopologicalBasis.eq_generateFrom

def thm46PairMap {Ω : Type*} (f g : Ω → ℝ) : Ω → ℝ × ℝ :=
  fun ω => (f ω, g ω)

theorem thm46_pairMap_preimage_openRectangles_measurable {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∀ R ∈ thm46OpenRectangles, MeasurableSet ((thm46PairMap f g) ⁻¹' R) := by
  rintro R ⟨U, hU, V, hV, rfl⟩
  rcases hU with ⟨a, b, _hab, rfl⟩
  rcases hV with ⟨c, d, _hcd, rfl⟩
  have hfI : MeasurableSet (f ⁻¹' Ioo a b) := hf measurableSet_Ioo
  have hgI : MeasurableSet (g ⁻¹' Ioo c d) := hg measurableSet_Ioo
  change MeasurableSet ((f ⁻¹' Ioo a b) ∩ (g ⁻¹' Ioo c d))
  exact hfI.inter hgI

theorem thm46_pairMap_measurable_from_rectangles {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (thm46PairMap f g) := by
  have hgen :
      (inferInstance : MeasurableSpace (ℝ × ℝ)) =
        MeasurableSpace.generateFrom thm46OpenRectangles := by
    calc
      (inferInstance : MeasurableSpace (ℝ × ℝ)) = borel (ℝ × ℝ) :=
        BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom thm46OpenRectangles :=
        thm46_borel_prod_eq_generateFrom_openRectangles
  have hsrc :
      @Measurable Ω (ℝ × ℝ) inferInstance
        (MeasurableSpace.generateFrom thm46OpenRectangles) (thm46PairMap f g) :=
    (thm_4_4 (thm46PairMap f g)).2
      (thm46_pairMap_preimage_openRectangles_measurable hf hg)
  convert hsrc using 1

def thm46AddMap : ℝ × ℝ → ℝ := fun z => z.1 + z.2
def thm46SubMap : ℝ × ℝ → ℝ := fun z => z.1 - z.2
def thm46MulMap : ℝ × ℝ → ℝ := fun z => z.1 * z.2
def thm46LinearMap (c : ℝ) : ℝ → ℝ := fun x => c * x
def thm46SquareMap : ℝ → ℝ := fun x => x ^ 2
def thm46InvMap : ℝ → ℝ := fun x => x⁻¹

theorem thm46_addMap_measurable_from_openBalls : Measurable thm46AddMap :=
  thm46_continuous_real_valued_measurable_from_openBalls thm46AddMap (by
    unfold thm46AddMap
    continuity)

theorem thm46_subMap_measurable_from_openBalls : Measurable thm46SubMap :=
  thm46_continuous_real_valued_measurable_from_openBalls thm46SubMap (by
    unfold thm46SubMap
    continuity)

theorem thm46_mulMap_measurable_from_openBalls : Measurable thm46MulMap :=
  thm46_continuous_real_valued_measurable_from_openBalls thm46MulMap (by
    unfold thm46MulMap
    continuity)

theorem thm46_linearMap_measurable_from_openBalls (c : ℝ) :
    Measurable (thm46LinearMap c) :=
  thm46_continuous_real_valued_measurable_from_openBalls (thm46LinearMap c) (by
    unfold thm46LinearMap
    continuity)

theorem thm46_squareMap_measurable_from_openBalls : Measurable thm46SquareMap :=
  thm46_continuous_real_valued_measurable_from_openBalls thm46SquareMap (by
    unfold thm46SquareMap
    continuity)

theorem thm46_invMap_preimage_Iio_of_pos {b : ℝ} (hb : 0 < b) :
    thm46InvMap ⁻¹' Iio b = Iic 0 ∪ Ioi b⁻¹ := by
  ext x
  change x⁻¹ < b ↔ x ≤ 0 ∨ b⁻¹ < x
  constructor
  · intro hxinv
    by_cases hx : x ≤ 0
    · exact Or.inl hx
    · exact Or.inr ((inv_lt_comm₀ (lt_of_not_ge hx) hb).mp hxinv)
  · rintro (hx | hx)
    · exact lt_of_le_of_lt (inv_nonpos.mpr hx) hb
    · have hbinv : 0 < b⁻¹ := inv_pos.mpr hb
      exact (inv_lt_comm₀ (lt_trans hbinv hx) hb).mpr hx

theorem thm46_invMap_preimage_Iio_zero :
    thm46InvMap ⁻¹' Iio 0 = Iio 0 := by
  ext x
  change x⁻¹ < 0 ↔ x < 0
  exact inv_lt_zero'

theorem thm46_invMap_preimage_Iio_of_neg {b : ℝ} (hb : b < 0) :
    thm46InvMap ⁻¹' Iio b = Ioo b⁻¹ 0 := by
  ext x
  change x⁻¹ < b ↔ b⁻¹ < x ∧ x < 0
  constructor
  · intro hxinv
    have hx : x < 0 := inv_lt_zero'.mp (lt_trans hxinv hb)
    exact ⟨(inv_lt_of_neg hx hb).mp hxinv, hx⟩
  · rintro ⟨hbx, hx⟩
    exact (inv_lt_of_neg hx hb).mpr hbx

theorem thm46_invMap_preimage_Iio_measurable (b : ℝ) :
    MeasurableSet (thm46InvMap ⁻¹' Iio b) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [thm46_invMap_preimage_Iio_of_neg hb]
    exact measurableSet_Ioo
  · rw [thm46_invMap_preimage_Iio_zero]
    exact measurableSet_Iio
  · rw [thm46_invMap_preimage_Iio_of_pos hb]
    exact measurableSet_Iic.union measurableSet_Ioi

theorem thm46_invMap_measurable_from_levelSets : Measurable thm46InvMap :=
  measurable_of_Iio thm46_invMap_preimage_Iio_measurable

theorem thm46_invMap_measurable_totalBridge : Measurable thm46InvMap :=
  thm46_invMap_measurable_from_levelSets

theorem thm46_mulMap_product_identity (z : ℝ × ℝ) :
    thm46MulMap z =
      (1 / 2 : ℝ) *
        (((z.1 + z.2) ^ 2) - z.1 ^ 2 - z.2 ^ 2) := by
  unfold thm46MulMap
  ring

theorem thm46_measurable_add_via_pair_and_composition {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω + g ω) := by
  have hpair := thm46_pairMap_measurable_from_rectangles hf hg
  have hcomp := measurable_composition
    (f := thm46PairMap f g) (g := thm46AddMap) hpair thm46_addMap_measurable_from_openBalls
  change Measurable (fun ω => f ω + g ω) at hcomp
  exact hcomp

theorem thm46_measurable_sub_via_pair_and_composition {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω - g ω) := by
  have hpair := thm46_pairMap_measurable_from_rectangles hf hg
  have hcomp := measurable_composition
    (f := thm46PairMap f g) (g := thm46SubMap) hpair thm46_subMap_measurable_from_openBalls
  change Measurable (fun ω => f ω - g ω) at hcomp
  exact hcomp

theorem thm46_measurable_linear_via_composition {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ℝ} (c : ℝ) (hf : Measurable f) :
    Measurable (fun ω => c * f ω) := by
  have hcomp := measurable_composition
    (f := f) (g := thm46LinearMap c) hf (thm46_linearMap_measurable_from_openBalls c)
  change Measurable (fun ω => c * f ω) at hcomp
  exact hcomp

theorem thm46_measurable_square_via_composition {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (fun ω => (f ω) ^ 2) := by
  have hcomp := measurable_composition
    (f := f) (g := thm46SquareMap) hf thm46_squareMap_measurable_from_openBalls
  change Measurable (fun ω => (f ω) ^ 2) at hcomp
  exact hcomp

theorem thm46_measurable_inv_via_totalBridge {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (fun ω => (f ω)⁻¹) := by
  have hcomp := measurable_composition
    (f := f) (g := thm46InvMap) hf thm46_invMap_measurable_from_levelSets
  change Measurable (fun ω => thm46InvMap (f ω)) at hcomp
  change Measurable (fun ω => thm46InvMap (f ω))
  exact hcomp

theorem thm46_measurable_mul_via_product_identity {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω * g ω) := by
  have hfg_add := thm46_measurable_add_via_pair_and_composition hf hg
  have hfg_add_sq := thm46_measurable_square_via_composition hfg_add
  have hf_sq := thm46_measurable_square_via_composition hf
  have hg_sq := thm46_measurable_square_via_composition hg
  have hsub1 := thm46_measurable_sub_via_pair_and_composition hfg_add_sq hf_sq
  have hsub2 := thm46_measurable_sub_via_pair_and_composition hsub1 hg_sq
  have hscaled := thm46_measurable_linear_via_composition (1 / 2 : ℝ) hsub2
  convert hscaled using 1
  ext ω
  ring

theorem thm46_measurable_div_via_inverse {Ω : Type*}
    [MeasurableSpace Ω] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (_hgz : ∀ ω, g ω ≠ 0) :
    Measurable (fun ω => f ω / g ω) := by
  have hginv := thm46_measurable_inv_via_totalBridge hg
  have hprod := thm46_measurable_mul_via_product_identity hf hginv
  simpa [div_eq_mul_inv] using hprod

theorem thm_4_6_with_product {Ω : Type*} [MeasurableSpace Ω]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧
      Measurable (f - g) ∧
      (∀ c : ℝ, Measurable (c • f)) ∧
      Measurable (f * g) ∧
      ((∀ ω, g ω ≠ 0) → Measurable (f / g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun ω => f ω + g ω)
    exact thm46_measurable_add_via_pair_and_composition hf hg
  · change Measurable (fun ω => f ω - g ω)
    exact thm46_measurable_sub_via_pair_and_composition hf hg
  · intro c
    change Measurable (fun ω => c * f ω)
    exact thm46_measurable_linear_via_composition c hf
  · change Measurable (fun ω => f ω * g ω)
    exact thm46_measurable_mul_via_product_identity hf hg
  · intro hgz
    change Measurable (fun ω => f ω / g ω)
    exact thm46_measurable_div_via_inverse hf hg hgz

theorem thm_4_6 {Ω : Type*} [MeasurableSpace Ω]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧
      Measurable (f - g) ∧
      (∀ c : ℝ, Measurable (c • f)) ∧
      ((∀ ω, g ω ≠ 0) → Measurable (f / g)) := by
  have h := thm_4_6_with_product f g hf hg
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
