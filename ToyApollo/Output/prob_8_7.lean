/-
TASK ID: prob_8_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_5
import ToyApollo.Output.thm_8_6

open MeasureTheory MeasurableSpace Set Filter
open TVCore
open scoped ENNReal NNReal Topology

noncomputable section

structure IsProbabilityDensity (f : ℝ → ℝ) : Prop where
  measurable : Measurable f
  nonneg : ∀ x, 0 ≤ f x
  integral_eq_one : ∫ x, f x = 1

structure PiecewiseContinuous (f : ℝ → ℝ) where
  breakpoints : Finset ℝ
  continuousAt : ∀ ⦃x : ℝ⦄, x ∉ breakpoints -> ContinuousAt f x

def fCommon (f_X f_Y : ℝ → ℝ) (x : ℝ) : ℝ := min (f_X x) (f_Y x)

def fExcessX (f_X f_Y : ℝ → ℝ) (x : ℝ) : ℝ := f_X x - fCommon f_X f_Y x

def fExcessY (f_X f_Y : ℝ → ℝ) (x : ℝ) : ℝ := f_Y x - fCommon f_X f_Y x

def diagEmbed : ℝ → ℝ × ℝ := fun x => (x, x)

def prob_8_7_p (f_X f_Y : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x|

def prob_8_7_fU (f_X f_Y : ℝ → ℝ) (_hp : prob_8_7_p f_X f_Y ≠ 1) : ℝ → ℝ :=
  fun u => fCommon f_X f_Y u / (1 - prob_8_7_p f_X f_Y)

def prob_8_7_fV (f_X f_Y : ℝ → ℝ) (_hp : prob_8_7_p f_X f_Y ≠ 0) : ℝ → ℝ :=
  fun v => fExcessX f_X f_Y v / prob_8_7_p f_X f_Y

def prob_8_7_fW (f_X f_Y : ℝ → ℝ) (_hp : prob_8_7_p f_X f_Y ≠ 0) : ℝ → ℝ :=
  fun w => fExcessY f_X f_Y w / prob_8_7_p f_X f_Y

def prob_8_7_jointDensity (f_X f_Y : ℝ → ℝ) (hp : prob_8_7_p f_X f_Y ≠ 0) :
    ℝ → ℝ → ENNReal :=
  fun x y => ENNReal.ofReal (prob_8_7_fV f_X f_Y hp x * prob_8_7_fW f_X f_Y hp y)

lemma measurable_diagEmbed : Measurable diagEmbed :=
  measurable_id.prodMk measurable_id

lemma fCommon_nonneg (f_X f_Y : ℝ → ℝ) (hX : ∀ x, 0 ≤ f_X x) (hY : ∀ x, 0 ≤ f_Y x) :
    ∀ x, 0 ≤ fCommon f_X f_Y x := fun x => le_min (hX x) (hY x)

lemma fExcessX_nonneg (f_X f_Y : ℝ → ℝ) :
    ∀ x, 0 ≤ fExcessX f_X f_Y x := by
  intro x; unfold fExcessX fCommon; linarith [min_le_left (f_X x) (f_Y x)]

lemma fExcessY_nonneg (f_X f_Y : ℝ → ℝ) :
    ∀ x, 0 ≤ fExcessY f_X f_Y x := by
  intro x; unfold fExcessY fCommon; linarith [min_le_right (f_X x) (f_Y x)]

lemma fCommon_measurable {f_X f_Y : ℝ → ℝ}
    (hX : Measurable f_X) (hY : Measurable f_Y) : Measurable (fCommon f_X f_Y) :=
  hX.min hY

lemma fExcessX_measurable {f_X f_Y : ℝ → ℝ}
    (hX : Measurable f_X) (hY : Measurable f_Y) : Measurable (fExcessX f_X f_Y) :=
  hX.sub (fCommon_measurable hX hY)

lemma fExcessY_measurable {f_X f_Y : ℝ → ℝ}
    (hX : Measurable f_X) (hY : Measurable f_Y) : Measurable (fExcessY f_X f_Y) :=
  hY.sub (fCommon_measurable hX hY)

lemma fX_eq_common_add_excessX (f_X f_Y : ℝ → ℝ) (x : ℝ) :
    f_X x = fCommon f_X f_Y x + fExcessX f_X f_Y x := by
  simp [fExcessX]

lemma fY_eq_common_add_excessY (f_X f_Y : ℝ → ℝ) (x : ℝ) :
    f_Y x = fCommon f_X f_Y x + fExcessY f_X f_Y x := by
  simp [fExcessY]

lemma abs_diff_eq_excessX_add_excessY (f_X f_Y : ℝ → ℝ) (x : ℝ) :
    |f_X x - f_Y x| = fExcessX f_X f_Y x + fExcessY f_X f_Y x := by
  simp [fExcessX, fExcessY, fCommon]
  rcases le_total (f_X x) (f_Y x) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

lemma integrable_fCommon {f_X f_Y : ℝ → ℝ}
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    Integrable (fCommon f_X f_Y) volume := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => f_X x;
  · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one;
  · exact Measurable.aestronglyMeasurable ( fCommon_measurable hfXpdf.measurable hfYpdf.measurable );
  · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( fCommon_nonneg f_X f_Y hfXpdf.nonneg hfYpdf.nonneg x ) ] ; exact min_le_left _ _;

lemma integrable_fExcessX {f_X f_Y : ℝ → ℝ}
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    Integrable (fExcessX f_X f_Y) volume := by
  refine' MeasureTheory.Integrable.sub _ _;
  · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one;
  · exact integrable_fCommon hfXpdf hfYpdf

lemma integrable_fExcessY {f_X f_Y : ℝ → ℝ}
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    Integrable (fExcessY f_X f_Y) volume := by
  apply_rules [ MeasureTheory.Integrable.sub, hfYpdf.integral_eq_one ];
  · exact MeasureTheory.integrable_of_integral_eq_one hfYpdf.integral_eq_one;
  · exact integrable_fCommon hfXpdf hfYpdf

lemma integral_excessX_eq_integral_excessY (f_X f_Y : ℝ → ℝ)
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    ∫ x, fExcessX f_X f_Y x = ∫ x, fExcessY f_X f_Y x := by
  rw [ show fExcessX f_X f_Y = fun x => f_X x - fCommon f_X f_Y x from funext fun x => rfl, show fExcessY f_X f_Y = fun x => f_Y x - fCommon f_X f_Y x from funext fun x => rfl, MeasureTheory.integral_sub, MeasureTheory.integral_sub ];
  · rw [ hfXpdf.integral_eq_one, hfYpdf.integral_eq_one ];
  · exact MeasureTheory.integrable_of_integral_eq_one hfYpdf.integral_eq_one;
  · exact integrable_fCommon hfXpdf hfYpdf;
  · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one;
  · exact integrable_fCommon hfXpdf hfYpdf

lemma p_eq_integral_excessX (f_X f_Y : ℝ → ℝ)
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    (1/2 : ℝ) * ∫ x, |f_X x - f_Y x| = ∫ x, fExcessX f_X f_Y x := by
  -- Use abs_diff_eq_excessX_add_excessY to rewrite ∫|f_X - f_Y| = ∫(fExcessX + fExcessY)
  have h_integral : ∫ x, |f_X x - f_Y x| = ∫ x, fExcessX f_X f_Y x + fExcessY f_X f_Y x := by
    exact congr_arg _ ( funext fun x => abs_diff_eq_excessX_add_excessY f_X f_Y x );
  rw [ h_integral, MeasureTheory.integral_add, integral_excessX_eq_integral_excessY ];
  · ring;
  · assumption;
  · assumption;
  · exact integrable_fExcessX hfXpdf hfYpdf;
  · exact integrable_fExcessY hfXpdf hfYpdf

theorem prob_8_7_exists (f_X f_Y : ℝ → ℝ) (hfXpdf : IsProbabilityDensity f_X)
    (hfYpdf : IsProbabilityDensity f_Y)
    (hfX_pc : PiecewiseContinuous f_X) (hfY_pc : PiecewiseContinuous f_Y) :
    let p := prob_8_7_p f_X f_Y
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f_X x))
    let ν := volume.withDensity (fun x => ENNReal.ofReal (f_Y x))
    ∃ (π : Measure (ℝ × ℝ)), IsProbabilityMeasure π ∧
      (Measure.map Prod.fst π = μ) ∧ (Measure.map Prod.snd π = ν) ∧
      (π {z | z.1 ≠ z.2} = ENNReal.ofReal p) := by
  by_cases hp0 : prob_8_7_p f_X f_Y = 0
  · -- Since $p = 0$, we have $f_X = f_Y$ almost everywhere.
    have hp_int : (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| = 0 := by
      simpa [prob_8_7_p] using hp0
    have h_eq : f_X =ᵐ[volume] f_Y := by
      simp +zetaDelta at *;
      rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ] at hp_int;
      · filter_upwards [ hp_int ] with x hx using sub_eq_zero.mp ( abs_eq_zero.mp hx );
      · exact fun x => abs_nonneg _;
      · exact MeasureTheory.Integrable.abs ( MeasureTheory.Integrable.sub ( by exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one ) ( by exact MeasureTheory.integrable_of_integral_eq_one hfYpdf.integral_eq_one ) );
    refine' ⟨ Measure.map diagEmbed ( volume.withDensity fun x => ENNReal.ofReal ( f_X x ) ), _, _, _, _ ⟩ <;> norm_num;
    · constructor;
      rw [ Measure.map_apply ] <;> norm_num [ measurable_diagEmbed ];
      rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · rw [ hfXpdf.integral_eq_one, ENNReal.ofReal_one ];
      · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one;
      · exact Filter.Eventually.of_forall hfXpdf.nonneg;
    · rw [ Measure.map_map ];
      · exact Measure.map_id;
      · exact measurable_fst;
      · exact measurable_diagEmbed;
    · rw [ Measure.map_map ];
      · rw [ MeasureTheory.withDensity_congr_ae ];
        any_goals exact fun x => ENNReal.ofReal ( f_Y x );
        · exact Measure.map_id;
        · filter_upwards [ h_eq ] with x hx using by rw [ hx ] ;
      · exact measurable_snd;
      · exact measurable_diagEmbed;
    · rw [MeasureTheory.Measure.map_apply]
      · simp [diagEmbed, hp0]
      · exact measurable_diagEmbed
      · have h_offdiag : MeasurableSet ({z : ℝ × ℝ | z.1 ≠ z.2} : Set (ℝ × ℝ)) := by
          exact (measurableSet_eq_fun
            (f := fun z : ℝ × ℝ => z.1)
            (g := fun z : ℝ × ℝ => z.2)
            measurable_fst measurable_snd).compl
        exact h_offdiag
  · have hp : (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| ≠ 0 := by
      simpa [prob_8_7_p] using hp0
    refine' ⟨ Measure.map ( fun x => ( x, x ) ) ( volume.withDensity ( fun x => ENNReal.ofReal ( fCommon f_X f_Y x ) ) ) + ( ENNReal.ofReal ( 1 / prob_8_7_p f_X f_Y ) ) • ( volume.withDensity ( fun x => ENNReal.ofReal ( fExcessX f_X f_Y x ) ) |> Measure.prod <| volume.withDensity ( fun x => ENNReal.ofReal ( fExcessY f_X f_Y x ) ) ), _, _, _, _ ⟩ <;> norm_num [ hp, prob_8_7_p ];
    · constructor ; norm_num;
      rw [ MeasureTheory.Measure.map_apply ] <;> norm_num;
      · rw [ MeasureTheory.Measure.prod_apply ] <;> norm_num;
        rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
          · rw [ ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul ];
            · rw [ ← ENNReal.ofReal_add ] <;> norm_num [ hp ];
              · have h_integral_common : ∫ x, fCommon f_X f_Y x = 1 - (∫ x, |f_X x - f_Y x|) / 2 := by
                  have h_integral_common : ∫ x, fCommon f_X f_Y x = (∫ x, f_X x) - (∫ x, fExcessX f_X f_Y x) := by
                    rw [ ← MeasureTheory.integral_sub ];
                    · exact congr_arg _ ( funext fun x => by rw [ fExcessX ] ; ring );
                    · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one;
                    · exact integrable_fExcessX hfXpdf hfYpdf;
                  have := p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf; norm_num [ hfXpdf.integral_eq_one, hfYpdf.integral_eq_one ] at *; linarith;
                grind +suggestions;
              · exact MeasureTheory.integral_nonneg fun x => fCommon_nonneg f_X f_Y hfXpdf.nonneg hfYpdf.nonneg x;
              · exact mul_nonneg ( mul_nonneg ( inv_nonneg.2 ( MeasureTheory.integral_nonneg fun _ => abs_nonneg _ ) ) zero_le_two ) ( mul_nonneg ( MeasureTheory.integral_nonneg fun _ => fExcessY_nonneg _ _ _ ) ( MeasureTheory.integral_nonneg fun _ => fExcessX_nonneg _ _ _ ) );
            · exact mul_nonneg ( inv_nonneg.2 ( MeasureTheory.integral_nonneg fun x => abs_nonneg _ ) ) zero_le_two;
            · exact MeasureTheory.integral_nonneg fun x => fExcessY_nonneg _ _ _;
          · exact integrable_fExcessX hfXpdf hfYpdf;
          · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x;
          · exact integrable_fExcessY hfXpdf hfYpdf;
          · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg _ _ x;
        · exact integrable_fCommon hfXpdf hfYpdf;
        · exact Filter.Eventually.of_forall fun x => fCommon_nonneg f_X f_Y hfXpdf.nonneg hfYpdf.nonneg x;
      · exact measurable_id.prodMk measurable_id;
    · rw [ Measure.map_add, Measure.map_smul ];
      · rw [ Measure.map_map ];
        · ext s hs; simp +decide [ *, MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.map_apply ] ; ring;
          rw [ Measure.map_apply ] <;> norm_num [ hs ];
          · rw [ show ( ∫⁻ x : ℝ, ENNReal.ofReal ( fExcessY f_X f_Y x ) ) = ENNReal.ofReal ( ∫ x : ℝ, fExcessY f_X f_Y x ) from ?_ ];
            · rw [ show ( ∫ x : ℝ, fExcessY f_X f_Y x ) = ( 1 / 2 : ℝ ) * ∫ x : ℝ, |f_X x - f_Y x| from ?_ ];
              · rw [ ← ENNReal.ofReal_mul ] <;> ring <;> norm_num [ hp ];
                · rw [ mul_inv_cancel₀ ( by aesop ) ] ; norm_num;
                  rw [ MeasureTheory.withDensity_apply' ];
                  rw [ show ( Prod.fst ∘ fun x => ( x, x ) ) ⁻¹' s = s by ext; aesop ];
                  rw [ ← MeasureTheory.lintegral_add_left' ];
                  · congr with x ; rw [ ← ENNReal.ofReal_add ] <;> norm_num [ fCommon, fExcessX ];
                    exact ⟨ hfXpdf.nonneg x, hfYpdf.nonneg x ⟩;
                  · exact ENNReal.measurable_ofReal.comp_aemeasurable ( fCommon_measurable hfXpdf.measurable hfYpdf.measurable |> Measurable.aemeasurable );
                · exact MeasureTheory.integral_nonneg fun x => abs_nonneg _;
              · have := integral_excessX_eq_integral_excessY f_X f_Y hfXpdf hfYpdf; have := p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf; aesop;
            · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
              · exact integrable_fExcessY hfXpdf hfYpdf;
              · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x;
          · exact measurable_fst.comp ( measurable_id.prodMk measurable_id );
        · exact measurable_fst;
        · exact measurable_id.prodMk measurable_id;
      · exact measurable_fst;
    · rw [ Measure.map_add ];
      · rw [ Measure.map_smul, Measure.map_map ];
        · ext s hs; simp +decide [ *, MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.map_apply ] ; ring;
          rw [ Measure.map_apply ] <;> norm_num [ hs ];
          · rw [ MeasureTheory.withDensity_apply' ];
            rw [ show ( ∫⁻ x in s, ENNReal.ofReal ( f_Y x ) ) = ( ∫⁻ x in s, ENNReal.ofReal ( fCommon f_X f_Y x ) ) + ( ∫⁻ x in s, ENNReal.ofReal ( fExcessY f_X f_Y x ) ) from ?_ ];
            · rw [ show ( ∫⁻ x, ENNReal.ofReal ( fExcessX f_X f_Y x ) ) = ENNReal.ofReal ( ∫ x, fExcessX f_X f_Y x ) from ?_, show ( ∫⁻ x in s, ENNReal.ofReal ( fExcessY f_X f_Y x ) ) = ENNReal.ofReal ( ∫ x in s, fExcessY f_X f_Y x ) from ?_ ];
              · rw [ show ( ∫ x, fExcessX f_X f_Y x ) = ( 1 / 2 : ℝ ) * ∫ x, |f_X x - f_Y x| from ?_ ];
                · rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf;
                  rw [ mul_inv_cancel₀ ( by aesop ) ] ; norm_num ; ring!;
                · simpa [prob_8_7_p] using
                    (p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf).symm;
              · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
                · exact MeasureTheory.Integrable.integrableOn ( integrable_fExcessY hfXpdf hfYpdf );
                · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x;
              · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
                · exact integrable_fExcessX hfXpdf hfYpdf;
                · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x;
            · rw [ ← MeasureTheory.lintegral_add_left' ];
              · refine' MeasureTheory.setLIntegral_congr_fun hs _;
                intro x hx; simp +decide [ fCommon, fExcessY ] ;
                cases le_total ( f_X x ) ( f_Y x ) <;> simp +decide [ * ];
                · have hxy : f_X x ≤ f_Y x := ‹f_X x ≤ f_Y x›
                  have hmin :
                      min (ENNReal.ofReal (f_X x)) (ENNReal.ofReal (f_Y x)) =
                        ENNReal.ofReal (f_X x) := by
                    exact min_eq_left (ENNReal.ofReal_le_ofReal hxy)
                  have hsplit :
                      ENNReal.ofReal (f_Y x) =
                        ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := by
                    calc
                      ENNReal.ofReal (f_Y x)
                          = ENNReal.ofReal (f_X x + (f_Y x - f_X x)) := by
                              congr 1
                              linarith
                      _ = ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := by
                              rw [ENNReal.ofReal_add]
                              · exact hfXpdf.nonneg x
                              · exact sub_nonneg.mpr hxy
                  calc
                    ENNReal.ofReal (f_Y x)
                        = ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := hsplit
                    _ = min (ENNReal.ofReal (f_X x)) (ENNReal.ofReal (f_Y x)) +
                          ENNReal.ofReal (f_Y x - f_X x) := by
                            rw [hmin]
                · exact ENNReal.ofReal_le_ofReal ‹_›;
              · exact ENNReal.measurable_ofReal.comp_aemeasurable ( fCommon_measurable hfXpdf.measurable hfYpdf.measurable |> Measurable.aemeasurable );
          · exact measurable_snd.comp ( measurable_id.prodMk measurable_id );
        · exact measurable_snd;
        · exact measurable_id.prodMk measurable_id;
      · exact measurable_snd;
    · rw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ measurable_diagEmbed ];
      · rw [ show { z : ℝ × ℝ | ¬z.1 = z.2 } = ( Set.univ : Set ( ℝ × ℝ ) ) \ { z : ℝ × ℝ | z.1 = z.2 } by ext; simp +decide, MeasureTheory.measure_diff_null ] <;> norm_num [ MeasureTheory.Measure.prod_apply ];
        · rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
          · rw [ ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul ] <;> norm_num [ hp ];
            · grind +suggestions;
            · exact MeasureTheory.integral_nonneg fun x => abs_nonneg _;
            · exact MeasureTheory.integral_nonneg fun x => fExcessY_nonneg _ _ _;
          · exact integrable_fExcessX hfXpdf hfYpdf;
          · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x;
          · exact integrable_fExcessY hfXpdf hfYpdf;
          · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x;
        · erw [ MeasureTheory.Measure.prod_apply ];
          · simp +decide [ Set.preimage ];
          · exact measurableSet_eq_fun measurable_fst measurable_snd;
      · exact measurable_id.prodMk measurable_id;
      · exact MeasurableSet.mem ( MeasurableSet.compl ( measurableSet_eq_fun measurable_fst measurable_snd ) )

noncomputable def prob_8_7_maximumCoupling (f_X f_Y : ℝ → ℝ)
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y)
    (hfX_pc : PiecewiseContinuous f_X) (hfY_pc : PiecewiseContinuous f_Y) :
    Measure (ℝ × ℝ) :=
  let diagonalPart :=
    Measure.map (fun x => (x, x)) (volume.withDensity fun x => ENNReal.ofReal (fCommon f_X f_Y x))
  let offDiagonalPart :=
    if hp0 : prob_8_7_p f_X f_Y = 0 then
      0
    else
      (ENNReal.ofReal (1 / prob_8_7_p f_X f_Y)) •
        ((volume.withDensity fun x => ENNReal.ofReal (fExcessX f_X f_Y x))
          |> Measure.prod <| volume.withDensity fun x => ENNReal.ofReal (fExcessY f_X f_Y x))
  diagonalPart + offDiagonalPart

theorem prob_8_7_maximumCoupling_spec (f_X f_Y : ℝ → ℝ)
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y)
    (hfX_pc : PiecewiseContinuous f_X) (hfY_pc : PiecewiseContinuous f_Y) :
    let p := prob_8_7_p f_X f_Y
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f_X x))
    let ν := volume.withDensity (fun x => ENNReal.ofReal (f_Y x))
    IsProbabilityMeasure (prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc) ∧
      (Measure.map Prod.fst (prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc) = μ) ∧
      (Measure.map Prod.snd (prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc) = ν) ∧
      ((prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc) {z | z.1 ≠ z.2}
        = ENNReal.ofReal p) := by
  by_cases hp0 : prob_8_7_p f_X f_Y = 0
  · have hp_int : (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| = 0 := by
      simpa [prob_8_7_p] using hp0
    have h_eq : f_X =ᵐ[volume] f_Y := by
      simp +zetaDelta at *
      rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hp_int
      · filter_upwards [hp_int] with x hx using sub_eq_zero.mp (abs_eq_zero.mp hx)
      · exact fun x => abs_nonneg _
      · exact MeasureTheory.Integrable.abs
          (MeasureTheory.Integrable.sub
            (by exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one)
            (by exact MeasureTheory.integrable_of_integral_eq_one hfYpdf.integral_eq_one))
    have hcommonX :
        volume.withDensity (fun x => ENNReal.ofReal (fCommon f_X f_Y x)) =
          volume.withDensity (fun x => ENNReal.ofReal (f_X x)) := by
      rw [MeasureTheory.withDensity_congr_ae]
      filter_upwards [h_eq] with x hx using by simp [fCommon, hx]
    have hπ :
        prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc =
          Measure.map diagEmbed (volume.withDensity fun x => ENNReal.ofReal (f_X x)) := by
      calc
        prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc
            = Measure.map (fun x => (x, x)) (volume.withDensity fun x => ENNReal.ofReal (f_X x)) := by
                simp [prob_8_7_maximumCoupling, hp0, hcommonX]
        _ = Measure.map diagEmbed (volume.withDensity fun x => ENNReal.ofReal (f_X x)) := by
                rfl
    rw [hπ]
    constructor
    · constructor
      rw [Measure.map_apply] <;> norm_num [measurable_diagEmbed]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      · rw [hfXpdf.integral_eq_one, ENNReal.ofReal_one]
      · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one
      · exact Filter.Eventually.of_forall hfXpdf.nonneg
    · constructor
      · rw [Measure.map_map]
        · exact Measure.map_id
        · exact measurable_fst
        · exact measurable_diagEmbed
      · constructor
        · rw [Measure.map_map]
          · rw [MeasureTheory.withDensity_congr_ae]
            any_goals exact fun x => ENNReal.ofReal (f_Y x)
            · exact Measure.map_id
            · filter_upwards [h_eq] with x hx using by rw [hx]
          · exact measurable_snd
          · exact measurable_diagEmbed
        · rw [MeasureTheory.Measure.map_apply]
          · simp [diagEmbed, hp0]
          · exact measurable_diagEmbed
          · have h_offdiag : MeasurableSet ({z : ℝ × ℝ | z.1 ≠ z.2} : Set (ℝ × ℝ)) := by
              exact (measurableSet_eq_fun
                (f := fun z : ℝ × ℝ => z.1)
                (g := fun z : ℝ × ℝ => z.2)
                measurable_fst measurable_snd).compl
            exact h_offdiag
  · have hp : (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| ≠ 0 := by
      simpa [prob_8_7_p] using hp0
    have hπ :
        prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc =
          Measure.map (fun x => (x, x)) (volume.withDensity (fun x => ENNReal.ofReal (fCommon f_X f_Y x))) +
            (ENNReal.ofReal (1 / prob_8_7_p f_X f_Y)) •
              ((volume.withDensity (fun x => ENNReal.ofReal (fExcessX f_X f_Y x)))
                |> Measure.prod <| volume.withDensity (fun x => ENNReal.ofReal (fExcessY f_X f_Y x))) := by
      simp [prob_8_7_maximumCoupling, hp0, diagEmbed]
    rw [hπ] <;> norm_num [hp, prob_8_7_p]
    constructor
    · constructor ; norm_num
      rw [MeasureTheory.Measure.map_apply] <;> norm_num
      · rw [MeasureTheory.Measure.prod_apply] <;> norm_num
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
        · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
          · rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul]
            · rw [← ENNReal.ofReal_add] <;> norm_num [hp]
              · have h_integral_common : ∫ x, fCommon f_X f_Y x = 1 - (∫ x, |f_X x - f_Y x|) / 2 := by
                  have h_integral_common : ∫ x, fCommon f_X f_Y x = (∫ x, f_X x) - (∫ x, fExcessX f_X f_Y x) := by
                    rw [← MeasureTheory.integral_sub]
                    · exact congr_arg _ (funext fun x => by rw [fExcessX]; ring)
                    · exact MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one
                    · exact integrable_fExcessX hfXpdf hfYpdf
                  have := p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf
                  norm_num [hfXpdf.integral_eq_one, hfYpdf.integral_eq_one] at *
                  linarith
                grind +suggestions
              · exact MeasureTheory.integral_nonneg fun x => fCommon_nonneg f_X f_Y hfXpdf.nonneg hfYpdf.nonneg x
              · exact mul_nonneg
                  (mul_nonneg (inv_nonneg.2 (MeasureTheory.integral_nonneg fun _ => abs_nonneg _)) zero_le_two)
                  (mul_nonneg
                    (MeasureTheory.integral_nonneg fun _ => fExcessY_nonneg _ _ _)
                    (MeasureTheory.integral_nonneg fun _ => fExcessX_nonneg _ _ _))
            · exact mul_nonneg (inv_nonneg.2 (MeasureTheory.integral_nonneg fun x => abs_nonneg _)) zero_le_two
            · exact MeasureTheory.integral_nonneg fun x => fExcessY_nonneg _ _ _
          · exact integrable_fExcessX hfXpdf hfYpdf
          · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x
          · exact integrable_fExcessY hfXpdf hfYpdf
          · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg _ _ x
        · exact integrable_fCommon hfXpdf hfYpdf
        · exact Filter.Eventually.of_forall fun x => fCommon_nonneg f_X f_Y hfXpdf.nonneg hfYpdf.nonneg x
      · exact measurable_id.prodMk measurable_id
    · constructor
      · rw [Measure.map_add, Measure.map_smul]
        · rw [Measure.map_map]
          · ext s hs
            simp +decide [*, MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.map_apply]
            ring
            rw [Measure.map_apply] <;> norm_num [hs]
            · rw [show (∫⁻ x : ℝ, ENNReal.ofReal (fExcessY f_X f_Y x)) = ENNReal.ofReal (∫ x : ℝ, fExcessY f_X f_Y x) from ?_]
              · rw [show (∫ x : ℝ, fExcessY f_X f_Y x) = (1 / 2 : ℝ) * ∫ x : ℝ, |f_X x - f_Y x| from ?_]
                · rw [← ENNReal.ofReal_mul] <;> ring <;> norm_num [hp]
                  · rw [mul_inv_cancel₀ (by aesop)]
                    norm_num
                    rw [MeasureTheory.withDensity_apply']
                    rw [show (Prod.fst ∘ fun x => (x, x)) ⁻¹' s = s by ext; aesop]
                    rw [← MeasureTheory.lintegral_add_left']
                    · congr with x
                      rw [← ENNReal.ofReal_add] <;> norm_num [fCommon, fExcessX]
                      exact ⟨hfXpdf.nonneg x, hfYpdf.nonneg x⟩
                    · exact ENNReal.measurable_ofReal.comp_aemeasurable (fCommon_measurable hfXpdf.measurable hfYpdf.measurable |> Measurable.aemeasurable)
                  · exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
                · have := integral_excessX_eq_integral_excessY f_X f_Y hfXpdf hfYpdf
                  have := p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf
                  aesop
              · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
                · exact integrable_fExcessY hfXpdf hfYpdf
                · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x
            · exact measurable_fst.comp (measurable_id.prodMk measurable_id)
          · exact measurable_fst
          · exact measurable_id.prodMk measurable_id
        · exact measurable_fst
      · constructor
        · rw [Measure.map_add]
          · rw [Measure.map_smul, Measure.map_map]
            · ext s hs
              simp +decide [*, MeasureTheory.Measure.prod_apply, MeasureTheory.Measure.map_apply]
              ring
              rw [Measure.map_apply] <;> norm_num [hs]
              · rw [MeasureTheory.withDensity_apply']
                rw [show (∫⁻ x in s, ENNReal.ofReal (f_Y x)) = (∫⁻ x in s, ENNReal.ofReal (fCommon f_X f_Y x)) + (∫⁻ x in s, ENNReal.ofReal (fExcessY f_X f_Y x)) from ?_]
                · rw [show (∫⁻ x, ENNReal.ofReal (fExcessX f_X f_Y x)) = ENNReal.ofReal (∫ x, fExcessX f_X f_Y x) from ?_, show (∫⁻ x in s, ENNReal.ofReal (fExcessY f_X f_Y x)) = ENNReal.ofReal (∫ x in s, fExcessY f_X f_Y x) from ?_]
                  · rw [show (∫ x, fExcessX f_X f_Y x) = (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| from ?_]
                    · rw [← ENNReal.ofReal_mul (by positivity)]
                      ring_nf
                      rw [mul_inv_cancel₀ (by aesop)]
                      norm_num
                      ring!
                    · simpa [prob_8_7_p] using
                        (p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf).symm
                  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
                    · exact MeasureTheory.Integrable.integrableOn (integrable_fExcessY hfXpdf hfYpdf)
                    · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x
                  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
                    · exact integrable_fExcessX hfXpdf hfYpdf
                    · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x
                · rw [← MeasureTheory.lintegral_add_left']
                  · refine' MeasureTheory.setLIntegral_congr_fun hs _
                    intro x hx
                    simp +decide [fCommon, fExcessY]
                    cases le_total (f_X x) (f_Y x) <;> simp +decide [*]
                    · have hxy : f_X x ≤ f_Y x := ‹f_X x ≤ f_Y x›
                      have hmin :
                          min (ENNReal.ofReal (f_X x)) (ENNReal.ofReal (f_Y x)) =
                            ENNReal.ofReal (f_X x) := by
                        exact min_eq_left (ENNReal.ofReal_le_ofReal hxy)
                      have hsplit :
                          ENNReal.ofReal (f_Y x) =
                            ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := by
                        calc
                          ENNReal.ofReal (f_Y x) = ENNReal.ofReal (f_X x + (f_Y x - f_X x)) := by
                            congr 1
                            linarith
                          _ = ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := by
                            rw [ENNReal.ofReal_add]
                            · exact hfXpdf.nonneg x
                            · exact sub_nonneg.mpr hxy
                      calc
                        ENNReal.ofReal (f_Y x) = ENNReal.ofReal (f_X x) + ENNReal.ofReal (f_Y x - f_X x) := hsplit
                        _ = min (ENNReal.ofReal (f_X x)) (ENNReal.ofReal (f_Y x)) +
                              ENNReal.ofReal (f_Y x - f_X x) := by
                                rw [hmin]
                    · exact ENNReal.ofReal_le_ofReal ‹_›
                  · exact ENNReal.measurable_ofReal.comp_aemeasurable (fCommon_measurable hfXpdf.measurable hfYpdf.measurable |> Measurable.aemeasurable)
              · exact measurable_snd.comp (measurable_id.prodMk measurable_id)
            · exact measurable_snd
            · exact measurable_id.prodMk measurable_id
          · exact measurable_snd
        · rw [MeasureTheory.Measure.map_apply] <;> norm_num [measurable_diagEmbed]
          · rw [show {z : ℝ × ℝ | ¬ z.1 = z.2} = (Set.univ : Set (ℝ × ℝ)) \ {z : ℝ × ℝ | z.1 = z.2} by ext; simp +decide,
              MeasureTheory.measure_diff_null] <;> norm_num [MeasureTheory.Measure.prod_apply]
            · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
              · rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul] <;> norm_num [hp]
                · have h_excessX :
                      ∫ x, fExcessX f_X f_Y x = (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| := by
                    simpa [prob_8_7_p] using (p_eq_integral_excessX f_X f_Y hfXpdf hfYpdf).symm
                  have h_excessY :
                      ∫ x, fExcessY f_X f_Y x = (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| := by
                    calc
                      ∫ x, fExcessY f_X f_Y x = ∫ x, fExcessX f_X f_Y x := by
                        symm
                        exact integral_excessX_eq_integral_excessY f_X f_Y hfXpdf hfYpdf
                      _ = (1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x| := h_excessX
                  rw [h_excessX, h_excessY]
                  have habs_nonneg : 0 ≤ ∫ x, |f_X x - f_Y x| := by
                    exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
                  have h_rhs :
                      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (∫ x, |f_X x - f_Y x|) =
                        ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, |f_X x - f_Y x|) := by
                    simpa using
                      (ENNReal.ofReal_mul (p := (1 / 2 : ℝ)) (q := ∫ x, |f_X x - f_Y x|) (by norm_num)).symm
                  rw [h_rhs]
                  congr 1
                  field_simp [hp]
                · exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
                · exact MeasureTheory.integral_nonneg fun x => fExcessY_nonneg _ _ _
              · exact integrable_fExcessX hfXpdf hfYpdf
              · exact Filter.Eventually.of_forall fun x => fExcessX_nonneg f_X f_Y x
              · exact integrable_fExcessY hfXpdf hfYpdf
              · exact Filter.Eventually.of_forall fun x => fExcessY_nonneg f_X f_Y x
            · erw [MeasureTheory.Measure.prod_apply]
              · simp +decide [Set.preimage]
              · exact measurableSet_eq_fun measurable_fst measurable_snd
          · exact measurable_id.prodMk measurable_id
          · exact MeasurableSet.mem (MeasurableSet.compl (measurableSet_eq_fun measurable_fst measurable_snd))

theorem prob_8_7_totalVariation_eq_p (f_X f_Y : ℝ → ℝ)
    (hfXpdf : IsProbabilityDensity f_X) (hfYpdf : IsProbabilityDensity f_Y) :
    totalVariationDistance
        (volume.withDensity (fun x => ENNReal.ofReal (f_X x)))
        (volume.withDensity (fun x => ENNReal.ofReal (f_Y x)))
      = prob_8_7_p f_X f_Y := by
  simpa [prob_8_7_p, TVCore.densityMeasure, TVCore.densityDiff] using
    thm_8_6_continuous hfXpdf.measurable hfYpdf.measurable
      (MeasureTheory.integrable_of_integral_eq_one hfXpdf.integral_eq_one)
      (MeasureTheory.integrable_of_integral_eq_one hfYpdf.integral_eq_one)
      hfXpdf.nonneg hfYpdf.nonneg hfXpdf.integral_eq_one hfYpdf.integral_eq_one

theorem prob_8_7 (f_X f_Y : ℝ → ℝ) (hfXpdf : IsProbabilityDensity f_X)
    (hfYpdf : IsProbabilityDensity f_Y)
    (hfX_pc : PiecewiseContinuous f_X) (hfY_pc : PiecewiseContinuous f_Y) :
    let p := prob_8_7_p f_X f_Y
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f_X x))
    let ν := volume.withDensity (fun x => ENNReal.ofReal (f_Y x))
    let π := prob_8_7_maximumCoupling f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc
    IsProbabilityMeasure π ∧
      (Measure.map Prod.fst π = μ) ∧
      (Measure.map Prod.snd π = ν) ∧
      (π {z | z.1 ≠ z.2} = ENNReal.ofReal p) ∧
      (totalVariationDistance μ ν = p) := by
  dsimp
  have hspec := prob_8_7_maximumCoupling_spec f_X f_Y hfXpdf hfYpdf hfX_pc hfY_pc
  have htv := prob_8_7_totalVariation_eq_p f_X f_Y hfXpdf hfYpdf
  rcases hspec with ⟨hprob, hfst, hsnd, hmismatch⟩
  exact ⟨hprob, hfst, hsnd, hmismatch, htv⟩

end
