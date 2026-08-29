/-
TASK ID: prob_7_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Filter Topology

def HasFiniteIntegralLimit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : ℕ → Ω → ℝ) (u_lim : Ω → ℝ) : Prop :=
  Integrable u_lim μ ∧
    Tendsto (fun n => ∫ ω, u n ω ∂μ) atTop (𝓝 (∫ ω, u_lim ω ∂μ))

theorem prob_7_9 {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g h : ℕ → Ω → ℝ} {f_lim g_lim h_lim : Ω → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : ∀ n, Integrable (g n) μ)
    (hh_int : ∀ n, Integrable (h n) μ)
    (hf_pt : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (f_lim ω)))
    (hg_pt : ∀ ω, Tendsto (fun n => g n ω) atTop (𝓝 (g_lim ω)))
    (hh_pt : ∀ ω, Tendsto (fun n => h n ω) atTop (𝓝 (h_lim ω)))
    (h_ineq_pt : ∀ n ω, f n ω ≤ g n ω ∧ g n ω ≤ h n ω)
    (hf_int_conv : HasFiniteIntegralLimit μ f f_lim)
    (hh_int_conv : HasFiniteIntegralLimit μ h h_lim) :
    Integrable g_lim μ ∧
      Tendsto (fun n => ∫ ω, g n ω ∂μ) atTop (𝓝 (∫ ω, g_lim ω ∂μ)) := by
  rcases hf_int_conv with ⟨hf_lim_int, hf_int_conv⟩
  rcases hh_int_conv with ⟨hh_lim_int, hh_int_conv⟩
  have hf_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (f_lim ω)) :=
    Filter.Eventually.of_forall hf_pt
  have hg_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (g_lim ω)) :=
    Filter.Eventually.of_forall hg_pt
  have hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 (h_lim ω)) :=
    Filter.Eventually.of_forall hh_pt
  have h_ineq : ∀ n, (f n ≤ᵐ[μ] g n) ∧ (g n ≤ᵐ[μ] h n) := by
    intro n
    exact ⟨
      Filter.Eventually.of_forall fun ω => (h_ineq_pt n ω).1,
      Filter.Eventually.of_forall fun ω => (h_ineq_pt n ω).2
    ⟩
  have hfg_lim : f_lim ≤ᵐ[μ] g_lim := by
    filter_upwards [hf_ae, hg_ae, ae_all_iff.2 fun n => (h_ineq n).1] with ω hf hg hfg
    exact le_of_tendsto_of_tendsto hf hg (eventually_atTop.2 ⟨0, fun n _ => hfg n⟩)
  have hgh_lim : g_lim ≤ᵐ[μ] h_lim := by
    filter_upwards [hg_ae, hh_ae, ae_all_iff.2 fun n => (h_ineq n).2] with ω hg hh hgh
    exact le_of_tendsto_of_tendsto hg hh (eventually_atTop.2 ⟨0, fun n _ => hgh n⟩)
  have hgi : Integrable g_lim μ := by
    refine' MeasureTheory.Integrable.mono' _ _ _
    · exact fun ω => |f_lim ω| + |h_lim ω|
    · exact MeasureTheory.Integrable.add (hf_lim_int.abs) (hh_lim_int.abs)
    · exact
        aestronglyMeasurable_of_tendsto_ae _ (fun n =>
          (hg_int n).aestronglyMeasurable) hg_ae
    ·
      filter_upwards [hfg_lim, hgh_lim] with ω hω₁ hω₂ using
        abs_le.mpr
          ⟨by
              cases abs_cases (f_lim ω) <;> cases abs_cases (h_lim ω) <;> linarith,
            by
              cases abs_cases (f_lim ω) <;> cases abs_cases (h_lim ω) <;> linarith⟩
  refine ⟨hgi, ?_⟩
  have h_liminf : ∫ ω, g_lim ω ∂μ ≤ Filter.liminf (fun n => ∫ ω, g n ω ∂μ) atTop := by
    refine' le_of_forall_pos_le_add fun ε εpos => _
    obtain ⟨N, hN⟩ :
        ∃ N,
          ∀ n ≥ N,
            ∫ ω, (g n ω - f n ω) ∂μ ≥ ∫ ω, (g_lim ω - f_lim ω) ∂μ - ε / 2 := by
      have h_fatou :
          ∫⁻ ω, ENNReal.ofReal (g_lim ω - f_lim ω) ∂μ ≤
            Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (g n ω - f n ω) ∂μ) Filter.atTop := by
        refine' le_trans _ (MeasureTheory.lintegral_liminf_le' _)
        · refine' MeasureTheory.lintegral_mono_ae _
          filter_upwards [hf_ae, hg_ae, hfg_lim] with ω hω₁ hω₂ hω₃
          exact le_of_eq (by rw [Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal (hω₂.sub hω₁))])
        · exact fun n =>
            ((hg_int n).aemeasurable.sub (hf_int n).aemeasurable).ennreal_ofReal
      have h_fatou :
          ∀ ε > 0,
            ∃ N,
              ∀ n ≥ N,
                ∫⁻ ω, ENNReal.ofReal (g n ω - f n ω) ∂μ ≥
                  ∫⁻ ω, ENNReal.ofReal (g_lim ω - f_lim ω) ∂μ -
                    ENNReal.ofReal (ε / 2) := by
        intro ε εpos
        contrapose! h_fatou
        simp_all +decide [Filter.liminf_eq]
        refine' lt_of_le_of_lt (csSup_le _ _) _
        · exact ∫⁻ ω, ENNReal.ofReal (g_lim ω - f_lim ω) ∂μ - ENNReal.ofReal (ε / 2)
        · exact ⟨0, ⟨0, fun _ _ => zero_le⟩⟩
        ·
          rintro _ ⟨N, hN⟩
          obtain ⟨n, hn₁, hn₂⟩ := h_fatou N
          exact le_trans (hN n hn₁) hn₂.le
        ·
          refine' ENNReal.sub_lt_self _ _ _ <;> norm_num
          · refine' ne_of_lt (MeasureTheory.Integrable.lintegral_lt_top _)
            exact hgi.sub hf_lim_int
          ·
            intro H
            specialize h_fatou 0
            aesop
          · grind
      obtain ⟨N, hN⟩ := h_fatou ε εpos
      use N
      intro n hn
      specialize hN n hn
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      ·
        contrapose! hN
        rw [lt_tsub_iff_right] at *
        rw [← ENNReal.toReal_lt_toReal] <;> norm_num
        ·
          rw [ENNReal.toReal_add] <;> norm_num
          · rwa [ENNReal.toReal_ofReal (by positivity)]
          ·
            exact ne_of_lt
              (MeasureTheory.Integrable.lintegral_lt_top
                (MeasureTheory.Integrable.ofReal ((hg_int n).sub (hf_int n))))
        ·
          exact ne_of_lt
            (MeasureTheory.Integrable.lintegral_lt_top
              (MeasureTheory.Integrable.ofReal ((hg_int n).sub (hf_int n))))
        · exact ne_of_lt (MeasureTheory.Integrable.lintegral_lt_top (MeasureTheory.Integrable.ofReal (hgi.sub hf_lim_int)))
      · filter_upwards [hfg_lim] with ω hω using sub_nonneg_of_le hω
      · exact hgi.1.sub hf_lim_int.1
      · filter_upwards [(h_ineq n).1] with ω hω using sub_nonneg_of_le hω
      · exact ((hg_int n).sub (hf_int n)).aestronglyMeasurable
    have h_rewrite :
        ∀ n ≥ N,
          ∫ ω, g n ω ∂μ ≥
            ∫ ω, g_lim ω ∂μ - ∫ ω, f_lim ω ∂μ + ∫ ω, f n ω ∂μ - ε / 2 := by
      intro n hn
      specialize hN n hn
      rw [MeasureTheory.integral_sub (hg_int n) (hf_int n), MeasureTheory.integral_sub hgi hf_lim_int] at hN
      linarith
    rw [← sub_le_iff_le_add]
    refine' le_of_forall_lt_imp_le_of_dense fun x hx => _
    refine' le_csSup _ _ <;> norm_num
    ·
      have h_le_h : ∀ n, ∫ ω, g n ω ∂μ ≤ ∫ ω, h n ω ∂μ := by
        intro n
        exact MeasureTheory.integral_mono_ae (hg_int n) (hh_int n) ((h_ineq n).2)
      exact
        ⟨_,
          by
            rintro _ ⟨n, hn⟩
            exact le_trans (hn _ le_rfl) (h_le_h _) |> le_trans <| le_ciSup (hh_int_conv.bddAbove_range) _⟩
    ·
      rcases Metric.tendsto_atTop.mp hf_int_conv (ε / 2) (half_pos εpos) with ⟨M, hM⟩
      exact
        ⟨Max.max N M,
          fun n hn => by
            linarith [abs_lt.mp (hM n (le_trans (le_max_right _ _) hn)), h_rewrite n (le_trans (le_max_left _ _) hn)]⟩
  have h_limsup : Filter.limsup (fun n => ∫ ω, g n ω ∂μ) atTop ≤ ∫ ω, g_lim ω ∂μ := by
    have h_fatou :
        Filter.liminf (fun n => ∫ ω, (h n ω - g n ω) ∂μ) Filter.atTop ≥
          ∫ ω, (h_lim ω - g_lim ω) ∂μ := by
      have h_limsup :
          Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (h n ω - g n ω) ∂μ) Filter.atTop ≥
            ∫⁻ ω, ENNReal.ofReal (h_lim ω - g_lim ω) ∂μ := by
        refine' le_trans _ (MeasureTheory.lintegral_liminf_le' _)
        · refine' MeasureTheory.lintegral_mono_ae _
          filter_upwards [hg_ae, hh_ae] with ω hω₁ hω₂
          exact le_of_eq (by rw [Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal (hω₂.sub hω₁))])
        · exact fun n =>
            ((hh_int n).aemeasurable.sub (hg_int n).aemeasurable).ennreal_ofReal
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      ·
        refine' le_trans (ENNReal.toReal_mono ?_ h_limsup) _
        ·
          have h_limsup :
              ∀ n, ∫⁻ ω, ENNReal.ofReal (h n ω - g n ω) ∂μ ≤
                ∫⁻ ω, ENNReal.ofReal (h n ω - f n ω) ∂μ := by
            intro n
            apply MeasureTheory.lintegral_mono_ae
            filter_upwards [ (h_ineq n).1, (h_ineq n).2 ] with ω hω₁ hω₂ using
              ENNReal.ofReal_le_ofReal (by linarith)
          have h_limsup :
              ∀ n,
                ∫⁻ ω, ENNReal.ofReal (h n ω - f n ω) ∂μ =
                  ENNReal.ofReal (∫ ω, (h n ω - f n ω) ∂μ) := by
            intro n
            rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
            · exact (hh_int n).sub (hf_int n)
            ·
              filter_upwards [ (h_ineq n).1, (h_ineq n).2 ] with ω hω₁ hω₂ using
                sub_nonneg_of_le (le_trans hω₁ hω₂)
          have h_limsup :
              Filter.Tendsto
                (fun n => ENNReal.ofReal (∫ ω, (h n ω - f n ω) ∂μ))
                Filter.atTop
                (nhds (ENNReal.ofReal (∫ ω, (h_lim ω - f_lim ω) ∂μ))) := by
            convert ENNReal.tendsto_ofReal (hh_int_conv.sub hf_int_conv) using 1
            · exact funext fun n => by rw [MeasureTheory.integral_sub (hh_int n) (hf_int n)]
            · rw [MeasureTheory.integral_sub hh_lim_int hf_lim_int]
          refine' ne_of_lt (lt_of_le_of_lt (Filter.liminf_le_of_frequently_le _ _) _)
          ·
            exact ENNReal.ofReal (∫ ω, h_lim ω - f_lim ω ∂μ) + 1
          ·
            exact
              Filter.Eventually.frequently <|
                by
                  filter_upwards
                    [h_limsup.eventually (gt_mem_nhds <| ENNReal.lt_add_right (by aesop) one_ne_zero)]
                    with n hn
                  exact le_trans (by aesop) hn.le
          · exact ⟨0, Filter.Eventually.of_forall fun n => zero_le⟩
          · exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩
        ·
          rw [Filter.liminf_congr (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop 0) fun n hn => ?_)]
          any_goals exact fun n => ENNReal.ofReal (∫ ω, h n ω - g n ω ∂μ)
          ·
            rw [Filter.liminf_eq, Filter.liminf_eq]
            rw [ENNReal.toReal_sSup]
            ·
              refine' csSup_le _ _ <;> norm_num
              · exact ⟨0, ⟨0, fun n hn => zero_le⟩⟩
              ·
                rintro b x n hx rfl
                refine' le_csSup _ _
                ·
                  refine' ⟨_, fun a ha => _⟩
                  · exact (∫ ω, h_lim ω ∂μ) - (∫ ω, f_lim ω ∂μ)
                  ·
                    obtain ⟨m, hm⟩ := ha
                    refine' le_of_tendsto_of_tendsto tendsto_const_nhds (hh_int_conv.sub hf_int_conv) (Filter.eventually_atTop.mpr ⟨Max.max n m, fun k hk => _⟩)
                    refine' le_trans (hm k (le_trans (le_max_right _ _) hk)) _
                    rw [MeasureTheory.integral_sub (hh_int k) (hg_int k)]
                    refine' sub_le_sub_left _ _
                    apply_rules [MeasureTheory.integral_mono_ae]
                    exact (h_ineq k).1
                ·
                  use n
                  intro m hm
                  specialize hx m hm
                  rw [ENNReal.le_ofReal_iff_toReal_le] at hx <;> norm_num at *
                  aesop
                  · exact ne_of_lt (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
                  · exact MeasureTheory.integral_nonneg_of_ae (by filter_upwards [(h_ineq m).2] with ω hω using sub_nonneg_of_le hω)
            · exact fun r hr => ne_of_lt <| lt_of_le_of_lt (hr.exists.choose_spec) <| ENNReal.ofReal_lt_top
          ·
            rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
            · exact (hh_int n).sub (hg_int n)
            · filter_upwards [(h_ineq n).2] with ω hω using sub_nonneg_of_le hω
      · filter_upwards [hgh_lim] with ω hω using sub_nonneg_of_le hω
      · exact hh_lim_int.1.sub hgi.1
    simp_all +decide [MeasureTheory.integral_sub, hf_int, hg_int, hh_int, hgi, hf_lim_int, hh_lim_int]
    rw [show liminf (fun n => ∫ ω, h n ω ∂μ - ∫ ω, g n ω ∂μ) atTop =
        (∫ ω, h_lim ω ∂μ) - limsup (fun n => ∫ ω, g n ω ∂μ) atTop from ?_] at h_fatou
    · linarith
    ·
      refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num
      ·
        refine' ⟨0, ⟨0, fun n hn => _⟩⟩
        rw [← MeasureTheory.integral_sub (hh_int n) (hg_int n)]
        exact MeasureTheory.integral_nonneg_of_ae (by filter_upwards [(h_ineq n).2] with ω hω using sub_nonneg_of_le hω)
      ·
        intro a x hx
        refine' le_of_forall_pos_le_add fun ε ε_pos => _
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∫ ω, h n ω ∂μ ≤ ∫ ω, h_lim ω ∂μ + ε := by
          exact Filter.eventually_atTop.mp (hh_int_conv.eventually (ge_mem_nhds <| lt_add_of_pos_right _ ε_pos))
        rw [show limsup (fun n => ∫ ω, g n ω ∂μ) atTop = sInf {a | ∀ᶠ n in atTop, ∫ ω, g n ω ∂μ ≤ a} from ?_]
        ·
          rw [sub_add_eq_add_sub]
          refine' le_sub_comm.mp _
          refine' csInf_le _ _
          ·
            use ∫ ω, f_lim ω ∂μ
            rintro a ha
            refine' le_of_tendsto hf_int_conv _
            filter_upwards [ha, Filter.eventually_ge_atTop N] with n hn hn' using
              le_trans (MeasureTheory.integral_mono_ae (hf_int n) (hg_int n) ((h_ineq n).1)) hn
          ·
            filter_upwards [Filter.eventually_ge_atTop x, Filter.eventually_ge_atTop N] with n hn hn' using by
              linarith [hx n hn, hN n hn']
        · rw [Filter.limsup_eq]
      ·
        intro w hw
        rw [lt_sub_comm] at hw
        rw [limsup_eq] at hw
        norm_num +zetaDelta at *
        rcases
            exists_lt_of_csInf_lt
              (show {a : ℝ | ∃ n, ∀ m ≥ n, ∫ ω, g m ω ∂μ ≤ a}.Nonempty from by
                have h_bounded : ∃ C, ∀ n, ∫ ω, g n ω ∂μ ≤ C := by
                  have h_bounded : ∀ n, ∫ ω, g n ω ∂μ ≤ ∫ ω, h n ω ∂μ := by
                    intro n
                    exact MeasureTheory.integral_mono_ae (hg_int n) (hh_int n) ((h_ineq n).2)
                  exact ⟨_, fun n => le_trans (h_bounded n) (le_csSup (hh_int_conv.bddAbove_range) ⟨n, rfl⟩)⟩
                exact ⟨h_bounded.choose, ⟨0, fun n hn => h_bounded.choose_spec n⟩⟩) hw with
          ⟨a, ⟨n, hn⟩, ha⟩
        rcases Metric.tendsto_atTop.mp hh_int_conv ((∫ ω, h_lim ω ∂μ - w - a) / 2)
            (half_pos (sub_pos.mpr ha)) with ⟨m, hm⟩
        exact
          ⟨w + (∫ ω, h_lim ω ∂μ - w - a) / 2,
            ⟨Max.max n m, fun k hk => by
              linarith [abs_lt.mp (hm k (le_trans (le_max_right n m) hk)), hn k (le_trans (le_max_left n m) hk)]⟩,
            by linarith⟩
  have h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ ω, g n ω ∂μ) := by
    have h_bounded : ∀ n, ∫ ω, g n ω ∂μ ≤ ∫ ω, h n ω ∂μ := by
      exact fun n => MeasureTheory.integral_mono_ae (hg_int n) (hh_int n) ((h_ineq n).2)
    exact ⟨_, Filter.eventually_atTop.mpr ⟨0, fun n hn => le_trans (h_bounded n) (le_ciSup (hh_int_conv.bddAbove_range) n)⟩⟩
  have h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ∫ ω, g n ω ∂μ) := by
    have h_bdd_below : ∀ n, ∫ ω, f n ω ∂μ ≤ ∫ ω, g n ω ∂μ := by
      exact fun n => MeasureTheory.integral_mono_ae (hf_int n) (hg_int n) ((h_ineq n).1)
    have := hf_int_conv.bddBelow_range
    exact ⟨this.choose, Filter.eventually_atTop.mpr ⟨0, fun n hn => le_trans (this.choose_spec ⟨n, rfl⟩) (h_bdd_below n)⟩⟩
  have h_eq : Filter.liminf (fun n => ∫ ω, g n ω ∂μ) atTop = ∫ ω, g_lim ω ∂μ :=
    le_antisymm (by linarith [Filter.liminf_le_limsup h_bdd_above h_bdd_below]) h_liminf
  have h_eq2 : Filter.limsup (fun n => ∫ ω, g n ω ∂μ) atTop = ∫ ω, g_lim ω ∂μ :=
    le_antisymm h_limsup (by linarith [Filter.liminf_le_limsup h_bdd_above h_bdd_below])
  exact tendsto_of_liminf_eq_limsup h_eq h_eq2
