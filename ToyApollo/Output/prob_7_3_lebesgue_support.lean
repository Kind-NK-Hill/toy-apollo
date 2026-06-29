import Mathlib
import ToyApollo.Output.thm_1_1_basic
import ToyApollo.Output.thm_7_8_sandwich_support

open MeasureTheory Set Filter

noncomputable section

/-- The strict-interval statement surface selected for Problem 7.3(a).

This is only a statement-shape support definition: it records that the focused
part (a) route uses `a < b`, the boundedness and left-endpoint atom hypotheses,
    and the RS-integrability/a.e.-relative-continuity iff. It deliberately
contains no Problem 7.3(b) completion claim. -/
def prob_7_3_partA_strict_statement
    {a b : ℝ} {f : ℝ → ℝ} {α : StieltjesFunction ℝ}
    (_hab : a < b)
    (_hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (_hAtom : α.measure {a} = 0) : Prop :=
  RSIntegrable f α a b ↔
    ∀ᵐ x ∂(α.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x

theorem prob_7_3_statement_alignment_strict_interval
    {a b : ℝ} {f : ℝ → ℝ} {α : StieltjesFunction ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hAtom : α.measure {a} = 0) :
    prob_7_3_partA_strict_statement (a := a) (b := b) (f := f) (α := α)
        hab hBounded hAtom ↔
      (RSIntegrable f α a b ↔
        ∀ᵐ x ∂(α.measure.restrict (Icc a b)),
          ContinuousWithinAt f (Icc a b) x) := by
  rfl

def prob_7_3_relativeDiscontinuitySetOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}

theorem prob_7_3_ae_continuity_iff_null_not_continuous
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ} :
    (∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ↔
      (μ.restrict (Icc a b)) {x | ¬ ContinuousWithinAt f (Icc a b) x} = 0 := by
  exact ae_iff

theorem prob_7_3_relativeDiscontinuitySetOn_null_of_ae_continuity
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) :
    (μ.restrict (Icc a b)) (prob_7_3_relativeDiscontinuitySetOn f a b) = 0 := by
  have hbad :
      (μ.restrict (Icc a b)) {x | ¬ ContinuousWithinAt f (Icc a b) x} = 0 :=
    (prob_7_3_ae_continuity_iff_null_not_continuous
      (μ := μ) (a := a) (b := b) (f := f)).1 hcont
  exact measure_mono_null (by
    intro x hx
    exact hx.2) hbad

theorem prob_7_3_ae_continuity_null_discontinuity_form
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ} :
    ((∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ↔
      (μ.restrict (Icc a b)) {x | ¬ ContinuousWithinAt f (Icc a b) x} = 0) ∧
      ((∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) →
        (μ.restrict (Icc a b)) (prob_7_3_relativeDiscontinuitySetOn f a b) = 0) := by
  exact ⟨prob_7_3_ae_continuity_iff_null_not_continuous μ,
    prob_7_3_relativeDiscontinuitySetOn_null_of_ae_continuity μ⟩

def prob_7_3_relativeLocalOscillationAtLeast
    (f : ℝ → ℝ) (a b x eta : ℝ) : Prop :=
  x ∈ Icc a b ∧ 0 < eta ∧
    ∀ delta : ℝ, 0 < delta →
      ∃ y : ℝ, y ∈ Icc a b ∧ |y - x| < delta ∧
        ∃ z : ℝ, z ∈ Icc a b ∧ |z - x| < delta ∧ eta ≤ |f y - f z|

def prob_7_3_largeOscillationSet (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : Set ℝ :=
  {x | prob_7_3_relativeLocalOscillationAtLeast f a b x
    ((1 : ℝ) / ((n : ℝ) + 1))}

theorem prob_7_3_positive_eta_to_inverse_nat_level {eta : ℝ} (heta : 0 < eta) :
    ∃ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ eta := by
  rcases exists_nat_one_div_lt heta with ⟨n, hn⟩
  refine ⟨n, ?_, le_of_lt hn⟩
  positivity

theorem prob_7_3_relativeLocalOscillationAtLeast_mono
    {f : ℝ → ℝ} {a b x eta eta' : ℝ}
    (heta' : 0 < eta') (hle : eta' ≤ eta)
    (hosc : prob_7_3_relativeLocalOscillationAtLeast f a b x eta) :
    prob_7_3_relativeLocalOscillationAtLeast f a b x eta' := by
  rcases hosc with ⟨hx, _heta, hlocal⟩
  refine ⟨hx, heta', ?_⟩
  intro delta hdelta
  rcases hlocal delta hdelta with ⟨y, hy, hydist, z, hz, hzdist, hyz⟩
  exact ⟨y, hy, hydist, z, hz, hzdist, hle.trans hyz⟩

theorem prob_7_3_continuousWithinAt_local_two_point_oscillation
    {f : ℝ → ℝ} {a b x eps : ℝ}
    (hf : ContinuousWithinAt f (Icc a b) x) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ y : ℝ, y ∈ Icc a b → |y - x| < delta →
        ∀ z : ℝ, z ∈ Icc a b → |z - x| < delta →
          |f y - f z| < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases (Metric.continuousWithinAt_iff.mp hf (eps / 2) hhalf) with
    ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro y hy hydist z hz hzdist
  have hyclose : |f y - f x| < eps / 2 := by
    have := Hdelta hy (by simpa [Real.dist_eq] using hydist)
    simpa [Real.dist_eq] using this
  have hzclose : |f z - f x| < eps / 2 := by
    have := Hdelta hz (by simpa [Real.dist_eq] using hzdist)
    simpa [Real.dist_eq] using this
  have htri : |f y - f z| ≤ |f y - f x| + |f z - f x| := by
    calc
      |f y - f z| = |(f y - f x) + -(f z - f x)| := by ring_nf
      _ ≤ |f y - f x| + |-(f z - f x)| :=
        abs_add_le (f y - f x) (-(f z - f x))
      _ = |f y - f x| + |f z - f x| := by rw [abs_neg]
  linarith

theorem prob_7_3_not_continuousWithinAt_positive_relative_oscillation
    {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Icc a b) (hf : ¬ ContinuousWithinAt f (Icc a b) x) :
    ∃ eta : ℝ, 0 < eta ∧
      prob_7_3_relativeLocalOscillationAtLeast f a b x eta := by
  classical
  rw [Metric.continuousWithinAt_iff] at hf
  push_neg at hf
  rcases hf with ⟨eta, heta, hbad⟩
  refine ⟨eta, heta, hx, heta, ?_⟩
  intro delta hdelta
  rcases hbad delta hdelta with ⟨y, hy, hydist, hyval⟩
  refine ⟨y, hy, ?_, x, hx, ?_, ?_⟩
  · simpa [Real.dist_eq] using hydist
  · simpa using hdelta
  · simpa [Real.dist_eq] using hyval

theorem prob_7_3_discontinuity_within_implies_largeOscillationSet_mem
    {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Icc a b) (hf : ¬ ContinuousWithinAt f (Icc a b) x) :
    ∃ n : ℕ, x ∈ prob_7_3_largeOscillationSet f a b n := by
  rcases prob_7_3_not_continuousWithinAt_positive_relative_oscillation
      (f := f) (a := a) (b := b) hx hf with
    ⟨eta, heta, hosc⟩
  rcases prob_7_3_positive_eta_to_inverse_nat_level heta with ⟨n, hnpos, hnle⟩
  refine ⟨n, ?_⟩
  exact prob_7_3_relativeLocalOscillationAtLeast_mono hnpos hnle hosc

theorem prob_7_3_restrict_left_endpoint_atom_zero
    (μ : Measure ℝ) {a b : ℝ} (hAtom : μ {a} = 0) :
    (μ.restrict (Icc a b)) {a} = 0 := by
  have hle : (μ.restrict (Icc a b)) {a} ≤ μ {a} :=
    (Measure.restrict_le_self (μ := μ) (s := Icc a b)) {a}
  exact le_antisymm (by simpa [hAtom] using hle) (zero_le _)

theorem prob_7_3_endpoint_atom_convention_support
    {a b : ℝ} (α : StieltjesFunction ℝ) (hAtom : α.measure {a} = 0) :
    (α.measure.restrict (Icc a b)) {a} = 0 := by
  exact prob_7_3_restrict_left_endpoint_atom_zero α.measure hAtom

theorem prob_7_3_rsIntegrable_unpacks_to_fine_upper_lower_gap_small
    {a b : ℝ} {f alpha : ℝ → ℝ} (hRS : RSIntegrable f alpha a b) :
    DarbouxRS.SourceHypotheses a b f alpha ∧
      ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
        ∀ P : DarbouxRS.Partition a b, P.mesh < delta →
          DarbouxRS.upperSum P f alpha - DarbouxRS.lowerSum P f alpha < eps := by
  let L := rsIntegral f alpha a b hRS
  have hUL : rsUpperLowerCommonLimit a b f alpha L :=
    rsIntegral_source_spec hRS
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := by linarith
  rcases hlim (eps / 2) hhalf with ⟨delta, hdelta, hdelta_spec⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  rcases hdelta_spec P hmesh with ⟨hupper, hlower⟩
  have hupper_lt : DarbouxRS.upperSum P f alpha - L < eps / 2 :=
    (abs_lt.mp hupper).2
  have hlower_lt : L - DarbouxRS.lowerSum P f alpha < eps / 2 := by
    have h := (abs_lt.mp hlower).1
    linarith
  linarith

theorem prob_7_3_restricted_measure_partition_cell_toReal
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    {i : ℕ} (hi : i < P.n) :
    ((F.measure.restrict (Icc a b)) (Ioc (P.pts i) (P.pts (i + 1)))).toReal =
      F (P.pts (i + 1)) - F (P.pts i) := by
  rw [Measure.restrict_apply measurableSet_Ioc]
  have hcell_subset : Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b :=
    thm_7_8_partition_Ioc_subset_Icc P hi
  have hcell_inter :
      Ioc (P.pts i) (P.pts (i + 1)) ∩ Icc a b =
        Ioc (P.pts i) (P.pts (i + 1)) := by
    exact inter_eq_self_of_subset_left hcell_subset
  rw [hcell_inter]
  exact thm_7_8_stieltjes_measure_Ioc_toReal F
    (le_of_lt (P.strict_mono i hi))

theorem prob_7_3_stieltjes_restricted_measure_partition_cells_endpoint_atom
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (hAtom : F.measure {a} = 0) :
    (∀ i : ℕ, ∀ _hi : i < P.n,
      ((F.measure.restrict (Icc a b)) (Ioc (P.pts i) (P.pts (i + 1)))).toReal =
        F (P.pts (i + 1)) - F (P.pts i)) ∧
    (F.measure.restrict (Icc a b)) {a} = 0 ∧
    (∀ x : ℝ, x ∈ Icc a b → x ≠ a →
      ∃ i : ℕ, i < P.n ∧ x ∈ Ioc (P.pts i) (P.pts (i + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact prob_7_3_restricted_measure_partition_cell_toReal F P hi
  · exact prob_7_3_endpoint_atom_convention_support F hAtom
  · intro x hx hxne
    exact thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hx hxne
