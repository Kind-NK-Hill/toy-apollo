import Mathlib
import ToyApollo.Output.thm_13_17

/-!
Support layer for Theorem 13.18.

This file owns the stopped-value interface, stopped-integral limit bridge,
DCT domination lemmas, and the three optional-stopping case assemblers used by
the source-facing parent theorem.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

noncomputable section
/-- The almost-sure identification of a real-valued representative `XT` with
the stopped value `X_T`.  Definition 13.8 records the infinite case as `none`;
Theorem 13.18 only uses this representative on the almost-sure finite event. -/
def thm_13_18_stoppedValueAgreement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ n : ℕ, T ω = (n : WithTop ℕ) → XT ω = X n ω

/-- Canonical real-valued representative of `X_T`.  On the finite event it is
the textbook stopped value; on `T = ∞` it uses `0`, which is irrelevant in the
almost-sure finite cases of Theorem 13.18. -/
def thm_13_18_stoppedValueReal {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω =>
    match T ω with
    | none => 0
    | some n => X n ω

theorem thm_13_18_stoppedValueReal_agreement {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) :
    thm_13_18_stoppedValueAgreement P X T
      (thm_13_18_stoppedValueReal X T) := by
  filter_upwards with ω n hT
  simp [thm_13_18_stoppedValueReal, hT]

theorem thm_13_18_stoppedValueReal_matches_option {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) (ω : Ω) (n : ℕ)
    (hT : T ω = (n : WithTop ℕ)) :
    def_13_8_stoppedValue X T ω =
      some (thm_13_18_stoppedValueReal X T ω) := by
  simp [def_13_8_stoppedValue, thm_13_18_stoppedValueReal, hT]

/-- The convergence of finite stopped expectations to the expectation of the
stopped value.  In cases (ii) and (iii), this is the Dominated Convergence
Theorem step in the textbook proof. -/
def thm_13_18_stoppedIntegralLimit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  Tendsto
    (fun n : ℕ => ∫ ω, def_13_9_stoppedProcess X T n ω ∂P)
    atTop
    (𝓝 (∫ ω, XT ω ∂P))

theorem thm_13_18_stoppedProcess_tendsto_of_agreement {Ω : Type*}
    [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) {ω : Ω} (hFinite : T ω < ⊤)
    (hAgree : ∀ n : ℕ, T ω = (n : WithTop ℕ) → XT ω = X n ω) :
    Tendsto (fun n : ℕ => def_13_9_stoppedProcess X T n ω) atTop
      (𝓝 (XT ω)) := by
  cases hTω : T ω with
  | top =>
      have hnot : ¬ (⊤ : WithTop ℕ) < ⊤ := by simp
      exact False.elim (hnot (by simpa [hTω] using hFinite))
  | coe k =>
      refine tendsto_nhds_of_eventually_eq ?_
      rw [Filter.eventually_atTop]
      refine ⟨k, ?_⟩
      intro n hn
      have hXT : X k ω = XT ω := (hAgree k (by simpa [hTω])).symm
      simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex,
        hTω, Nat.min_eq_left hn, hXT]

theorem thm_13_18_stoppedProcess_uniformBound {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ} {K : ℝ}
    (hXBound : ∀ n : ℕ, ∀ᵐ ω ∂P, |X n ω| ≤ K) :
    ∀ n : ℕ, ∀ᵐ ω ∂P,
      |def_13_9_stoppedProcess X T n ω| ≤ K := by
  intro n
  have hAll : ∀ᵐ ω ∂P, ∀ m : ℕ, |X m ω| ≤ K :=
    eventually_countable_forall.2 hXBound
  filter_upwards [hAll] with ω hω
  simpa [def_13_9_stoppedProcess] using
    hω (def_13_9_stoppedIndex T n ω)

theorem thm_13_18_stoppedIntegralLimit_of_uniformBound {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hFinite : ∀ᵐ ω ∂P, T ω < ⊤)
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT)
    (hMeas : ∀ n : ℕ,
      AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hBound :
      ∃ K : ℝ,
        0 ≤ K ∧
          Integrable (fun _ : Ω => K) P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P, |X n ω| ≤ K) :
    thm_13_18_stoppedIntegralLimit P X T XT := by
  rcases hBound with ⟨K, _hK_nonneg, hKIntegrable, hXBound⟩
  have hStoppedBound :
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        |def_13_9_stoppedProcess X T n ω| ≤ K :=
    thm_13_18_stoppedProcess_uniformBound
      (P := P) (X := X) (T := T) hXBound
  have hLimit :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => def_13_9_stoppedProcess X T n ω)
          atTop (𝓝 (XT ω)) := by
    filter_upwards [hFinite, hAgree] with ω hFiniteω hAgreeω
    exact thm_13_18_stoppedProcess_tendsto_of_agreement X T XT
      hFiniteω hAgreeω
  have hNormBound :
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖def_13_9_stoppedProcess X T n ω‖ ≤ (fun _ : Ω => K) ω := by
    intro n
    filter_upwards [hStoppedBound n] with ω hω
    simpa [Real.norm_eq_abs] using hω
  exact
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω => K)
      hMeas
      hKIntegrable
      hNormBound
      hLimit

theorem thm_13_18_stoppedIntegralLimit_of_integrableDomination {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hFinite : ∀ᵐ ω ∂P, T ω < ⊤)
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT)
    (hMeas : ∀ n : ℕ,
      AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hDomination : ∃ G : Ω → ℝ,
      Integrable G P ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P,
          |def_13_9_stoppedProcess X T n ω| ≤ G ω) :
    thm_13_18_stoppedIntegralLimit P X T XT := by
  rcases hDomination with ⟨G, hGIntegrable, hStoppedBound⟩
  have hLimit :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => def_13_9_stoppedProcess X T n ω)
          atTop (𝓝 (XT ω)) := by
    filter_upwards [hFinite, hAgree] with ω hFiniteω hAgreeω
    exact thm_13_18_stoppedProcess_tendsto_of_agreement X T XT
      hFiniteω hAgreeω
  have hNormBound :
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖def_13_9_stoppedProcess X T n ω‖ ≤ G ω := by
    intro n
    filter_upwards [hStoppedBound n] with ω hω
    simpa [Real.norm_eq_abs] using hω
  exact
    MeasureTheory.tendsto_integral_of_dominated_convergence
      G
      hMeas
      hGIntegrable
      hNormBound
      hLimit

theorem thm_13_18_telescoping_abs_bound {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ω : Ω) {c : ℝ} (hc : 0 ≤ c)
    (hIncrementBound : ∀ k : ℕ, |X (k + 1) ω - X k ω| ≤ c) :
    ∀ m : ℕ, |X m ω| ≤ |X 0 ω| + c * (m : ℝ) := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hStep :
          |X (m + 1) ω| ≤ |X m ω| + |X (m + 1) ω - X m ω| := by
        have hDecomp :
            X (m + 1) ω = X m ω + (X (m + 1) ω - X m ω) := by
          ring
        calc
          |X (m + 1) ω|
              = |X m ω + (X (m + 1) ω - X m ω)| := by
                exact congrArg abs hDecomp
          _ ≤ |X m ω| + |X (m + 1) ω - X m ω| :=
                abs_add_le (X m ω) (X (m + 1) ω - X m ω)
      calc
        |X (m + 1) ω|
            ≤ |X m ω| + |X (m + 1) ω - X m ω| := hStep
        _ ≤ (|X 0 ω| + c * (m : ℝ)) + c :=
            add_le_add ih (hIncrementBound m)
        _ = |X 0 ω| + c * ((m + 1 : ℕ) : ℝ) := by
            norm_num
            ring

theorem thm_13_18_stoppedProcess_boundedIncrement_domination {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {τ : Ω → ℕ} {c : ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hFinite : ∀ᵐ ω ∂P, T ω = (τ ω : WithTop ℕ))
    (hTIntegrable : Integrable (fun ω => (τ ω : ℝ)) P)
    (hc : 0 ≤ c)
    (hIncrementBound : ∀ n : ℕ, ∀ᵐ ω ∂P,
      |X (n + 1) ω - X n ω| ≤ c) :
    ∃ G : Ω → ℝ,
      Integrable G P ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P,
          |def_13_9_stoppedProcess X T n ω| ≤ G ω := by
  refine ⟨fun ω => |X 0 ω| + c * (τ ω : ℝ), ?_, ?_⟩
  · have hX0 : Integrable (X 0) P := def_13_7_integrable hM 0
    have hAbsX0 : Integrable (fun ω => |X 0 ω|) P := by
      simpa [Real.norm_eq_abs] using hX0.norm
    exact hAbsX0.add (hTIntegrable.const_mul c)
  · intro n
    have hAllIncrements :
        ∀ᵐ ω ∂P, ∀ k : ℕ, |X (k + 1) ω - X k ω| ≤ c :=
      eventually_countable_forall.2 hIncrementBound
    filter_upwards [hFinite, hAllIncrements] with ω hTω hIncω
    have hIndexEq :
        def_13_9_stoppedIndex T n ω = min (τ ω) n := by
      simp [def_13_9_stoppedIndex, hTω]
    have hIndexLeTau :
        def_13_9_stoppedIndex T n ω ≤ τ ω := by
      rw [hIndexEq]
      exact Nat.min_le_left (τ ω) n
    have hIndexLeTauReal :
        ((def_13_9_stoppedIndex T n ω : ℕ) : ℝ) ≤ (τ ω : ℝ) := by
      exact_mod_cast hIndexLeTau
    have hMul :
        c * ((def_13_9_stoppedIndex T n ω : ℕ) : ℝ) ≤
          c * (τ ω : ℝ) :=
      mul_le_mul_of_nonneg_left hIndexLeTauReal hc
    have hTel :=
      thm_13_18_telescoping_abs_bound X ω hc hIncω
        (def_13_9_stoppedIndex T n ω)
    calc
      |def_13_9_stoppedProcess X T n ω|
          = |X (def_13_9_stoppedIndex T n ω) ω| := by
            simp [def_13_9_stoppedProcess]
      _ ≤ |X 0 ω| +
            c * ((def_13_9_stoppedIndex T n ω : ℕ) : ℝ) := hTel
      _ ≤ |X 0 ω| + c * (τ ω : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hMul |X 0 ω|

/-- Optional-stopping case (i): `T` is bounded almost surely, and the finite
stopped process at that bound has the same integral as `X_T`. -/
def thm_13_18_boundedStoppingCase {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  ∃ C : ℕ,
    (∀ᵐ ω ∂P, T ω ≤ (C : WithTop ℕ)) ∧
      thm_13_18_stoppedValueAgreement P X T XT

/-- Optional-stopping case (ii): the stopping time is finite almost surely, the
martingale is uniformly bounded, and dominated convergence identifies the
limit of stopped expectations with `E[X_T]`. -/
def thm_13_18_uniformBoundCase {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, T ω < ⊤) ∧
    thm_13_18_stoppedValueAgreement P X T XT ∧
      ∃ K : ℝ,
        0 ≤ K ∧
          Integrable (fun _ : Ω => K) P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P, |X n ω| ≤ K

/-- Optional-stopping case (iii): `T` has an integrable finite representative,
the increments are uniformly bounded, and the textbook telescoping domination
gives the dominated-convergence limit. -/
def thm_13_18_boundedIncrementCase {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  ∃ τ : Ω → ℕ,
    (∀ᵐ ω ∂P, T ω = (τ ω : WithTop ℕ)) ∧
      Integrable (fun ω => (τ ω : ℝ)) P ∧
        thm_13_18_stoppedValueAgreement P X T XT ∧
          (∃ c : ℝ,
            0 ≤ c ∧
              ∀ n : ℕ, ∀ᵐ ω ∂P,
                |X (n + 1) ω - X n ω| ≤ c)

/-- The three textbook alternatives in Theorem 13.18. -/
def thm_13_18_optionalStoppingCases {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (XT : Ω → ℝ) : Prop :=
  thm_13_18_boundedStoppingCase P X T XT ∨
    thm_13_18_uniformBoundCase P X T XT ∨
      thm_13_18_boundedIncrementCase P X T XT

/-- Canonical version of case (i), using the internally defined representative
of `X_T`. -/
def thm_13_18_boundedStoppingCaseCanonical {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (_X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) : Prop :=
  ∃ C : ℕ, ∀ᵐ ω ∂P, T ω ≤ (C : WithTop ℕ)

def thm_13_18_uniformBoundCaseCanonical {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) : Prop :=
  (∀ᵐ ω ∂P, T ω < ⊤) ∧
    ∃ K : ℝ,
      0 ≤ K ∧
        Integrable (fun _ : Ω => K) P ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P, |X n ω| ≤ K

def thm_13_18_boundedIncrementCaseCanonical {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) : Prop :=
  ∃ τ : Ω → ℕ,
    (∀ᵐ ω ∂P, T ω = (τ ω : WithTop ℕ)) ∧
      Integrable (fun ω => (τ ω : ℝ)) P ∧
        (∃ c : ℝ,
          0 ≤ c ∧
            ∀ n : ℕ, ∀ᵐ ω ∂P,
              |X (n + 1) ω - X n ω| ≤ c)

def thm_13_18_optionalStoppingCasesCanonical {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ) : Prop :=
  thm_13_18_boundedStoppingCaseCanonical P X T ∨
    thm_13_18_uniformBoundCaseCanonical P X T ∨
      thm_13_18_boundedIncrementCaseCanonical P X T

theorem thm_13_18_boundedStoppingCase_of_canonical {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hCase : thm_13_18_boundedStoppingCaseCanonical P X T) :
    thm_13_18_boundedStoppingCase P X T
      (thm_13_18_stoppedValueReal X T) := by
  rcases hCase with ⟨C, hBounded⟩
  exact ⟨C, hBounded, thm_13_18_stoppedValueReal_agreement P X T⟩

theorem thm_13_18_uniformBoundCase_of_canonical {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hCase : thm_13_18_uniformBoundCaseCanonical P X T) :
    thm_13_18_uniformBoundCase P X T
      (thm_13_18_stoppedValueReal X T) := by
  rcases hCase with ⟨hFinite, hBound⟩
  exact ⟨hFinite, thm_13_18_stoppedValueReal_agreement P X T,
    hBound⟩

theorem thm_13_18_boundedIncrementCase_of_canonical {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hCase : thm_13_18_boundedIncrementCaseCanonical P X T) :
    thm_13_18_boundedIncrementCase P X T
      (thm_13_18_stoppedValueReal X T) := by
  rcases hCase with
    ⟨τ, hFinite, hTIntegrable, hIncrementBound⟩
  exact ⟨τ, hFinite, hTIntegrable,
    thm_13_18_stoppedValueReal_agreement P X T,
    hIncrementBound⟩

theorem thm_13_18_optionalStoppingCases_of_canonical {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hCase : thm_13_18_optionalStoppingCasesCanonical P X T) :
    thm_13_18_optionalStoppingCases P X T
      (thm_13_18_stoppedValueReal X T) := by
  rcases hCase with hBounded | hRest
  · exact Or.inl (thm_13_18_boundedStoppingCase_of_canonical hBounded)
  · rcases hRest with hUniform | hIncrement
    · exact Or.inr
        (Or.inl (thm_13_18_uniformBoundCase_of_canonical hUniform))
    · exact Or.inr
        (Or.inr (thm_13_18_boundedIncrementCase_of_canonical hIncrement))

theorem thm_13_18_constant_limit_of_stopped_expectations {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hConst : ∀ n : ℕ,
      ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
        ∫ ω, X 0 ω ∂P)
    (hLimit : thm_13_18_stoppedIntegralLimit P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hStoppedTend :
      Tendsto
        (fun n : ℕ => ∫ ω, def_13_9_stoppedProcess X T n ω ∂P)
        atTop
        (𝓝 (∫ ω, X 0 ω ∂P)) := by
    simpa [hConst] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ∫ ω, X 0 ω ∂P) atTop
          (𝓝 (∫ ω, X 0 ω ∂P)))
  exact tendsto_nhds_unique hLimit hStoppedTend

theorem thm_13_18_boundedStopping_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {XT : Ω → ℝ} {C : ℕ}
    (hBounded : ∀ᵐ ω ∂P, T ω ≤ (C : WithTop ℕ))
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT) :
    XT =ᵐ[P] def_13_9_stoppedProcess X T C := by
  filter_upwards [hBounded, hAgree] with ω hBound hAgreeω
  cases hTω : T ω with
  | top =>
      have hnot : ¬ (⊤ : WithTop ℕ) ≤ (C : WithTop ℕ) := by simp
      exact False.elim (hnot (by simpa [hTω] using hBound))
  | coe k =>
      have hkC : k ≤ C := by
        exact WithTop.coe_le_coe.mp (by simpa [hTω] using hBound)
      have hXT : XT ω = X k ω := hAgreeω k (by simpa [hTω])
      simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex, hTω,
        Nat.min_eq_left hkC, hXT]

theorem thm_13_18_boundedStopping_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {XT : Ω → ℝ} {C : ℕ}
    (hBounded : ∀ᵐ ω ∂P, T ω ≤ (C : WithTop ℕ))
    (hAgree : thm_13_18_stoppedValueAgreement P X T XT) :
    ∫ ω, XT ω ∂P =
      ∫ ω, def_13_9_stoppedProcess X T C ω ∂P :=
  integral_congr_ae (thm_13_18_boundedStopping_ae_eq hBounded hAgree)

theorem thm_13_18_bounded_case {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {XT : Ω → ℝ}
    (hConst : ∀ n : ℕ,
      ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
        ∫ ω, X 0 ω ∂P)
    (hCase : thm_13_18_boundedStoppingCase P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  rcases hCase with ⟨C, hBounded, hAgree⟩
  have hIntegral :
      ∫ ω, XT ω ∂P =
        ∫ ω, def_13_9_stoppedProcess X T C ω ∂P :=
    thm_13_18_boundedStopping_integral_eq hBounded hAgree
  calc
    ∫ ω, XT ω ∂P =
        ∫ ω, def_13_9_stoppedProcess X T C ω ∂P := hIntegral
    _ = ∫ ω, X 0 ω ∂P := hConst C

theorem thm_13_18_uniformBound_case {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {XT : Ω → ℝ}
    (hMeas : ∀ n : ℕ,
      AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hConst : ∀ n : ℕ,
      ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
        ∫ ω, X 0 ω ∂P)
    (hCase : thm_13_18_uniformBoundCase P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  rcases hCase with ⟨hFinite, hAgree, hBound⟩
  have hLimit : thm_13_18_stoppedIntegralLimit P X T XT :=
    thm_13_18_stoppedIntegralLimit_of_uniformBound hFinite hAgree
      hMeas hBound
  exact thm_13_18_constant_limit_of_stopped_expectations hConst hLimit

theorem thm_13_18_boundedIncrement_case {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {XT : Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hMeas : ∀ n : ℕ,
      AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P)
    (hConst : ∀ n : ℕ,
      ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
        ∫ ω, X 0 ω ∂P)
    (hCase : thm_13_18_boundedIncrementCase P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  rcases hCase with
    ⟨_τ, _hFinite, _hTIntegrable, _hAgree, _hIncrementBound⟩
  have hFiniteTop : ∀ᵐ ω ∂P, T ω < ⊤ := by
    filter_upwards [_hFinite] with ω hTω
    simpa [hTω] using (WithTop.coe_lt_top (_τ ω))
  rcases _hIncrementBound with ⟨c, hc, hInc⟩
  have hDomination :
      ∃ G : Ω → ℝ,
        Integrable G P ∧
          ∀ n : ℕ, ∀ᵐ ω ∂P,
            |def_13_9_stoppedProcess X T n ω| ≤ G ω :=
    thm_13_18_stoppedProcess_boundedIncrement_domination
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (τ := _τ) (c := c)
      hM _hFinite _hTIntegrable hc hInc
  have hLimit : thm_13_18_stoppedIntegralLimit P X T XT :=
    thm_13_18_stoppedIntegralLimit_of_integrableDomination
      hFiniteTop _hAgree hMeas hDomination
  exact thm_13_18_constant_limit_of_stopped_expectations hConst hLimit
