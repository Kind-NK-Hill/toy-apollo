import Mathlib
import ToyApollo.Output.def_13_9
import ToyApollo.Output.thm_13_16

/-
TASK ID: thm_13_17
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{thmbox}{13.17}
\end{thmbox}

The stopped process .(XT

n )n\geq0 is a martingale relative to the filtration

(\mathcal{F}n)n\geq0, andE[XT

n ]= E[X0] for alln \geq 0.

\textit{Proof} The expectationE[XT

n ] is less than or equal to maxk E[Xk], with maximum

taken over k = 0, 1,...,n Since E[Xk] is finite for all k, the maximum is also

finite.

For n \geq 0,t h e n-th random variable XT

n in the stopped process is a function of

X0,X 1,...,X n and T Since T is a stopping time, XT

n is\mathcal{F}n-measurable.

We write XT

n+1 as XT

n + (Xn+1 - Xn)1{T> n}The conditional expectation of

XT

n+1 given. \mathcal{F}n is

E[XT

n+1\vert\mathcal{F}n]= XT

n + 1{T> n}E[Xn+1 - Xn\vert\mathcal{F}n]= XT

n + 1{T> n} \cdot 0 = XT

n .

This proves that XT

n is a martingale relative to .(\mathcal{F}n)n\geq0.

Because.(XT

n )n\geq1 is a martingale, the last statement about the expectation. E[XT

n ]

follows from Theorem 13.16. \hfill $\square$

In contrast to the previous theorem, we are not just interested in the expected

value of the stopped process at a particular time, but also interested in the expected

value of the martingale sequence when it stops. The following theorem is called

the martingale stopping theorem, which is also known as Doob's optional stopping

theorem. Under the gambling scenario, the first condition in the theorem means

that a gambler has to leave the casino within a fixed duration. The second one

requires that the game must end when the gambler lose all of his fortune or win

a predetermined amount of money. The third one models the scenario in which the

increments are uniformly bounded.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/-- The event on which the martingale has not stopped before the transition
from `n` to `n+1`. -/
def thm_13_17_activeEvent {Ω : Type*} (T : Ω → WithTop ℕ) (n : ℕ) :
    Set Ω :=
  {ω | (n : WithTop ℕ) < T ω}

/-- The unstopped martingale increment `X_{n+1} - X_n`. -/
def thm_13_17_rawIncrement {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X (n + 1) ω - X n ω

/-- The increment that remains after stopping: `(X_{n+1}-X_n) 1_{T>n}`. -/
def thm_13_17_stoppedIncrement {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) (n : ℕ) : Ω → ℝ :=
  (thm_13_17_activeEvent T n).indicator (thm_13_17_rawIncrement X n)

/-- For a stopping time, `{T > n}` is known at time `n`. -/
theorem thm_13_17_activeEvent_measurable {Ω : Type*}
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) (n : ℕ) :
    @MeasurableSet Ω (𝓕n n) (thm_13_17_activeEvent T n) := by
  have hle : @MeasurableSet Ω (𝓕n n) {ω | T ω ≤ (n : WithTop ℕ)} :=
    def_13_8_event_le_measurable hT n
  simpa [thm_13_17_activeEvent, Set.compl_setOf, not_le] using hle.compl

/-- At time zero the stopped process agrees with the original process. -/
theorem thm_13_17_stoppedProcess_zero {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) :
    def_13_9_stoppedProcess X T 0 = X 0 := by
  funext ω
  cases hTω : T ω with
  | top =>
      simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex, hTω]
  | coe k =>
      simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex, hTω]

/-- The textbook update identity
`X^T_{n+1} = X^T_n + (X_{n+1} - X_n) 1_{T>n}`. -/
theorem thm_13_17_stoppedProcess_succ_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) (n : ℕ) :
    def_13_9_stoppedProcess X T (n + 1) =
      def_13_9_stoppedProcess X T n + thm_13_17_stoppedIncrement X T n := by
  funext ω
  by_cases hactive : ω ∈ thm_13_17_activeEvent T n
  · cases hTω : T ω with
    | top =>
        simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex,
          thm_13_17_stoppedIncrement, thm_13_17_rawIncrement,
          thm_13_17_activeEvent, hTω, hactive]
    | coe k =>
        have hnkTop : (n : WithTop ℕ) < (k : WithTop ℕ) := by
          simpa [thm_13_17_activeEvent, hTω] using hactive
        have hnk : n < k := WithTop.coe_lt_coe.mp hnkTop
        have hmin_n : min k n = n := Nat.min_eq_right hnk.le
        have hmin_succ : min k (n + 1) = n + 1 :=
          Nat.min_eq_right (Nat.succ_le_of_lt hnk)
        simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex,
          thm_13_17_stoppedIncrement, hTω, hmin_n, hmin_succ]
        rw [Set.indicator_of_mem hactive]
        simp [thm_13_17_rawIncrement]
  · have hnot : ¬ (n : WithTop ℕ) < T ω := by
      simpa [thm_13_17_activeEvent] using hactive
    have hle : T ω ≤ (n : WithTop ℕ) := le_of_not_gt hnot
    cases hTω : T ω with
    | top =>
        simp [thm_13_17_activeEvent, hTω] at hactive
    | coe k =>
        have hkTop : (k : WithTop ℕ) ≤ (n : WithTop ℕ) := by
          simpa [hTω] using hle
        have hk : k ≤ n := WithTop.coe_le_coe.mp hkTop
        have hk_succ : k ≤ n + 1 := hk.trans (Nat.le_succ n)
        have hmin_n : min k n = k := Nat.min_eq_left hk
        have hmin_succ : min k (n + 1) = k := Nat.min_eq_left hk_succ
        simp [def_13_9_stoppedProcess, def_13_9_stoppedIndex,
          thm_13_17_stoppedIncrement, hTω, hmin_n, hmin_succ]
        intro hmem
        exact False.elim (hactive hmem)

theorem thm_13_17_rawIncrement_integrable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (n : ℕ) :
    Integrable (thm_13_17_rawIncrement X n) P :=
  (def_13_7_integrable hM (n + 1)).sub (def_13_7_integrable hM n)

/-- The martingale increment has conditional expectation zero. -/
theorem thm_13_17_rawIncrement_condExp_zero {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (n : ℕ) :
    P[thm_13_17_rawIncrement X n | 𝓕n n] =ᵐ[P] (0 : Ω → ℝ) := by
  have hself : P[X n | 𝓕n n] =ᵐ[P] X n :=
    thm_13_15_condExp_self hM hSigmaFinite n
  have hstep : P[X (n + 1) | 𝓕n n] =ᵐ[P] X n :=
    def_13_7_condExp_succ hM n
  calc
    P[thm_13_17_rawIncrement X n | 𝓕n n]
        =ᵐ[P] P[X (n + 1) | 𝓕n n] - P[X n | 𝓕n n] := by
          simpa [thm_13_17_rawIncrement] using
            condExp_sub (def_13_7_integrable hM (n + 1))
              (def_13_7_integrable hM n) (𝓕n n)
    _ =ᵐ[P] X n - X n := hstep.sub hself
    _ =ᵐ[P] (0 : Ω → ℝ) := by
      simp

theorem thm_13_17_stoppedIncrement_integrable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T) (n : ℕ) :
    Integrable (thm_13_17_stoppedIncrement X T n) P := by
  have hfiltration := def_13_7_isFiltration hM
  have hA_sub : @MeasurableSet Ω (𝓕n n) (thm_13_17_activeEvent T n) :=
    thm_13_17_activeEvent_measurable hT n
  have hA : MeasurableSet (thm_13_17_activeEvent T n) :=
    hfiltration.1 n _ hA_sub
  exact (thm_13_17_rawIncrement_integrable hM n).indicator hA

theorem thm_13_17_stoppedIncrement_measurable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {P : Measure Ω}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T) (n : ℕ) :
    @Measurable Ω ℝ (𝓕n (n + 1)) _ (thm_13_17_stoppedIncrement X T n) := by
  have hfiltration := def_13_7_isFiltration hM
  have hmono : 𝓕n n ≤ 𝓕n (n + 1) :=
    def_13_6_mono hfiltration (Nat.le_succ n)
  have hXn : @Measurable Ω ℝ (𝓕n (n + 1)) _ (X n) :=
    (def_13_7_adapted hM n).mono hmono le_rfl
  have hXsucc : @Measurable Ω ℝ (𝓕n (n + 1)) _ (X (n + 1)) :=
    def_13_7_adapted hM (n + 1)
  have hraw :
      @Measurable Ω ℝ (𝓕n (n + 1)) _ (thm_13_17_rawIncrement X n) := by
    simpa [thm_13_17_rawIncrement] using hXsucc.sub hXn
  have hA_sub : @MeasurableSet Ω (𝓕n n) (thm_13_17_activeEvent T n) :=
    thm_13_17_activeEvent_measurable hT n
  have hA : @MeasurableSet Ω (𝓕n (n + 1)) (thm_13_17_activeEvent T n) :=
    hmono _ hA_sub
  exact hraw.indicator hA

theorem thm_13_17_stoppedProcess_integrable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T) :
    ∀ n : ℕ, Integrable (def_13_9_stoppedProcess X T n) P := by
  intro n
  induction n with
  | zero =>
      rw [thm_13_17_stoppedProcess_zero]
      exact def_13_7_integrable hM 0
  | succ n ih =>
      rw [thm_13_17_stoppedProcess_succ_eq]
      exact ih.add (thm_13_17_stoppedIncrement_integrable hM hT n)

theorem thm_13_17_stoppedProcess_adapted {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T) :
    def_13_6_adapted 𝓕n (def_13_9_stoppedProcess X T) := by
  intro n
  induction n with
  | zero =>
      rw [thm_13_17_stoppedProcess_zero]
      exact def_13_7_adapted hM 0
  | succ n ih =>
      rw [thm_13_17_stoppedProcess_succ_eq]
      have hmono : 𝓕n n ≤ 𝓕n (n + 1) :=
        def_13_6_mono (def_13_7_isFiltration hM) (Nat.le_succ n)
      have hStopped : @Measurable Ω ℝ (𝓕n (n + 1)) _
          (def_13_9_stoppedProcess X T n) :=
        ih.mono hmono le_rfl
      exact hStopped.add (thm_13_17_stoppedIncrement_measurable hM hT n)

/-- The stopped increment has conditional expectation zero. -/
theorem thm_13_17_stoppedIncrement_condExp_zero {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (n : ℕ) :
    P[thm_13_17_stoppedIncrement X T n | 𝓕n n] =ᵐ[P] (0 : Ω → ℝ) := by
  have hA_sub : @MeasurableSet Ω (𝓕n n) (thm_13_17_activeEvent T n) :=
    thm_13_17_activeEvent_measurable hT n
  have hrawInt : Integrable (thm_13_17_rawIncrement X n) P :=
    thm_13_17_rawIncrement_integrable hM n
  have hpull :
      P[thm_13_17_stoppedIncrement X T n | 𝓕n n] =ᵐ[P]
        (thm_13_17_activeEvent T n).indicator
          (P[thm_13_17_rawIncrement X n | 𝓕n n]) := by
    simpa [thm_13_17_stoppedIncrement] using
      condExp_indicator (μ := P) (m := 𝓕n n)
        (s := thm_13_17_activeEvent T n) hrawInt hA_sub
  have hzero := thm_13_17_rawIncrement_condExp_zero hM hSigmaFinite n
  refine hpull.trans ?_
  filter_upwards [hzero] with ω hcond
  by_cases hmem : ω ∈ thm_13_17_activeEvent T n <;>
    simp [Set.indicator, hmem, hcond]

/-- The one-step condition for the stopped process. The integrability and
adaptedness hypotheses are the two concrete textbook obligations not yet
exported by `def_13_9`. -/
theorem thm_13_17_stopped_oneStepCondition {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    def_13_7_oneStepCondition P 𝓕n (def_13_9_stoppedProcess X T) := by
  intro n
  have hfiltration := def_13_7_isFiltration hM
  have hStoppedIntegrable :
      ∀ n : ℕ, Integrable (def_13_9_stoppedProcess X T n) P :=
    thm_13_17_stoppedProcess_integrable hM hT
  have hStoppedAdapted :
      def_13_6_adapted 𝓕n (def_13_9_stoppedProcess X T) :=
    thm_13_17_stoppedProcess_adapted hM hT
  have hIncInt : Integrable (thm_13_17_stoppedIncrement X T n) P :=
    thm_13_17_stoppedIncrement_integrable hM hT n
  have hself :
      P[def_13_9_stoppedProcess X T n | 𝓕n n] =ᵐ[P]
        def_13_9_stoppedProcess X T n := by
    haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
    have hcond :
        P[def_13_9_stoppedProcess X T n | 𝓕n n] =
          def_13_9_stoppedProcess X T n :=
      condExp_of_stronglyMeasurable (hfiltration.1 n)
        ((hStoppedAdapted n).stronglyMeasurable)
        (hStoppedIntegrable n)
    rw [hcond]
  have hzero :
      P[thm_13_17_stoppedIncrement X T n | 𝓕n n] =ᵐ[P] (0 : Ω → ℝ) :=
    thm_13_17_stoppedIncrement_condExp_zero hM hT hSigmaFinite n
  calc
    P[def_13_9_stoppedProcess X T (n + 1) | 𝓕n n]
        =ᵐ[P] P[def_13_9_stoppedProcess X T n +
          thm_13_17_stoppedIncrement X T n | 𝓕n n] := by
          rw [thm_13_17_stoppedProcess_succ_eq]
    _ =ᵐ[P]
        P[def_13_9_stoppedProcess X T n | 𝓕n n] +
          P[thm_13_17_stoppedIncrement X T n | 𝓕n n] :=
        condExp_add (hStoppedIntegrable n) hIncInt _
    _ =ᵐ[P] def_13_9_stoppedProcess X T n + (0 : Ω → ℝ) :=
        hself.add hzero
    _ =ᵐ[P] def_13_9_stoppedProcess X T n := by
        simp

/-- The stopped process is a martingale. -/
theorem thm_13_17_stopped_martingale {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    def_13_7 P 𝓕n (def_13_9_stoppedProcess X T) := by
  exact ⟨def_13_7_isFiltration hM,
    thm_13_17_stoppedProcess_integrable hM hT,
    thm_13_17_stoppedProcess_adapted hM hT,
    thm_13_17_stopped_oneStepCondition hM hT hSigmaFinite⟩

/-- The stopped process has the same expectation as `X_0` at every finite time. -/
theorem thm_13_17_expectation_constant {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    ∀ n : ℕ,
      ∫ ω, def_13_9_stoppedProcess X T n ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hStoppedM :
      def_13_7 P 𝓕n (def_13_9_stoppedProcess X T) :=
    thm_13_17_stopped_martingale hM hT hSigmaFinite
  have hStoppedSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hStoppedM).1 n)) := by
    intro n
    exact hSigmaFinite n
  intro n
  cases n with
  | zero =>
      rw [thm_13_17_stoppedProcess_zero]
  | succ n =>
      calc
        ∫ ω, def_13_9_stoppedProcess X T (n + 1) ω ∂P =
            ∫ ω, def_13_9_stoppedProcess X T 0 ω ∂P :=
          thm_13_16 hStoppedM hStoppedSigmaFinite (n + 1) (Nat.succ_pos n)
        _ = ∫ ω, X 0 ω ∂P := by
          rw [thm_13_17_stoppedProcess_zero]

/-- Theorem 13.17: the stopped process is a martingale and its finite-time
expectations remain equal to the initial expectation. -/
theorem thm_13_17 {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    def_13_7 P 𝓕n (def_13_9_stoppedProcess X T) ∧
      ∀ n : ℕ,
        ∫ ω, def_13_9_stoppedProcess X T n ω ∂P = ∫ ω, X 0 ω ∂P := by
  exact ⟨thm_13_17_stopped_martingale hM hT hSigmaFinite,
    thm_13_17_expectation_constant hM hT hSigmaFinite⟩
