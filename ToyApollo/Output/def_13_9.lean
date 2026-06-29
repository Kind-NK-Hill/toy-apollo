import Mathlib
import ToyApollo.Output.def_13_8

/-
TASK ID: def_13_9
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{defbox}{13.9}
\end{defbox}

Given a martingale .(Xn)n\geq0 and a stopping time T ,a stopped process . (XT

n )n\geq0

is obtained from .(Xn)n\geq0 by forcing the values with indices larger than T to be

XT That is, XT

n () \coloneqqXT n().

For allm \geq T , the random variable. XT

m stops updating and is equal to XT In the

definition, we used the notation a b \coloneqqmin(a, b).
-/

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

/-- The finite time `T ∧ n` from Definition 13.9.  If `T = ∞`, then
`T ∧ n = n`; if `T = k`, then `T ∧ n = min k n`. -/
def def_13_9_stoppedIndex {Ω : Type*}
    (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) : ℕ :=
  match T ω with
  | none => n
  | some k => min k n

/-- Definition 13.9: the stopped process obtained from `X` by freezing it
after the stopping time `T`; the nth stopped value is `X_{T ∧ n}`. -/
def def_13_9_stoppedProcess {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) : ℕ → Ω → S :=
  fun n ω => X (def_13_9_stoppedIndex T n ω) ω

/-- Exported Definition 13.9: `Y` is the stopped process associated with
`X` and `T`. -/
def def_13_9 {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (Y : ℕ → Ω → S) : Prop :=
  Y = def_13_9_stoppedProcess X T

/-- Definition 13.9 with the source-side stopping-time hypothesis retained. -/
def def_13_9_ofStoppingTime {Ω S : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → S)
    (T : Ω → WithTop ℕ) (Y : ℕ → Ω → S) : Prop :=
  def_13_8 𝓕n T ∧ Y = def_13_9_stoppedProcess X T

theorem def_13_9_ofStoppingTime_stoppingTime {Ω S : Type*}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → S}
    {T : Ω → WithTop ℕ} {Y : ℕ → Ω → S}
    (h : def_13_9_ofStoppingTime 𝓕n X T Y) :
    def_13_8 𝓕n T :=
  h.1

theorem def_13_9_ofStoppingTime_process {Ω S : Type*}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → S}
    {T : Ω → WithTop ℕ} {Y : ℕ → Ω → S}
    (h : def_13_9_ofStoppingTime 𝓕n X T Y) :
    Y = def_13_9_stoppedProcess X T :=
  h.2

theorem def_13_9_apply {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) :
    def_13_9_stoppedProcess X T n ω =
      X (def_13_9_stoppedIndex T n ω) ω :=
  rfl

theorem def_13_9_stoppedIndex_top {Ω : Type*}
    (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) (hT : T ω = ⊤) :
    def_13_9_stoppedIndex T n ω = n := by
  simp [def_13_9_stoppedIndex, hT]

theorem def_13_9_stoppedIndex_after_stop {Ω : Type*}
    (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    def_13_9_stoppedIndex T n ω = k := by
  simp [def_13_9_stoppedIndex, hT, Nat.min_eq_left hkn]

theorem def_13_9_stoppedProcess_after_stop {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    def_13_9_stoppedProcess X T n ω = X k ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_after_stop T n k ω hT hkn]

theorem def_13_9_stoppedProcess_top {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω)
    (hT : T ω = ⊤) :
    def_13_9_stoppedProcess X T n ω = X n ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_top T n ω hT]

theorem def_13_9_matches_stoppedValue_after_stop {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    some (def_13_9_stoppedProcess X T n ω) =
      def_13_8_stoppedValue X T ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_after_stop T n k ω hT hkn,
    def_13_8_stoppedValue, hT]
