import ToyApollo.Output.def_4_1
import Mathlib

open MeasureTheory

inductive Omega : Type
  | a | b | c | d | e
  deriving Fintype, DecidableEq

instance : MeasurableSpace Omega := ⊤
instance : MeasurableSingletonClass Omega := ⟨fun _ => trivial⟩

/-- A uniform law on the five-point sample space from the source example. -/
noncomputable def exP : Measure Omega := (1 / 5 : ENNReal) • Measure.count

/-- The random variable `X` is a lookup table from outcomes to real values. -/
noncomputable def exX : Omega → ℝ
  | Omega.a => 1
  | Omega.b => 2
  | Omega.c => 3
  | Omega.d => 4
  | Omega.e => 5

/-- The random variable `Y` is another lookup table on the same sample space. -/
noncomputable def exY : Omega → ℝ
  | Omega.a => 0
  | Omega.b => 3
  | Omega.c => 2
  | Omega.d => -1
  | Omega.e => 5

/-- Reading the two dictionaries at a sampled outcome returns the realized pair `(X(ω), Y(ω))`. -/
def lookupPair : Omega → ℝ × ℝ
  | Omega.a => (1, 0)
  | Omega.b => (2, 3)
  | Omega.c => (3, 2)
  | Omega.d => (4, -1)
  | Omega.e => (5, 5)

/--
Example 4.1.2: on a finite sample space, a random variable can be viewed as a predefined
lookup function from outcomes to numerical values. Once `ω` is sampled, the values of `X`
and `Y` are determined by reading the corresponding entries in the tables.
-/
theorem ex_4_1_2 :
    IsRealMeasurable exX ∧
      IsRealMeasurable exY ∧
      ∀ ω : Omega, (exX ω, exY ω) = lookupPair ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    trivial
  · intro B hB
    trivial
  · intro ω
    cases ω <;> rfl
