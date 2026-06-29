import Mathlib
import ToyApollo.Output.def_2_3
import ToyApollo.Output.def_12_2

/-
TASK ID: def_13_3
TYPE: Definition
SOURCE PLAN: chapter13-sub-sigma-algebra
TASK CONTENT:
\begin{defbox}{13.3}
\end{defbox}

Let X be a real-valued P -integrable random variable and \mathcal{G}is a sub-\sigma-algebra

of \mathcal{F}The conditional expectation of X given \mathcal{G}, denoted by E[X\vert\mathcal{G}],i sa \mathcal{G}-

measurable random variable that satisfies

\int

B

E[X\vert\mathcal{G}] dP =

\int

B

XdP for all B \in\mathcal{G}. (13.3)

The condition in (13.3) can be written in two equivalent forms. These forms

provide alternative ways to think about the definition of E[X\vert\mathcal{G}].

(i)

\int

\Omega

E[X\vert\mathcal{G}]\cdot 1B dP =

\int

\Omega

X \cdot 1B dP for all B \in\mathcal{G}; (13.4)

(ii)

\int

\Omega

E[X\vert\mathcal{G}]\cdot ZdP =

\int

\Omega

X\cdot ZdP (13.5)

for all bounded \mathcal{G}-measurable random variables Z .

It is obvious that condition (ii) in (13.5) implies condition (i) in (13.4) because

the indicator function . 1B for any B\in \mathcal{G} is \mathcal{G}-measurable. To show the reverse

direction, we can proceed with the sequence of indicator functions, simple functions,

and bounded functions that are \mathcal{G}-measurable.

Comparing condition (ii) in (13.5) with the version of Orthogonal Principle

in (12.5), we see that when X is square integrable, the conditional expectation of

X given a sub-\sigma-algebra \mathcal{G}is the same as the projection of X on the space of \mathcal{G}-

measurable functions with finite second moments. Roughly speaking, for random

variables in L2(P) , the conditional expectation is just a minimum mean-squared

error (MMSE) estimator. A more precise statement is given in the next theorem.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- Integrability with respect to the ambient sigma-field `𝓕`. This avoids
accidentally asking Lean to type a measure through the sub-sigma-field `𝓖`. -/
def AmbientIntegrable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Integrable X P

/-- A real-valued function measurable with respect to the sub-sigma-field
`𝓖`. -/
def GMeasurable {Ω : Type*} (𝓖 : SigmaField Ω) (Y : Ω → ℝ) : Prop :=
  Measurable[𝓖] Y

/-- The bounded `𝓖`-measurable test random variables used in the equivalent
form (13.5). -/
def BoundedGMeasurable {Ω : Type*} (𝓖 : SigmaField Ω) (Z : Ω → ℝ) : Prop :=
  GMeasurable 𝓖 Z ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, |Z ω| ≤ C

/-- Definition 13.3 in its set-integral form: `Y` is a conditional expectation
of `X` given `𝓖` when it is `𝓖`-measurable and has the same integral as `X`
over every `𝓖`-measurable set. -/
def ConditionalExpectationSetFormula {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (X Y : Ω → ℝ) : Prop :=
  @AmbientIntegrable Ω 𝓕 P X ∧
    @AmbientIntegrable Ω 𝓕 P Y ∧
      GMeasurable 𝓖 Y ∧
        ∀ ⦃B : Set Ω⦄, IsMeasurableIn 𝓖 B →
          ∫ ω in B, Y ω ∂P = ∫ ω in B, X ω ∂P

/-- Equivalent indicator-function form (13.4). -/
def ConditionalExpectationIndicatorFormula {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (X Y : Ω → ℝ) : Prop :=
  @AmbientIntegrable Ω 𝓕 P X ∧
    @AmbientIntegrable Ω 𝓕 P Y ∧
      GMeasurable 𝓖 Y ∧
        ∀ ⦃B : Set Ω⦄, IsMeasurableIn 𝓖 B →
          ∫ ω, Y ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P =
            ∫ ω, X ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P

/-- Equivalent bounded-test-function form (13.5). -/
def ConditionalExpectationTestFunctionFormula {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (X Y : Ω → ℝ) : Prop :=
  @AmbientIntegrable Ω 𝓕 P X ∧
    @AmbientIntegrable Ω 𝓕 P Y ∧
      GMeasurable 𝓖 Y ∧
        ∀ Z : Ω → ℝ, BoundedGMeasurable 𝓖 Z →
          ∫ ω, Y ω * Z ω ∂P = ∫ ω, X ω * Z ω ∂P

/-- The `L²` orthogonality reading cited after (13.5): for square-integrable
variables, the conditional expectation has the same inner products against all
square-integrable `𝓖`-measurable test variables. -/
def ConditionalExpectationL2ProjectionFormula {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (X Y : Ω → ℝ) : Prop :=
  ∃ hX : @L2Function Ω 𝓕 P X, ∃ hY : @L2Function Ω 𝓕 P Y,
    GMeasurable 𝓖 Y ∧
      ∀ Z : Ω → ℝ, GMeasurable 𝓖 Z → ∀ hZ : @L2Function Ω 𝓕 P Z,
        @l2Inner Ω 𝓕 P Y Z hY hZ = @l2Inner Ω 𝓕 P X Z hX hZ

theorem ConditionalExpectationSetFormula.to_indicator {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {X Y : Ω → ℝ}
    (h : @ConditionalExpectationSetFormula Ω 𝓕 P 𝓖 X Y) :
    @ConditionalExpectationIndicatorFormula Ω 𝓕 P 𝓖 X Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro B hB
  have hBF : @MeasurableSet Ω 𝓕 B := h𝓖 hB
  have hYindicator :
      (fun ω => Y ω * B.indicator (fun _ => (1 : ℝ)) ω) = B.indicator Y := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator, hω]
  have hXindicator :
      (fun ω => X ω * B.indicator (fun _ => (1 : ℝ)) ω) = B.indicator X := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator, hω]
  rw [hYindicator, hXindicator, integral_indicator hBF, integral_indicator hBF]
  exact h.2.2.2 hB

theorem ConditionalExpectationIndicatorFormula.to_set {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {X Y : Ω → ℝ}
    (h : @ConditionalExpectationIndicatorFormula Ω 𝓕 P 𝓖 X Y) :
    @ConditionalExpectationSetFormula Ω 𝓕 P 𝓖 X Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro B hB
  have hBF : @MeasurableSet Ω 𝓕 B := h𝓖 hB
  have hYindicator :
      (fun ω => Y ω * B.indicator (fun _ => (1 : ℝ)) ω) = B.indicator Y := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator, hω]
  have hXindicator :
      (fun ω => X ω * B.indicator (fun _ => (1 : ℝ)) ω) = B.indicator X := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator, hω]
  rw [← integral_indicator hBF, ← integral_indicator hBF, ← hYindicator, ← hXindicator]
  exact h.2.2.2 hB

theorem ConditionalExpectationTestFunctionFormula.to_indicator {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω}
    {X Y : Ω → ℝ}
    (h : @ConditionalExpectationTestFunctionFormula Ω 𝓕 P 𝓖 X Y) :
    @ConditionalExpectationIndicatorFormula Ω 𝓕 P 𝓖 X Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro B hB
  have hZ : BoundedGMeasurable 𝓖 (B.indicator (fun _ => (1 : ℝ))) := by
    refine ⟨measurable_const.indicator hB, ⟨1, by norm_num, ?_⟩⟩
    intro ω
    by_cases hω : ω ∈ B <;> simp [Set.indicator, hω]
  exact h.2.2.2 (B.indicator (fun _ => (1 : ℝ))) hZ

/-- The reverse direction sketched after (13.5): the setwise conditional
expectation condition implies equality against every bounded `𝓖`-measurable
test function. The proof uses Mathlib's uniqueness theorem for conditional
expectation and its pull-out property, which packages the standard
indicator/simple/bounded approximation route. -/
theorem ConditionalExpectationSetFormula.to_test {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [hσ : SigmaFinite (P.trim (show 𝓖 ≤ 𝓕 from fun _ hA => h𝓖 hA))]
    {X Y : Ω → ℝ}
    (h : @ConditionalExpectationSetFormula Ω 𝓕 P 𝓖 X Y) :
    @ConditionalExpectationTestFunctionFormula Ω 𝓕 P 𝓖 X Y := by
  let hm : 𝓖 ≤ 𝓕 := fun _ hA => h𝓖 hA
  haveI : SigmaFinite (P.trim hm) := hσ
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro Z hZ
  obtain ⟨C, _hC, hZ_bound_abs⟩ := hZ.2
  have hZ_bound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C := by
    exact ae_of_all P fun ω => by
      simpa [Real.norm_eq_abs] using hZ_bound_abs ω
  have hZ_meas_ambient : Measurable[𝓕] Z :=
    hZ.1.mono hm le_rfl
  have hZ_aesm_ambient : AEStronglyMeasurable[𝓕] Z P :=
    hZ_meas_ambient.aestronglyMeasurable
  have hXZ_int : Integrable (fun ω => X ω * Z ω) P :=
    h.1.mul_bdd hZ_aesm_ambient hZ_bound
  have hY_ae_cond : Y =ᵐ[P] P[X | 𝓖] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm h.1 ?_ ?_ ?_
    · intro s _hs _hfin
      exact h.2.1.integrableOn
    · intro s hs _hfin
      exact h.2.2.2 hs
    · exact h.2.2.1.aestronglyMeasurable
  have hY_to_cond :
      ∫ ω, Y ω * Z ω ∂P = ∫ ω, P[X | 𝓖] ω * Z ω ∂P := by
    apply integral_congr_ae
    filter_upwards [hY_ae_cond] with ω hω
    simp [hω]
  have hPull :
      P[fun ω => X ω * Z ω | 𝓖] =ᵐ[P] fun ω => P[X | 𝓖] ω * Z ω :=
    condExp_mul_of_stronglyMeasurable_right
      (show StronglyMeasurable[𝓖] Z from hZ.1.stronglyMeasurable) hXZ_int h.1
  calc
    ∫ ω, Y ω * Z ω ∂P = ∫ ω, P[X | 𝓖] ω * Z ω ∂P := hY_to_cond
    _ = ∫ ω, P[fun ω => X ω * Z ω | 𝓖] ω ∂P := by
      exact (integral_congr_ae hPull).symm
    _ = ∫ ω, X ω * Z ω ∂P := integral_condExp hm

theorem ConditionalExpectationIndicatorFormula.to_test {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    [SigmaFinite (P.trim (show 𝓖 ≤ 𝓕 from fun _ hA => h𝓖 hA))]
    {X Y : Ω → ℝ}
    (h : @ConditionalExpectationIndicatorFormula Ω 𝓕 P 𝓖 X Y) :
    @ConditionalExpectationTestFunctionFormula Ω 𝓕 P 𝓖 X Y :=
  @ConditionalExpectationSetFormula.to_test Ω 𝓕 P 𝓖 h𝓖 inferInstance X Y
    (@ConditionalExpectationIndicatorFormula.to_set Ω 𝓕 P 𝓖 h𝓖 X Y h)

/-- Exported Definition 13.3: `Y` is a version of `E[X | 𝓖]`. The sub-sigma
field hypothesis records that `𝓖` sits inside the ambient sigma-field
`𝓕 = inferInstance`. -/
def def_13_3 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω)
    (_h𝓖 : IsSubSigmaField 𝓖 𝓕)
    (X Y : Ω → ℝ) : Prop :=
  @ConditionalExpectationSetFormula Ω 𝓕 P 𝓖 X Y

theorem def_13_3_integrable_original {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {X Y : Ω → ℝ} (h : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y) :
    @AmbientIntegrable Ω 𝓕 P X :=
  h.1

theorem def_13_3_integrable_version {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {X Y : Ω → ℝ} (h : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y) :
    @AmbientIntegrable Ω 𝓕 P Y :=
  h.2.1

theorem def_13_3_measurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {X Y : Ω → ℝ} (h : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y) :
    GMeasurable 𝓖 Y :=
  h.2.2.1

theorem def_13_3_set_integral_eq {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {X Y : Ω → ℝ} (h : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y)
    {B : Set Ω} (hB : IsMeasurableIn 𝓖 B) :
    ∫ ω in B, Y ω ∂P = ∫ ω in B, X ω ∂P :=
  h.2.2.2 hB
