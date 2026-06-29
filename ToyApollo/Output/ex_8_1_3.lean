import Mathlib
import ToyApollo.Output.def_8_1
import ToyApollo.Output.def_8_2

/-
TASK ID: ex_8_1_3
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
TASK CONTENT:
\textbf{Example 8.1.3 (Deterministic Coupling of Two Continuous Random Variables)} \\
Suppose $\tilde{X}_1$ and $\tilde{X}_2$ are real-valued random variables with cdf $F_1(x)$ and $F_2(x)$, respectively. Furthermore, suppose that the two functions $F_1(x)$ and $F_2(x)$ are monotonically increasing functions from 0 to 1. For simplicity, suppose that the inverse functions of $F_1$ and $F_2$ exist. We can construct a coupling between $\tilde{X}_1$ and $\tilde{X}_2$ by defining $X_1=F_1^{-1}(U)$ and $X_2=F_2^{-1}(U)$, respectively, where $U$ is a uniform random variable distributed between 0 and 1. (This is a preliminary idea of the Skorohod representation theorem (Theorem 10.8).)

In what follows we investigate how to relate two couplings. Let $(\Omega,\mathcal{H},\mu)$ and $(\Omega',\mathcal{H}',\mu')$ be couplings of probability measures $P$ and $Q$, defined on the sample spaces $\mathcal{X}$ and $\mathcal{Y}$, respectively. We say that a measurable function $g:\Omega\to \Omega'$ is a \textit{morphism} from the coupling on $\Omega$ to the coupling on $\Omega'$ if it satisfies the following commutative diagram:
\[
\Omega
\]
\[
\downarrow g
\]
\[
\Omega'
\]
\[
\swarrow X' \qquad \searrow Y'
\]
\[
\mathcal{X} \qquad \qquad \mathcal{Y}
\]
with the outer arrows given by $X$ and $Y$. That is, we have $X=X'\circ g$ and $Y=Y'\circ g$. The measure $\mu'$ on $\Omega'$ is related to $\mu$ in $\Omega$ through the relation $\mu'(E')=\mu(g^{-1}(E'))$, which holds for all $E'\in \mathcal{H}'$.

Using this notion of morphism, we can define the concept of \textit{equivalent couplings}. Two couplings $(\Omega,\mathcal{H},\mu)$ and $(\Omega',\mathcal{H}',\mu')$ are said to be equivalent if there exist two morphisms, $g$ from the first coupling to the second and $g'$ from the second to the first, that are inverses of each other up to a null set, meaning that the compositions $g'\circ g$ and $g\circ g'$ are equal to the identity map almost everywhere. To be precise, this means that for all $E\in \mathcal{H}$, we have $g'(g(E))\Delta E = N$ and for all $E'\in \mathcal{H}'$, we have $g(g'(E'))\Delta E' = N'$, where $N$ and $N'$ are null sets in $\mathcal{H}$ and $\mathcal{H}'$, respectively, and $\Delta$ is the symmetric difference operator in set theory.

Suppose we have two separate sample spaces $\mathcal{X}$ and $\mathcal{Y}$. We want to turn the Cartesian product $\mathcal{X}\times \mathcal{Y}$ into a measurable space by selecting a $\sigma$-algebra on $\mathcal{X}\times \mathcal{Y}$. There are many ways to do this, but we are interested in the one that makes the two projection functions $\pi_1(x,y)=x$ from $\mathcal{X}\times \mathcal{Y}$ to $\mathcal{X}$ and the projection $\pi_2(x,y)=y$ from $\mathcal{X}\times \mathcal{Y}$ to $\mathcal{Y}$ measurable. Specifically, we want the inverse image $\pi_1^{-1}(E_1)=E_1\times \mathcal{Y}$ to be measurable for all $E_1\in \mathcal{F}$ and the inverse image $\pi_2^{-1}(E_2)=\mathcal{X}\times E_2$ to be measurable for all $E_2\in \mathcal{G}$.

This motivates the definition of measurable rectangles.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The uniform probability measure on the unit interval `[0,1]`, realized as Lebesgue measure
restricted to `Icc 0 1`. -/
noncomputable def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

noncomputable instance : IsProbabilityMeasure unitIntervalMeasure := by
  refine ⟨?_⟩
  simp [unitIntervalMeasure, Real.volume_Icc]

/-- Push-forward of the unit-interval uniform law along a measurable map is again a probability
measure. -/
noncomputable abbrev mapUnitIntervalIsProbabilityMeasure
    (f : ℝ → ℝ) (hf : Measurable f) :
    IsProbabilityMeasure (Measure.map f unitIntervalMeasure) := by
  refine ⟨?_⟩
  rw [Measure.map_apply hf MeasurableSet.univ]
  simpa using (IsProbabilityMeasure.measure_univ (μ := unitIntervalMeasure))

/-- The coupling obtained by applying two inverse-cdf-type maps to the same uniform random
variable on `[0,1]`. -/
noncomputable abbrev inverseCDFCoupling
    (F₁Inv F₂Inv : ℝ → ℝ)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    Coupling P Q := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  exact
    { Ω := ℝ
      instMeasurableSpaceΩ := inferInstance
      μ := unitIntervalMeasure
      instIsProbabilityMeasureμ := inferInstance
      X := F₁Inv
      Y := F₂Inv
      measurable_X := hF₁Inv_meas
      measurable_Y := hF₂Inv_meas
      map_X := rfl
      map_Y := rfl }

/-- A morphism between two couplings of the same marginals is a measurable map between the common
probability spaces that commutes with both coordinate maps and pushes one source measure to the
other. -/
structure CouplingMorphism
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  toFun : π.Ω → π'.Ω
  measurable_toFun : Measurable toFun
  comm_X : π.X = π'.X ∘ toFun
  comm_Y : π.Y = π'.Y ∘ toFun
  map_μ : Measure.map toFun π.μ = π'.μ

/-- Two couplings are equivalent when they admit morphisms in both directions whose compositions
agree almost everywhere with the respective identity maps. -/
structure EquivalentCouplings
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  forward : CouplingMorphism π π'
  backward : CouplingMorphism π' π
  left_inv_ae : ∀ᵐ ω ∂π.μ, backward.toFun (forward.toFun ω) = ω
  right_inv_ae : ∀ᵐ ω' ∂π'.μ, forward.toFun (backward.toFun ω') = ω'

/-- When `F₁Inv` is a right inverse of the cdf `F₁` on `[0,1]`, the common-uniform coupling can be
re-expressed as a deterministic coupling with transport map `F₂Inv ∘ F₁`. -/
noncomputable abbrev inverseCDFDeterministicCoupling
    (F₁ F₁Inv F₂Inv : ℝ → ℝ)
    (hF₁_meas : Measurable F₁)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv)
    (hRightInv₁ : ∀ u ∈ Icc (0 : ℝ) 1, F₁ (F₁Inv u) = u) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    DeterministicCoupling P Q := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  exact
  { toCoupling :=
      { Ω := ℝ
        instMeasurableSpaceΩ := inferInstance
        μ := Measure.map F₁Inv unitIntervalMeasure
        instIsProbabilityMeasureμ := inferInstance
        X := id
        Y := F₂Inv ∘ F₁
        measurable_X := measurable_id
        measurable_Y := hF₂Inv_meas.comp hF₁_meas
        map_X := Measure.map_id
        map_Y := by
          have hAe :
              (F₁ ∘ F₁Inv) =ᵐ[unitIntervalMeasure] id := by
            refine (ae_restrict_iff' measurableSet_Icc).2 ?_
            filter_upwards with u hu
            exact hRightInv₁ u hu
          have hAeComp :
              (fun u => F₂Inv (F₁ (F₁Inv u))) =ᵐ[unitIntervalMeasure] F₂Inv := by
            simpa [Function.comp] using hAe.fun_comp F₂Inv
          calc
            Measure.map (F₂Inv ∘ F₁) (Measure.map F₁Inv unitIntervalMeasure)
                = Measure.map (fun u => F₂Inv (F₁ (F₁Inv u))) unitIntervalMeasure := by
                    simpa [Function.comp] using
                      (Measure.map_map (g := F₂Inv ∘ F₁) (f := F₁Inv)
                        (μ := unitIntervalMeasure) (hg := hF₂Inv_meas.comp hF₁_meas)
                        (hf := hF₁Inv_meas))
            _ = Measure.map F₂Inv unitIntervalMeasure := Measure.map_congr hAeComp
      }
    T := F₂Inv ∘ F₁
    measurable_T := hF₂Inv_meas.comp hF₁_meas
    Y_eq_transport := by
      ext x
      rfl }

/-- Example 8.1.3: inverse-cdf maps applied to a common uniform random variable on `[0,1]`
produce a coupling, and when the first inverse really inverts a cdf `F₁`, this same
construction yields a deterministic transport `F₂Inv ∘ F₁` between the two induced laws. -/
theorem ex_8_1_3
    {F₁ F₁Inv F₂Inv : ℝ → ℝ}
    (hF₁_meas : Measurable F₁)
    (hF₁Inv_meas : Measurable F₁Inv)
    (hF₂Inv_meas : Measurable F₂Inv)
    (hRightInv₁ : ∀ u ∈ Icc (0 : ℝ) 1, F₁ (F₁Inv u) = u) :
    let P := Measure.map F₁Inv unitIntervalMeasure
    let Q := Measure.map F₂Inv unitIntervalMeasure
    letI : IsProbabilityMeasure P := mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
    letI : IsProbabilityMeasure Q := mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
    ∃ δ : DeterministicCoupling.{0, 0, 0} P Q, δ.T = F₂Inv ∘ F₁ := by
  dsimp
  letI : IsProbabilityMeasure (Measure.map F₁Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₁Inv hF₁Inv_meas
  letI : IsProbabilityMeasure (Measure.map F₂Inv unitIntervalMeasure) :=
    mapUnitIntervalIsProbabilityMeasure F₂Inv hF₂Inv_meas
  let δ :
      DeterministicCoupling.{0, 0, 0}
        (Measure.map F₁Inv unitIntervalMeasure)
        (Measure.map F₂Inv unitIntervalMeasure) := by
    simpa using
      inverseCDFDeterministicCoupling F₁ F₁Inv F₂Inv hF₁_meas hF₁Inv_meas hF₂Inv_meas hRightInv₁
  exact ⟨δ, rfl⟩
