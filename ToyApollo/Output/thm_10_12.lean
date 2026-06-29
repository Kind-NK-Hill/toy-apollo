import Mathlib
import ToyApollo.Output.thm_10_11
import ToyApollo.Output.thm_10_10
import ToyApollo.Output.thm_4_6
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2

/-
TASK ID: thm_10_12
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-continuous-mapping
TASK CONTENT:
\begin{thmbox}{10.12}
\begin{enumerate}
\item Suppose $X_n\xrightarrow{\mathrm{a.s.}}X$ and $Y_n\xrightarrow{\mathrm{a.s.}}Y$. Then:
\begin{enumerate}
\item $X_n+Y_n\xrightarrow{\mathrm{a.s.}}X+Y$.
\item $X_nY_n\xrightarrow{\mathrm{a.s.}}XY$.
\item $\alpha X_n\xrightarrow{\mathrm{a.s.}}\alpha X$ for any constant $\alpha$.
\item $X_n/Y_n\xrightarrow{\mathrm{a.s.}}X/Y$ provided that $Y_n$ and $Y$ are nonzero with probability $1$.
\end{enumerate}
\item If $X_n\xrightarrow{P}X$ and $Y_n\xrightarrow{P}Y$, then (a) to (d) above hold with ``a.s.'' replaced by ``$P$''.
\end{enumerate}
\end{thmbox}

\textit{Proof}
We prove part (a) for convergence in probability only. The proofs of the others are similar. Since $X_n$ and $Y_n$ are both converging to $X$ and $Y$, respectively, in probability, the random vector $(X_n,Y_n)$ converges to the random vector $(X,Y)$ in probability. We apply Theorem 10.11 with the continuous function $f(x,y)=x+y$ (cf. the proof of Theorem 4.6).
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

/-- Encode two scalar random variables as the two coordinates of a random
vector. -/
def thm_10_12_pair (x y : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then x else y

/-- Encode one scalar random variable as a one-dimensional random vector. -/
def thm_10_12_one (x : ℝ) : Fin 1 → ℝ :=
  fun _ => x

def thm_10_12_addMap (v : Fin 2 → ℝ) : Fin 1 → ℝ :=
  thm_10_12_one (v 0 + v 1)

def thm_10_12_mulMap (v : Fin 2 → ℝ) : Fin 1 → ℝ :=
  thm_10_12_one (v 0 * v 1)

noncomputable def thm_10_12_divMap (v : Fin 2 → ℝ) : Fin 1 → ℝ :=
  thm_10_12_one (v 0 / v 1)

def thm_10_12_constMulMap (α : ℝ) (v : Fin 1 → ℝ) : Fin 1 → ℝ :=
  thm_10_12_one (α * v 0)

theorem thm_10_12_addMap_continuousAt (v : Fin 2 → ℝ) :
    ContinuousAt thm_10_12_addMap v := by
  unfold thm_10_12_addMap thm_10_12_one
  fun_prop

theorem thm_10_12_mulMap_continuousAt (v : Fin 2 → ℝ) :
    ContinuousAt thm_10_12_mulMap v := by
  unfold thm_10_12_mulMap thm_10_12_one
  fun_prop

theorem thm_10_12_divMap_continuousAt {v : Fin 2 → ℝ} (hv : v 1 ≠ 0) :
    ContinuousAt thm_10_12_divMap v := by
  rw [continuousAt_pi]
  intro i
  fin_cases i
  simpa [thm_10_12_divMap, thm_10_12_one] using
    ((continuousAt_apply (0 : Fin 2) v).div (continuousAt_apply (1 : Fin 2) v) hv)

theorem thm_10_12_constMulMap_continuousAt (α : ℝ) (v : Fin 1 → ℝ) :
    ContinuousAt (thm_10_12_constMulMap α) v := by
  rw [continuousAt_pi]
  intro i
  fin_cases i
  simpa [thm_10_12_constMulMap, thm_10_12_one] using
    ((continuousAt_apply (0 : Fin 1) v).const_mul α)

theorem thm_10_12_almost_sure_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : ConvergesAlmostSurely μ Xn X) (hY : ConvergesAlmostSurely μ Yn Y) :
    ConvergesAlmostSurely μ
      (fun n ω => Xn n ω + Yn n ω) (fun ω => X ω + Y ω) := by
  filter_upwards [hX, hY] with ω hXω hYω
  exact hXω.add hYω

theorem thm_10_12_almost_sure_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : ConvergesAlmostSurely μ Xn X) (hY : ConvergesAlmostSurely μ Yn Y) :
    ConvergesAlmostSurely μ
      (fun n ω => Xn n ω * Yn n ω) (fun ω => X ω * Y ω) := by
  filter_upwards [hX, hY] with ω hXω hYω
  exact hXω.mul hYω

theorem thm_10_12_almost_sure_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (α : ℝ) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hX : ConvergesAlmostSurely μ Xn X) :
    ConvergesAlmostSurely μ (fun n ω => α * Xn n ω) (fun ω => α * X ω) := by
  filter_upwards [hX] with ω hXω
  exact hXω.const_mul α

theorem thm_10_12_almost_sure_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : ConvergesAlmostSurely μ Xn X) (hY : ConvergesAlmostSurely μ Yn Y)
    (_hYn_ne : ∀ n : ℕ, ∀ᵐ ω ∂μ, Yn n ω ≠ 0)
    (hY_ne : ∀ᵐ ω ∂μ, Y ω ≠ 0) :
    ConvergesAlmostSurely μ
      (fun n ω => Xn n ω / Yn n ω) (fun ω => X ω / Y ω) := by
  filter_upwards [hX, hY, hY_ne] with ω hXω hYω hYω_ne
  exact hXω.div hYω hYω_ne

theorem thm_10_12_pair_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hX : ConvergesInProbability μ Xn X) (hY : ConvergesInProbability μ Yn Y) :
    VectorConvergesInProbability μ
      (fun n ω => thm_10_12_pair (Xn n ω) (Yn n ω))
      (fun ω => thm_10_12_pair (X ω) (Y ω)) := by
  apply thm_10_10_component_prob_to_vector μ
  intro i
  fin_cases i
  · simpa [thm_10_12_pair] using hX
  · simpa [thm_10_12_pair] using hY

theorem thm_10_12_one_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hX : ConvergesInProbability μ Xn X) :
    VectorConvergesInProbability μ
      (fun n ω => thm_10_12_one (Xn n ω)) (fun ω => thm_10_12_one (X ω)) := by
  apply thm_10_10_component_prob_to_vector μ
  intro i
  fin_cases i
  simpa [thm_10_12_one] using hX

theorem thm_10_12_probability_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hPair_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_pair (Xn n ω) (Yn n ω)) μ)
    (hAdd_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_addMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hX : ConvergesInProbability μ Xn X) (hY : ConvergesInProbability μ Yn Y) :
    ConvergesInProbability μ
      (fun n ω => Xn n ω + Yn n ω) (fun ω => X ω + Y ω) := by
  have hvec :=
    thm_10_11_probability μ
      (fun n ω => thm_10_12_pair (Xn n ω) (Yn n ω))
      (fun ω => thm_10_12_pair (X ω) (Y ω))
      thm_10_12_addMap Set.univ hPair_meas hAdd_meas
      (by simp) (by simp)
      (fun v _ => thm_10_12_addMap_continuousAt v)
      (thm_10_12_pair_probability μ Xn Yn X Y hX hY)
  have hcomp := (thm_10_10_probability_iff μ
    (fun n ω => thm_10_12_addMap (thm_10_12_pair (Xn n ω) (Yn n ω)))
    (fun ω => thm_10_12_addMap (thm_10_12_pair (X ω) (Y ω)))).mp hvec 0
  simpa [thm_10_12_addMap, thm_10_12_one, thm_10_12_pair] using hcomp

theorem thm_10_12_probability_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hPair_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_pair (Xn n ω) (Yn n ω)) μ)
    (hMul_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_mulMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hX : ConvergesInProbability μ Xn X) (hY : ConvergesInProbability μ Yn Y) :
    ConvergesInProbability μ
      (fun n ω => Xn n ω * Yn n ω) (fun ω => X ω * Y ω) := by
  have hvec :=
    thm_10_11_probability μ
      (fun n ω => thm_10_12_pair (Xn n ω) (Yn n ω))
      (fun ω => thm_10_12_pair (X ω) (Y ω))
      thm_10_12_mulMap Set.univ hPair_meas hMul_meas
      (by simp) (by simp)
      (fun v _ => thm_10_12_mulMap_continuousAt v)
      (thm_10_12_pair_probability μ Xn Yn X Y hX hY)
  have hcomp := (thm_10_10_probability_iff μ
    (fun n ω => thm_10_12_mulMap (thm_10_12_pair (Xn n ω) (Yn n ω)))
    (fun ω => thm_10_12_mulMap (thm_10_12_pair (X ω) (Y ω)))).mp hvec 0
  simpa [thm_10_12_mulMap, thm_10_12_one, thm_10_12_pair] using hcomp

theorem thm_10_12_probability_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hOne_meas :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω => thm_10_12_one (Xn n ω)) μ)
    (hConst_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_constMulMap α (thm_10_12_one (Xn n ω))) μ)
    (hX : ConvergesInProbability μ Xn X) :
    ConvergesInProbability μ (fun n ω => α * Xn n ω) (fun ω => α * X ω) := by
  have hvec :=
    thm_10_11_probability μ
      (fun n ω => thm_10_12_one (Xn n ω))
      (fun ω => thm_10_12_one (X ω))
      (thm_10_12_constMulMap α) Set.univ hOne_meas hConst_meas
      (by simp) (by simp)
      (fun v _ => thm_10_12_constMulMap_continuousAt α v)
      (thm_10_12_one_probability μ Xn X hX)
  have hcomp := (thm_10_10_probability_iff μ
    (fun n ω => thm_10_12_constMulMap α (thm_10_12_one (Xn n ω)))
    (fun ω => thm_10_12_constMulMap α (thm_10_12_one (X ω)))).mp hvec 0
  simpa [thm_10_12_constMulMap, thm_10_12_one] using hcomp

theorem thm_10_12_probability_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hPair_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_pair (Xn n ω) (Yn n ω)) μ)
    (hDiv_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_divMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hY_ne_meas : MeasurableSet {ω : Ω | Y ω ≠ 0})
    (hY_ne_measure : μ {ω : Ω | Y ω ≠ 0} = 1)
    (hX : ConvergesInProbability μ Xn X) (hY : ConvergesInProbability μ Yn Y) :
    ConvergesInProbability μ
      (fun n ω => Xn n ω / Yn n ω) (fun ω => X ω / Y ω) := by
  let S : Set (Fin 2 → ℝ) := {v | v 1 ≠ 0}
  have hS_meas : MeasurableSet {ω : Ω | thm_10_12_pair (X ω) (Y ω) ∈ S} := by
    simpa [S, thm_10_12_pair] using hY_ne_meas
  have hS_measure : μ {ω : Ω | thm_10_12_pair (X ω) (Y ω) ∈ S} = 1 := by
    simpa [S, thm_10_12_pair] using hY_ne_measure
  have hvec :=
    thm_10_11_probability μ
      (fun n ω => thm_10_12_pair (Xn n ω) (Yn n ω))
      (fun ω => thm_10_12_pair (X ω) (Y ω))
      thm_10_12_divMap S hPair_meas hDiv_meas
      hS_meas hS_measure
      (fun v hv => thm_10_12_divMap_continuousAt hv)
      (thm_10_12_pair_probability μ Xn Yn X Y hX hY)
  have hcomp := (thm_10_10_probability_iff μ
    (fun n ω => thm_10_12_divMap (thm_10_12_pair (Xn n ω) (Yn n ω)))
    (fun ω => thm_10_12_divMap (thm_10_12_pair (X ω) (Y ω)))).mp hvec 0
  simpa [thm_10_12_divMap, thm_10_12_one, thm_10_12_pair] using hcomp

/-- Theorem 10.12, exported as its eight algebraic preservation components.
The probability components expose the measurability side conditions required by
the local `TendstoInMeasure`-based continuous-mapping interface. -/
theorem thm_10_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X Y : Ω → ℝ) (α : ℝ)
    (hPair_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_pair (Xn n ω) (Yn n ω)) μ)
    (hOne_meas :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω => thm_10_12_one (Xn n ω)) μ)
    (hAdd_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_addMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hMul_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_mulMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hDiv_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_divMap (thm_10_12_pair (Xn n ω) (Yn n ω))) μ)
    (hConst_meas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => thm_10_12_constMulMap α (thm_10_12_one (Xn n ω))) μ)
    (hY_ne_seq : ∀ n : ℕ, ∀ᵐ ω ∂μ, Yn n ω ≠ 0)
    (hY_ne_ae : ∀ᵐ ω ∂μ, Y ω ≠ 0)
    (hY_ne_meas : MeasurableSet {ω : Ω | Y ω ≠ 0})
    (hY_ne_measure : μ {ω : Ω | Y ω ≠ 0} = 1) :
    (ConvergesAlmostSurely μ Xn X → ConvergesAlmostSurely μ Yn Y →
      ConvergesAlmostSurely μ
        (fun n ω => Xn n ω + Yn n ω) (fun ω => X ω + Y ω)) ∧
    (ConvergesAlmostSurely μ Xn X → ConvergesAlmostSurely μ Yn Y →
      ConvergesAlmostSurely μ
        (fun n ω => Xn n ω * Yn n ω) (fun ω => X ω * Y ω)) ∧
    (ConvergesAlmostSurely μ Xn X →
      ConvergesAlmostSurely μ (fun n ω => α * Xn n ω) (fun ω => α * X ω)) ∧
    (ConvergesAlmostSurely μ Xn X → ConvergesAlmostSurely μ Yn Y →
      ConvergesAlmostSurely μ
        (fun n ω => Xn n ω / Yn n ω) (fun ω => X ω / Y ω)) ∧
    (ConvergesInProbability μ Xn X → ConvergesInProbability μ Yn Y →
      ConvergesInProbability μ
        (fun n ω => Xn n ω + Yn n ω) (fun ω => X ω + Y ω)) ∧
    (ConvergesInProbability μ Xn X → ConvergesInProbability μ Yn Y →
      ConvergesInProbability μ
        (fun n ω => Xn n ω * Yn n ω) (fun ω => X ω * Y ω)) ∧
    (ConvergesInProbability μ Xn X →
      ConvergesInProbability μ (fun n ω => α * Xn n ω) (fun ω => α * X ω)) ∧
    (ConvergesInProbability μ Xn X → ConvergesInProbability μ Yn Y →
      ConvergesInProbability μ
        (fun n ω => Xn n ω / Yn n ω) (fun ω => X ω / Y ω)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hX hY => thm_10_12_almost_sure_add μ Xn Yn X Y hX hY
  · exact fun hX hY => thm_10_12_almost_sure_mul μ Xn Yn X Y hX hY
  · exact fun hX => thm_10_12_almost_sure_const_mul μ α Xn X hX
  · exact fun hX hY => thm_10_12_almost_sure_div μ Xn Yn X Y hX hY hY_ne_seq hY_ne_ae
  · exact fun hX hY =>
      thm_10_12_probability_add μ Xn Yn X Y hPair_meas hAdd_meas hX hY
  · exact fun hX hY =>
      thm_10_12_probability_mul μ Xn Yn X Y hPair_meas hMul_meas hX hY
  · exact fun hX =>
      thm_10_12_probability_const_mul μ α Xn X hOne_meas hConst_meas hX
  · exact fun hX hY =>
      thm_10_12_probability_div μ Xn Yn X Y hPair_meas hDiv_meas
        hY_ne_meas hY_ne_measure hX hY
