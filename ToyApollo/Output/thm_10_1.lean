import Mathlib
import ToyApollo.Output.def_10_1

/-
TASK ID: thm_10_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{thmbox}{10.1}
\[
X_n\xrightarrow{\mathrm{a.s.}}X
\quad\Longleftrightarrow\quad
\forall \epsilon>0,\; P(\lvert X_n-X\rvert>\epsilon\ \mathrm{i.o.})=0.
\]
\end{thmbox}

\textit{Proof}
Suppose $X_n\xrightarrow{\mathrm{a.s.}}X$, and let $E$ denote the event that $X_n(\omega)\to X(\omega)$. By assumption, we have $P(E)=1$.

Fix $\epsilon>0$. If the sequence $(X_n(\omega))_{n\geq 1}$ converges to $X(\omega)$, there exists a sufficiently large integer $N$ such that $\lvert X_n(\omega)-X(\omega)\rvert\leq\epsilon$ for all $n\geq N$. Hence, if $\omega$ is an outcome in $\Omega$ such that $\lvert X_n(\omega)-X(\omega)\rvert>\epsilon$ for infinitely many $n$, we must have $\omega\in E^c$. Since $P(E^c)=0$, we obtain
\[
P(\lvert X_n-X\rvert>\epsilon\ \mathrm{i.o.})=0
\]
as desired.

Conversely, suppose $P(\lvert X_n-X\rvert>\epsilon\ \mathrm{i.o.})=0$ for all $\epsilon>0$. By the definition of convergence of sequences, we have
\[
X_n(\omega)\to X(\omega)
\quad\Longleftrightarrow\quad
\forall k\in\mathbb{N},\; \lvert X_n(\omega)-X(\omega)\rvert\leq \frac{1}{k}
\text{ for all sufficiently large }n.
\]
Hence, the event that the sequence $(X_n(\omega))_{n\geq 1}$ fails to converge to $X(\omega)$ is contained in the countable union
\[
\bigcup_{k=1}^{\infty}
\left\{\omega:\lvert X_n(\omega)-X(\omega)\rvert>\frac{1}{k}\ \mathrm{i.o.}\right\}.
\]
Since all the events on the right are null sets, we have $P(X_n\not\to X)=0$.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

/-- The ε-deviation event used in Theorem 10.1. -/
def almostSureDeviationEvent {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ)
    (ε : ℝ) : Set Ω :=
  {ω : Ω | |Xn n ω - X ω| > ε}

/-- The textbook event `{ω : |Xₙ(ω) - X(ω)| > ε i.o.}`. -/
def deviationInfinitelyOften {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (ε : ℝ) :
    Set Ω :=
  limsup (fun n : ℕ => almostSureDeviationEvent Xn X n ε) atTop

private lemma not_mem_deviationInfinitelyOften_of_tendsto {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ} {ω : Ω} {ε : ℝ} (hε : 0 < ε)
    (hω : Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    ω ∉ deviationInfinitelyOften Xn X ε := by
  rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem]
  refine Filter.not_frequently.2 ?_
  rcases (Metric.tendsto_atTop.mp hω) ε hε with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hdist : dist (Xn n ω) (X ω) < ε := hN n hn
  have habs : |Xn n ω - X ω| < ε := by
    simpa [Real.dist_eq] using hdist
  exact not_lt.mpr habs.le

private lemma tendsto_of_not_mem_deviationInfinitelyOften_all {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ} {ω : Ω}
    (hω : ∀ k : ℕ, ω ∉ deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1))) :
    Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  rcases Real.exists_nat_pos_inv_lt hε with ⟨k, hk_pos, hk_lt⟩
  have hk_cast_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  have hthreshold_lt : 1 / ((k : ℝ) + 1) < ε := by
    calc
      1 / ((k : ℝ) + 1) < (k : ℝ)⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt hk_cast_pos (lt_add_one (k : ℝ))
      _ < ε := hk_lt
  have hnfreq : ¬ ∃ᶠ n : ℕ in atTop,
      ω ∈ almostSureDeviationEvent Xn X n (1 / ((k : ℝ) + 1)) := by
    intro hfreq
    exact hω k (mem_limsup_iff_frequently_mem.2 hfreq)
  have hev : ∀ᶠ n : ℕ in atTop,
      ¬ ω ∈ almostSureDeviationEvent Xn X n (1 / ((k : ℝ) + 1)) :=
    Filter.not_frequently.1 hnfreq
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hnot := hN n hn
  have hle : |Xn n ω - X ω| ≤ 1 / ((k : ℝ) + 1) := by
    exact not_lt.1 hnot
  calc
    dist (Xn n ω) (X ω) = |Xn n ω - X ω| := by simp [Real.dist_eq]
    _ ≤ 1 / ((k : ℝ) + 1) := hle
    _ < ε := hthreshold_lt

/--
Theorem 10.1: almost-sure convergence is equivalent to every positive
deviation event occurring only finitely often almost surely.
-/
theorem thm_10_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ConvergesAlmostSurely μ Xn X ↔
      ∀ ε : ℝ, 0 < ε → μ (deviationInfinitelyOften Xn X ε) = 0 := by
  constructor
  · intro has ε hε
    have hbad : μ {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} = 0 :=
      ae_iff.1 has
    refine MeasureTheory.measure_mono_null ?_ hbad
    intro ω hω hconv
    exact not_mem_deviationInfinitelyOften_of_tendsto hε hconv hω
  · intro hio
    refine ae_iff.2 ?_
    have hbad_subset :
        {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} ⊆
          ⋃ k : ℕ, deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1)) := by
      intro ω hω_bad
      by_contra hnot
      have hnot_each :
          ∀ k : ℕ, ω ∉ deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1)) := by
        intro k hk
        exact hnot (mem_iUnion.2 ⟨k, hk⟩)
      exact hω_bad (tendsto_of_not_mem_deviationInfinitelyOften_all hnot_each)
    refine MeasureTheory.measure_mono_null hbad_subset ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro k
    have hk_pos : 0 < (1 / ((k : ℝ) + 1) : ℝ) := by positivity
    exact hio (1 / ((k : ℝ) + 1)) hk_pos
