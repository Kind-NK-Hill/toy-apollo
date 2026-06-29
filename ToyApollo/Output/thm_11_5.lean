import Mathlib
import ToyApollo.Output.def_7_3
import ToyApollo.Output.def_9_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.thm_11_4

/-
TASK ID: thm_11_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-weak-law-large-numbers
TASK CONTENT:
\begin{thmbox}{11.5 (Weak Law of Large Numbers (L2 Version))}
\end{thmbox}

Let .(Xi)\infty

i=1 be a sequence of pairwise uncorrelated random variables with

common mean E[Xi]= \mu and variance Va r(Xi) = \sigma2 for all i. Then

Sn/n

P

-\to \mu.

\textit{Proof} The proof is an application of Chebyshev inequality (Theorem 11.2).

Fix any \epsilon> 0 and integer n. Using the fact that Sn/n is an average of pairwise

uncorrelated random variables with common mean \mu,we have

P

(\vert\vertSn

n -\mu

\vert\vert >\epsilon

)

=P

(\vert\vertSn -n\mu

\vert\vert >n \epsilon

)

\leq Va r(Sn)

n2\epsilon2 = 1

n2\epsilon2

n\sum

i=1

Va r(Xi).

The last equality follows from Theorem 11.4.

Using Theorem 11.4, we know that .

\sumn

i=1 Va r(Xi)= n\sigma 2. Therefore, we have

P

( \vert\vert\vertSn

n -\mu

\vert\vert\vert >\epsilon

)

\leq n\sigma2

n2\epsilon2 = \sigma2

n\epsilon2 .

Asn\to\infty , the right-hand side approaches zero, which implies thatSn/n converges

in probability to \mu. This completes the proof. \hfill $\square$

The assumption of finite second moment can be relaxed to finite mean, but at the

cost of strengthening the uncorrelated assumption to independence.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

/-- The textbook sample average, written with `n + 1` terms to avoid a zero
denominator at the first natural index. -/
noncomputable def thm_11_5_sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (1 / ((n : ℝ) + 1)) * ∑ i : Fin (n + 1), X i.1 ω

private theorem thm_11_5_local_variance_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    _root_.variance P Y = Var[Y; P] := by
  rw [_root_.variance, rthCentralMoment]
  exact ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := Y) hY.aemeasurable

private theorem thm_11_5_sampleMean_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) (n : ℕ) :
    MemLp (thm_11_5_sampleMean X n) 2 P := by
  have hsum : MemLp (fun ω => ∑ i : Fin (n + 1), X i.1 ω) 2 P := by
    simpa using
      (memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => hX i.1))
  change MemLp (fun ω => (1 / ((n : ℝ) + 1)) *
    ∑ i : Fin (n + 1), X i.1 ω) 2 P
  simpa [one_div] using hsum.const_mul (1 / ((n : ℝ) + 1))

private theorem thm_11_5_sampleMean_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (m : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, P[X i] = m) (n : ℕ) :
    P[thm_11_5_sampleMean X n] = m := by
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  calc
    P[thm_11_5_sampleMean X n]
        = (1 / ((n : ℝ) + 1)) *
            P[fun ω => ∑ i : Fin (n + 1), X i.1 ω] := by
          simp [thm_11_5_sampleMean, integral_const_mul]
    _ = (1 / ((n : ℝ) + 1)) *
          (∑ i : Fin (n + 1), P[X i.1]) := by
          rw [integral_finset_sum]
          exact fun i _hi => (hX i.1).integrable (by simp)
    _ = (1 / ((n : ℝ) + 1)) *
          (∑ _i : Fin (n + 1), m) := by
          simp [hmean]
    _ = m := by
          simp [Finset.sum_const, Fintype.card_fin]
          field_simp [hNpos.ne']

private theorem thm_11_5_sampleMean_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (sigma2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P)
    (huncorr : Pairwise fun i j => Uncorrelated P (X i) (X j))
    (hvar : ∀ i, _root_.variance P (X i) = sigma2) (n : ℕ) :
    _root_.variance P (thm_11_5_sampleMean X n) =
      sigma2 / ((n : ℝ) + 1) := by
  let S : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), X i.1 ω
  let c : ℝ := 1 / ((n : ℝ) + 1)
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hS_mem : MemLp S 2 P := by
    simpa [S] using
      (memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => hX i.1))
  have hmean_mem : MemLp (thm_11_5_sampleMean X n) 2 P :=
    thm_11_5_sampleMean_memLp P X hX n
  have hS_var :
      _root_.variance P S = ∑ i : Fin (n + 1), _root_.variance P (X i.1) := by
    simpa [S] using
      (thm_11_4 P (fun i : Fin (n + 1) => X i.1)
        (fun i => hX i.1)
        (by
          intro i j hij
          exact huncorr (by
            intro hval
            exact hij (Fin.ext hval))))
  have hS_var_sigma :
      _root_.variance P S = ((n : ℝ) + 1) * sigma2 := by
    rw [hS_var]
    simp [hvar, Finset.sum_const, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hsmul : thm_11_5_sampleMean X n = c • S := by
    ext ω
    simp [thm_11_5_sampleMean, S, c, smul_eq_mul]
  calc
    _root_.variance P (thm_11_5_sampleMean X n)
        = Var[thm_11_5_sampleMean X n; P] :=
          thm_11_5_local_variance_eq P hmean_mem
    _ = Var[c • S; P] := by rw [hsmul]
    _ = c ^ 2 * Var[S; P] := by
          exact ProbabilityTheory.variance_smul c S P
    _ = c ^ 2 * _root_.variance P S := by
          rw [thm_11_5_local_variance_eq P hS_mem]
    _ = c ^ 2 * (((n : ℝ) + 1) * sigma2) := by
          rw [hS_var_sigma]
    _ = sigma2 / ((n : ℝ) + 1) := by
          dsimp [c]
          field_simp [hNpos.ne']

private theorem thm_11_5_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (m sigma2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, P[X i] = m)
    (huncorr : Pairwise fun i j => Uncorrelated P (X i) (X j))
    (hvar : ∀ i, _root_.variance P (X i) = sigma2)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    P (deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ => m) n ε) ≤
      ENNReal.ofReal ((sigma2 / ((n : ℝ) + 1)) / ε ^ 2) := by
  let A : Ω → ℝ := thm_11_5_sampleMean X n
  have hA_mem : MemLp A 2 P := thm_11_5_sampleMean_memLp P X hX n
  have hA_mean : P[A] = m := thm_11_5_sampleMean_integral P X m hX hmean n
  have hA_var :
      _root_.variance P A = sigma2 / ((n : ℝ) + 1) :=
    thm_11_5_sampleMean_variance P X sigma2 hX huncorr hvar n
  let Echeb : Set Ω := {ω | ε ≤ |A ω - P[A]|}
  have hsubset :
      deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ => m) n ε ⊆ Echeb := by
    intro ω hω
    dsimp [deviationEvent, Echeb, A] at hω ⊢
    rw [hA_mean]
    exact le_of_lt hω
  have hmono : P (deviationEvent (fun n => thm_11_5_sampleMean X n) (fun _ => m) n ε) ≤
      P Echeb := measure_mono hsubset
  have hcheb_real : P.real Echeb ≤ _root_.variance P A / ε ^ 2 := by
    simpa [Echeb, A] using thm_11_2 P A hA_mem hε
  have hcheb : P Echeb ≤ ENNReal.ofReal (_root_.variance P A / ε ^ 2) := by
    have hE : P Echeb = ENNReal.ofReal (P.real Echeb) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P Echeb)]
    rw [hE]
    exact ENNReal.ofReal_le_ofReal hcheb_real
  exact hmono.trans <| by
    simpa [hA_var] using hcheb

/--
Theorem 11.5, L2 weak law of large numbers.

For a pairwise uncorrelated sequence with common mean and common variance, the
sample averages converge in probability to the common mean.  The sequence is
indexed from `0`, so the average at index `n` uses the first `n + 1` variables.
-/
theorem thm_11_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (m sigma2 : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P)
    (huncorr : Pairwise fun i j => Uncorrelated P (X i) (X j))
    (hmean : ∀ i, P[X i] = m)
    (hvar : ∀ i, _root_.variance P (X i) = sigma2) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
  intro ε hε
  have hden :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hreal :
      Tendsto (fun n : ℕ => (sigma2 / ((n : ℝ) + 1)) / ε ^ 2)
        atTop (nhds 0) := by
    have hdiv :
        Tendsto (fun n : ℕ => sigma2 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hden sigma2
    simpa [div_eq_mul_inv] using hdiv.mul tendsto_const_nhds
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal ((sigma2 / ((n : ℝ) + 1)) / ε ^ 2))
        atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
    (fun n => zero_le _) ?_
  intro n
  exact thm_11_5_tail_bound P X m sigma2 hX hmean huncorr hvar hε n
