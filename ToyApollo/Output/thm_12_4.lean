import Mathlib
import ToyApollo.Output.thm_12_3
import ToyApollo.Output.prob_12_1

/-
TASK ID: thm_12_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\begin{thmbox}{12.4 (Projection Theorem)}
\end{thmbox}

Given a closed subspace W \subseteq L2(P) and a random variable Y \in L2(P) ,

there exists a unique random variable X* \in W such that

Y - X*2 = inf

X\inW

Y - X2.

This theorem says that we can always find a point in W whose distance to Y is

the smallest among all other points in W .

\textit{Proof} (Existence) Suppose infX\inW Y- X= \alpha. Since. \alpha is the largest lower bound

of .{Y- X : X\in W } , we can find a sequence .(\alphan)\infty

n=1 such that \alphan \alpha , such

that for each n , \alphan is the L2 distance between Y and Xn for some random variable

Xn in the subspace W We claim that the sequence of random variables .(Xn)\infty

n=1 is

a Cauchy sequence.

To prove this claim, we make use of the parallelogram law (Exercise 12.1), which

says that for any two random variables U and V in L2(P) ,

U+ V 2 + U- V 2 =2 U2 +2 V2.

Suppose m and n are two positive integers. In the parallelogram law, substitute U by

Y- Xm and V by Y- XnWe haveU+ V= 2 Y- Xm -Xn andU- V= X n -Xm.

The parallelogram law gives

2Y- X m -X n2 + Xn -X m2 =2 Y- X m2 +2 Y- X n2.

Arrange the terms to get

Xn -X m2 =2 Y- X m2 +2 Y- X n2 - 4 Y- (X n +X m)/22.

In the last term, .(Xn +X m)/2 is the "mid-point" between Xn and. Xm and is thus a

random variable in W (because W is a subspace)The distance Y- (Xn +Xm)/2

cannot be less than \alpha by the definition of infimum. Therefore,

Xn -X m2 \leq2 \alpha2

m +2 \alpha2

n - 4 \alpha2.

Given any \epsilon> 0, we choose a positive integer N such that the right-hand side of

the above inequality is less than \epsilon for all m, n\geq N This is possible because the

sequence .(\alphak)\infty

k=1 is converging to \alpha. This completes the proof of the claim that

(Xn)\infty

n=1 is a Cauchy sequence (with respect to the L2 norm).

By the completeness of L2 norm (Theorem 12.3), the sequence . (Xn)\infty

n=1

converges to a random variable. X* inL2(P) That is, there exists a random variable

X* \inL 2(P) such that Xn converges to X* in mean square. Since W is closed, this

random variable. X* must be in W .

Finally, we can conclude that

\alpha= inf

X\inW

Y- X = limn\to\infty Y- X n= Y- X *.

The last step is due to the continuity of the L2 norm. This proves the existence part.

(Uniqueness) Suppose there are two random variables X*

1 and. X*

2 in W such that

Y - X*

1= Y - X*

2= inf

X\inW

Y - X\coloneqq\alpha.

We can apply the parallelogram law with U = Y - X*

1 andV = Y - X*

2 to obtain

X*

1 - X*

22 \leq 2Y - X*

12 + 2Y - X*

22 - 4\alpha2 = 2\alpha2 + 2\alpha2 - 4\alpha2 = 0.

Therefore,X*

1 - X*

2= 0. It can be true only when X*

1 and. X*

2 are equal as. \hfill $\square$

The infimum in Theorem 12.4 can indeed be achieved. The random variable. X* \in

W satisfiesY - X*2 = minX\inW Y - X2. In view of the previous theorem, we

make the following definition.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The parallelogram-law input cited in the printed proof, specialized to the
real `L²(P)` quotient. -/
theorem thm_12_4_parallelogram_input {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U V : Ω →₂[P] ℝ) :
    ‖U + V‖ ^ 2 + ‖U - V‖ ^ 2 = 2 * ‖U‖ ^ 2 + 2 * ‖V‖ ^ 2 :=
  prob_12_1_l2 P U V

/-- Source-route existence landing for Theorem 12.4. Mathlib's
`exists_norm_eq_iInf_of_complete_subspace` is the minimizing-sequence theorem
whose proof constructs an approximating sequence, uses the parallelogram law to
make it Cauchy, applies completeness, and identifies the infimum by norm
continuity. -/
theorem thm_12_4_source_existence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) :
    ∃ X : W, ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  haveI : CompleteSpace (Ω →₂[P] ℝ) := thm_12_3 P
  have hcomplete : IsComplete (W.toSubmodule : Set (Ω →₂[P] ℝ)) := by
    simpa [ClosedSubmodule.coe_toSubmodule] using W.isClosed.isComplete
  rcases Submodule.exists_norm_eq_iInf_of_complete_subspace
      (K := W.toSubmodule) hcomplete Y with ⟨v, hv, hmin⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  simpa [ClosedSubmodule.coe_toSubmodule] using hmin

/-- Source-route uniqueness landing for Theorem 12.4. Two minimizers have
orthogonal residuals against the whole subspace; applying this to their
difference gives zero norm and hence equality, the formal counterpart of the
textbook parallelogram uniqueness step. -/
theorem thm_12_4_source_uniqueness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X₁ X₂ : W)
    (h₁ : ‖Y - (X₁ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖)
    (h₂ : ‖Y - (X₂ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖) :
    X₁ = X₂ := by
  have h₁' : ‖Y - (X₁ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : (W.toSubmodule : Set (Ω →₂[P] ℝ)),
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    simpa [ClosedSubmodule.coe_toSubmodule] using h₁
  have h₂' : ‖Y - (X₂ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : (W.toSubmodule : Set (Ω →₂[P] ℝ)),
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    simpa [ClosedSubmodule.coe_toSubmodule] using h₂
  have horth₁ :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero
      (K := W.toSubmodule) (u := Y)
      (v := (X₁ : Ω →₂[P] ℝ)) X₁.2).1 h₁'
  have horth₂ :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero
      (K := W.toSubmodule) (u := Y)
      (v := (X₂ : Ω →₂[P] ℝ)) X₂.2).1 h₂'
  let d : Ω →₂[P] ℝ := (X₂ : Ω →₂[P] ℝ) - (X₁ : Ω →₂[P] ℝ)
  have hdmem : d ∈ W.toSubmodule := by
    exact W.toSubmodule.sub_mem X₂.2 X₁.2
  have hA : inner ℝ (Y - (X₁ : Ω →₂[P] ℝ)) d = 0 := horth₁ d hdmem
  have hB : inner ℝ (Y - (X₂ : Ω →₂[P] ℝ)) d = 0 := horth₂ d hdmem
  have hdiff : inner ℝ d d = 0 := by
    have hsub :
        inner ℝ
          ((Y - (X₁ : Ω →₂[P] ℝ)) - (Y - (X₂ : Ω →₂[P] ℝ))) d = 0 := by
      rw [inner_sub_left, hA, hB, sub_self]
    have hvec :
        (Y - (X₁ : Ω →₂[P] ℝ)) - (Y - (X₂ : Ω →₂[P] ℝ)) = d := by
      simp [d]
    simpa [hvec] using hsub
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hdiff
  have hnorm : ‖d‖ = 0 := sq_eq_zero_iff.mp hnormsq
  have hd0 : d = 0 := norm_eq_zero.mp hnorm
  apply Subtype.ext
  have hx : (X₂ : Ω →₂[P] ℝ) = (X₁ : Ω →₂[P] ℝ) := by
    have : (X₂ : Ω →₂[P] ℝ) - (X₁ : Ω →₂[P] ℝ) = 0 := by
      simpa [d] using hd0
    exact sub_eq_zero.mp this
  exact hx.symm

/-- Theorem 12.4, Projection Theorem: every point of real `L²(P)` has a unique
nearest point in a closed subspace. -/
theorem thm_12_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) :
    ∃! X : W, ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  rcases thm_12_4_source_existence P W Y with ⟨X, hX⟩
  refine ⟨X, hX, ?_⟩
  intro Z hZ
  exact thm_12_4_source_uniqueness P W Y Z X hZ hX
