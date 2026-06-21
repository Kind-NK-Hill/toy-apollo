import ToyApollo.Output.thm_14_5_support

/-
TASK ID: thm_14_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-tightness
TASK CONTENT:
\begin{thmbox}{14.5}
\end{thmbox}

Let .(Pn)\infty

n=1 be a sequence of distribution on R, and let \phin(t) denote

the characteristic function of distribution PnI f .(\phin(t))\infty

n=1 converges to a

functionc(t) that is continuous at t= 0 , then.(Pn)\infty

n=1 is tight.

\textit{Proof} Because \phin(0)= 1 for all n,we havec(0)= 1 Moreover, note that . 1-

\phin(t)= 0 when t= 0 The idea of proof is to examine the behavior of . 1- \phi n(t)

when t is close to zero. By assumption, we know that .1- \phi n(t) converges to the

function .1- c(t) , which is continuous at t= 0 .

The first step is to apply Fubini theorem to derive

\int u

-u

(1- \phin(t)) dt=

\int

R

\int u

-u

(1- e itx )dtdP n(x) (14.3)

for any positive u. The order of integration can be exchanged because the integrand

has absolute value bounded by 2.

Next, for any u> 0 and x/=0 , the inner integral can be computed using

\int u

-u

1- e itx dt= 2

\int u

1- cos txdt = 2

(

u- sinux

x

)

(14.4)

Combining (14.3) and (14.4), we obtain

u

\int u

-u

(1- \phin(t)) dt=

\int

R

(

1- sinux

ux

)

dPn(x). (14.5)

On the other hand, for\vertx\vert\geq 2/u, we can bound the integral in the second integral

above as follows:

(

1- sin(ux)

ux

)

=2

(

1- sin(u\vertx\vert)

u\vertx\vert

)

\geq2

(

1- 1

u\vertx\vert

)

\geq1 .

Therefore,

(

1- sinux

ux

)

\geq

{

1f o r \vertx\vert\geq 2

u

0f o r \vertx\vert< 2

u.

Here, we use the fact that sin(u\vertx\vert)<u \vertx\vert when u\vertx\vert< 2 Consequently, for any

u> 0,

\vert\vert\vert 1

u

\int u

-u

(1- \phin(t)) dt

\vert\vert\vert \geqP n

(

\vertx\vert\geq 2

u

)

(14.6)

The remaining task is to find a sufficiently small u, such that the left-hand side

of (14.6) is bounded by a constant for all n. Applying the triangle inequality for real

numbers, we can write

\vert\vert\vert 1

u

\int u

-u

(1- \phin(t)) dt

\vert\vert\vert =

\vert\vert\vert 1

u

\int u

-u

(1- c(t) + c(t) - \phin(t)) dt

\vert\vert\vert

\leq 1

u

\int u

-u

\vert1- c(t) \vertdt + 1

u

\int u

-u

\vertc(t)- \phin(t)\vertdt. (14.7)

The first integral in (14.7) can be made arbitrarily small because it is assumed that

c(t) is continuous at t= 0 We can pick a sufficiently small u0 >0 such that

u0

\int u0

-u0

\vert1- c(t) \vertdt \leq \epsilon/ 2.

For the second term in (14.7), we use the assumption that\phin(t) is converging to. c(t)

to show that

limn\to\infty

u0

\int u0

-u0

\vertc(t)- \phin(t)\vertdt = 1

u0

\int u0

-u0

limn\to\infty \vertc(t)- \phin(t)\vertdt = 0 .

Because the integrand is bounded by a constant 2, we can apply the dominated

convergence theorem and choose a sufficiently large integer N such that

u0

\int u0

-u0

\vertc(t)- \phin(t)\vertdt \leq \epsilon/ 2

for all n\geq N Consequently, we obtain

Pn

(

\vertx\vert\geq 2

u0

)

\leq\epsilon

for n\geq N .

Since there are only finitely many positive integers that are less than N, for each

i= 1 ,2,...,N -1, we can pick. Mi such thatPi(\vertx\vert\geq Mi)\leq \epsilon. Finally, we choose

a value of M that is larger than. M1,M2,...,M N- 1, and.2/u0. Then. Pn(\vertx\vert>M ) \leq

\epsilonfor all n. This completes the proof that the sequence .(Pn)\infty

n=1 is tight. \hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Complex Real
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section

/-- Theorem 14.5: pointwise convergence of characteristic functions to a
function continuous at zero implies tightness. -/
theorem thm_14_5
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    def_14_3 Pseq := by
  exact
    thm_14_5_of_uniformTailBound Pseq
      (thm_14_5_source_route_uniform_tail_bound Pseq c hchar hcont)
