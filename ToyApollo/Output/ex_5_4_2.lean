import ToyApollo.Support.IIDWord

/-
TASK ID: ex_5_4_2
TYPE: Example_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
TASK CONTENT:
\textbf{Example 5.4.2 (Monkey Randomly Typing on a Keyboard)} \\
Let $\mathcal{A}$ be an alphabet set of finite size, and let $w=a_1a_2 \cdots a_n$ be a particular word of length $n$, where $a_i \in \mathcal{A}$ for all $i$. If we randomly generate an infinite string $(X_i)_{i=1}^{\infty}$ where $X_i$'s are independent and uniformly chosen from $\mathcal{A}$, then with probability $1$, the word $w$ appears at least once in the infinite string in $n$ consecutive positions.

To see this, we can divide the infinite string into infinitely many non-overlapping sub-strings of length $n$. The first sub-string is from position $1$ to $n$, the second sub-string is from position $n+1$ to $2n$, and so on. For $k=1,2,3,\ldots$, let $A_k$ be the event that the $k$-th sub-string is exactly equal to the chosen string $w$. These events are independent because there is no overlap between the sub-strings. Although the probability $P(A_k)$ is a very small number, it is still strictly positive. Hence, by the second Borel--Cantelli lemma, with probability $1$, infinitely many such sub-strings are equal to $w$.
...
This example is often presented vividly by taking the word $w$ to be a Shakespeare novel and imagining a monkey randomly typing on a keyboard one character at a time. The Borel--Cantelli lemma states that given infinite time, the monkey will reproduce the entire volume of the Shakespeare novel, with probability $1$.

Combining the two Borel--Cantelli lemmas, we have the following zero--one law.
-/

-- WRITE FINAL LEAN CODE BELOW
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

section MonkeyTyping

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {n : ℕ} [NeZero n]

/--
For a uniformly random infinite string over a finite alphabet, every fixed word appears in
infinitely many non-overlapping blocks with probability `1`.
-/
theorem ex_5_4_2 (w : Fin n → α) :
    typingMeasure (α := α) (limsup (wordEvent (α := α) n w) atTop) = 1 := by
  exact typingMeasure_limsup_wordEvent_eq_one (α := α) (n := n) w

end MonkeyTyping
