import ToyApollo.Output.def_2_4
import ToyApollo.Output.thm_2_1

/-
\textbf{2.6.} For $i=1,2,3,\dots$, let $A_i$ be a subset of a set $\Omega$. Prove that
\[
\liminf_{i\to\infty} A_i \subseteq \limsup_{i\to\infty} A_i.
\]

HARD DEPENDENCIES (plan-derived and mandatory imports already uploaded as local Lean files)
- (none)

SOFT IMPORTS (externally selected but mandatory imports already uploaded as local Lean files)
- def_2_4 | type=Definition | title=Definition 2.4 (liminf and limsup of Sets) | source_plan=41_chap2_algebra_of_events
  latex=\begin{defbox}{2.4} Let $E_1,E_2,\dots$ be an arbitrary sequence of subsets in a set $\Omega$. The \textit{limit inferior} and \textit{limit superior} of $(E_i)_{i\ge 1}$ are defined, respectively, as \[ \liminf_{i\to\infty} E_i \triangleq \bigcup_{j=1}^{\infty}\bigcap_{k\ge j} E_k, \qquad \limsup_{i\to\infty} E_i \triangleq \bigcap_{j=1}^{\infty}\bigcup_{k\ge j} E_k. \] In general, we have the following set inclusion: \[ \liminf_{i\to\infty} E_i \subseteq \limsup_{i\to\infty} E_i. \] If equality holds, we say that the \textit{limit} of $(E_i)_{i\ge 1}$ exists and is defined as $\liminf_i E_i$ or $\limsup_i E_i$. \end{defbox}
- thm_2_1 | type=Theorem_with_Proof | title=Theorem 2.1 (Definition 2.4) | source_plan=41_chap2_algebra_of_events
  latex=\begin{thmbox}{2.1 (Definition 2.4)} Let $(E_i)_{i\ge 1}$ be a sequence of subsets in a set $\Omega$. We have \[ \liminf_{i\to\infty} E_i = \{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ for all but finitely many } i\}, \] \[ \limsup_{i\to\infty} E_i = \{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ infinitely often}\}. \] \end{thmbox} \textit{Proof} We note that the condition of an outcome $\omega$ being in $E_i$ for all but finite many $i$ is equivalent to the statement that $\omega$ belongs to $E_i$ eventually for all $i\ge N$, for some integer $N$. Using the definition of liminf, we see that an outcome $\omega$ belongs to $\cup_{j\ge 1}\cap_{k\ge j} E_k$ if and only if it belongs to $\cap_{k\ge j} E_k$ for some $j$. This is the same as saying that $\omega$ bel...

FINAL IMPORT UNION (all listed files are mandatory imports and physically included in this package)
- def_2_4 | type=Definition | title=Definition 2.4 (liminf and limsup of Sets) | source_plan=41_chap2_algebra_of_events
  latex=\begin{defbox}{2.4} Let $E_1,E_2,\dots$ be an arbitrary sequence of subsets in a set $\Omega$. The \textit{limit inferior} and \textit{limit superior} of $(E_i)_{i\ge 1}$ are defined, respectively, as \[ \liminf_{i\to\infty} E_i \triangleq \bigcup_{j=1}^{\infty}\bigcap_{k\ge j} E_k, \qquad \limsup_{i\to\infty} E_i \triangleq \bigcap_{j=1}^{\infty}\bigcup_{k\ge j} E_k. \] In general, we have the following set inclusion: \[ \liminf_{i\to\infty} E_i \subseteq \limsup_{i\to\infty} E_i. \] If equality holds, we say that the \textit{limit} of $(E_i)_{i\ge 1}$ exists and is defined as $\liminf_i E_i$ or $\limsup_i E_i$. \end{defbox}
- thm_2_1 | type=Theorem_with_Proof | title=Theorem 2.1 (Definition 2.4) | source_plan=41_chap2_algebra_of_events
  latex=\begin{thmbox}{2.1 (Definition 2.4)} Let $(E_i)_{i\ge 1}$ be a sequence of subsets in a set $\Omega$. We have \[ \liminf_{i\to\infty} E_i = \{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ for all but finitely many } i\}, \] \[ \limsup_{i\to\infty} E_i = \{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ infinitely often}\}. \] \end{thmbox} \textit{Proof} We note that the condition of an outcome $\omega$ being in $E_i$ for all but finite many $i$ is equivalent to the statement that $\omega$ belongs to $E_i$ eventually for all $i\ge N$, for some integer $N$. Using the definition of liminf, we see that an outcome $\omega$ belongs to $\cup_{j\ge 1}\cap_{k\ge j} E_k$ if and only if it belongs to $\cap_{k\ge j} E_k$ for some $j$. This is the same as saying that $\omega$ bel...
-/
theorem prob_2_6 (Ω : Type _) (A : ℕ → Set Ω) :
    (⋃ n : ℕ, ⋂ i ≥ n, A i) ⊆ (⋂ n : ℕ, ⋃ i ≥ n, A i) := by
      intro ω hω;
      simp +zetaDelta at *;
      exact fun n => ⟨ _, le_max_left _ _, hω.choose_spec _ ( le_max_right _ _ ) ⟩