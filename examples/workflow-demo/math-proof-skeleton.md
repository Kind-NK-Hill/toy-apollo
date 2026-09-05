# Teaching repair: definition and caller skeleton

Scope: this new teaching fixture only, outside the probability textbook catalog.
The source is `source.tex`; the initial defect is a source statement mismatch,
because the required domain conditions are absent from the public interface.

1. Accept natural-number inputs `hits` and `total`, together with proofs of
   `0 < total` and `hits <= total`. These are exactly the source domain
   conditions. Do not add a premise asserting the numerical conclusion.
2. Define the returned natural number by `1000 * hits / total`. Natural-number
   division is the nonnegative integer quotient when the divisor is positive;
   this preserves the specified rounded per-thousand count. It is not a real
   probability and no probability-measure theorem is being established.
3. For the direct caller, supply proofs of `0 < 4` and `2 <= 4`. Evaluate
   `1000 * 2 / 4` to `500`. Lean's kernel-checked closed computation suffices for
   the domain witnesses and final equality. No Mathlib theorem, axiom,
   auxiliary bridge, or circular premise is needed.

The interface-only intermediate version intentionally leaves the caller old so
the compiler can expose its missing arguments. The completed repair must update
both the definition and that caller before it receives semantic approval.
Reviewing this skeleton authorizes only this teaching repair route. It does not
approve a Lean candidate or replace a fresh bound semantic review and apply.
