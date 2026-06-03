# Phase2 Examples

This file records short examples of current policy. Keep it short; put full
investigation history in archive or task reports.

Responsibility: give compact examples of policy application. Non-responsibility:
defining policy or preserving full repair histories.

## `thm_11_7`: Public Assumption Expansion

Bad public package:

```lean
MemLp (fun w => X i w - mu) 4 P
rthMoment P (fun w => X i w - mu) 4 <= c
```

Why bad: the textbook assumes finite fourth moments of `X_i` and then centers
inside the proof. The centered package is a proof ingredient and must be derived
internally.

Acceptable public package:

```lean
MemLp (X i) 4 P
rthMoment P (X i) 4 <= c
```

Why acceptable: this is the Lean spelling of the source condition
`E[X_i^4] <= c < infinity`.

Required internal theorem:

```lean
thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound
```

This theorem derives the centered package from the uncentered public source
assumption. With that bridge and the fourth-moment expansion/tail summability
route landed, `thm_11_7` can be classified as `textbook_proof_completed`.

## Adapter Vs Textbook Route

If a theorem is closed by a stronger Mathlib theorem whose proof route skips the
source proof, classify it as `mathlib_backed_adapter_completed`, not
`textbook_proof_completed`.

If Mathlib supplies local algebra, measure, summability, or inequality lemmas
inside the source proof route, that is ordinary proof substrate and can still be
textbook-complete.

## `prob_11_10`: Task-Local Missing Lemma

Bad repair stop:

```lean
exact prob_11_10_polya_uniformization_from_pointwise P X F hCDF hIndicators hPointwise
```

when no theorem or lemma with that name exists.

Why bad: the candidate invented a task-local theorem name and then stopped at
`unknown_identifier`. This is not an external dependency blocker.

Required action: prove that theorem, split it into smaller local lemmas, or
import a real existing helper. If the final public theorem still exposes
indicator-level SLLN premises instead of source-facing iid/cdf assumptions, it
must be classified as an operational/interface theorem rather than the final
textbook-facing Glivenko-Cantelli statement.
