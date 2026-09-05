# Case study: `thm_14_8`

## What went wrong

The historical Lean theorem compiled, but it accepted a
`ProofBeyondBook` structure whose fields already contained the two difficult
mathematical steps. The task was therefore recorded as
`allowed_exception`, not as a clean proof. Any downstream caller also had to
carry that proof package.

This was honest as temporary debt, but it was not finished formalization and
it was a poor project story: the theorem delegated the result that an
interviewer would naturally ask about.

## Review and repair

1. A July review passed only at the explicit exception boundary; apply did not
   count it as clean completion.
2. A new candidate implemented the canonical triangular-array proof, including
   the Lindeberg characteristic-function route and Lyapunov-to-Lindeberg
   implication.
3. Semantic review still failed because the concrete independent-row Interface
   was missing and a direct consumer still required the old proof package.
4. The repair added the concrete-row/product-law bridge and migrated the direct
   consumer to the premise-free theorem.
5. Fresh review passed as `source_faithful_proof_completed`; `review-apply`
   promoted the candidate and the final build succeeded.

The important engineering point is that replacing a proof premise with a large
internal proof was still insufficient until the public Interface and its direct
consumer were reviewed together.

## Files

- [`initial.lean`](initial.lean): an independently compiling, reduced
  reconstruction of the historical public-premise theorem shape.
- [`final.lean`](final.lean): the same reduced Interface with internally proved
  branches and no `ProofBeyondBook` argument.
- [`review-timeline.json`](review-timeline.json): the historical exception,
  failed transition review, and final hash-bound pass.

Both snapshots deliberately collapse the mathematical conditions to a toy
predicate so they compile quickly and compare only the Interface change. The
full proof remains in
[`ProbabilityTheory/chapter_14/thm_14_8.lean`](../../../ProbabilityTheory/chapter_14/thm_14_8.lean);
the case slice does not claim to reproduce that proof.
