# Semantic Review Report for prob_14_11

- Verdict: `pass`
- Proof class: `source_route_proof_completed`
- Completion class: `textbook_problem_completed_exact_standardized`
- Needs class normalization: `False`
- Task status: ``
- Confidence: `high`
- Recommended disposition: `accept`
- Cache hit: `False`

## Summary

Pass. The v8 hash-bound official subject proves the source-facing exact-standardized generalization of Example 14.4.3 for targetDistinct n / couponTypes n -> r, 0 < r < 1. The final theorem keeps the documented thm_14_8_ProofBeyondBook boundary, proves the local coupon triangular-array representation and Lyapunov condition in prob_14_11_support.lean, and does not assert the rejected fixed-r textbook-normalized convergence from ratio-only hypotheses. prob_14_11_support.lean now imports ToyApollo.Output.chapter14_coupon_geometric_support directly and has no code-level import or symbol use of ex_14_4_3 task-owned support.

## Reviewer Independence

- Role: `independent_read_only_reviewer`
- Read-only: `True`
- Edited candidate: `False`
- Used current request: `True`

## Interface Contract

- Status: `covered`
- Summary: The public theorem has the accepted exact-standardized statement. Source setup data are public as fields; row independence, exact representation, moment formulas, variance bounds, and Lyapunov are proved in support declarations. The only public proof premise is the allowed thm_14_8_ProofBeyondBook boundary.

## Proof Obligations

- Status: `covered`
- Summary: All active blocking obligations are covered by verified theorem/field landings. The obsolete mean/variance-scale transfer is correctly not applicable because reviving it would assert the forbidden fixed-r textbook route under ratio-only hypotheses.

## Downstream Adequacy

- Status: `covered`
- Summary: No direct downstream consumers are listed. The exported theorem and support declarations are adequate for the source task and do not force downstream users to provide new non-source theorem-level assumptions.

## Forbidden Weakenings

- `not_present` `unnamed`:
- `not_present` `unnamed`:

## Findings

- `info` / `general`:
