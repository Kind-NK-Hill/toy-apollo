# Case study: `ex_8_3_4`

## What went wrong

The first candidate encoded a finite transport matrix, its marginal
constraints, and a double-sum cost. It then proved that one fixed matrix was
feasible and that its cost equaled the same displayed expression.

That is not an optimization result. The central quantifier over every feasible
competitor was missing, so a feasibility certificate was presented as an
optimal transport solution.

A second candidate repaired the finite linear program and optimizer, but review
found another omitted mathematical object: the metric-cost specialization and
finite-carrier Wasserstein Interface.

## Review and repair

1. Fail: no lower-bound, comparison, argmin, or optimizer-existence claim.
2. Fail: optimization is repaired, but the Wasserstein part of the bound task
   has no public landing.
3. Pass: the final subject expresses feasible couplings, an attained minimum,
   metric-power cost, and the guarded distance construction.

This case is a direct example of quantifier drift: replacing “minimize over all
feasible plans” with “here is a feasible plan” changes the mathematical
statement while leaving compilable code.

## Files

- [`initial.lean`](initial.lean): feasibility without optimization.
- [`final.lean`](final.lean): minimal optimizer and Wasserstein Interface
  slice.
- [`review-timeline.json`](review-timeline.json): two distinct semantic
  failures before pass.

The complete compactness, continuity, attainment, and value-equality proofs
remain hash-bound in the private evidence pack.

Current maintained corpus implementation: [ProbabilityTheory/chapter_08/ex_8_3_4.lean](../../../ProbabilityTheory/chapter_08/ex_8_3_4.lean).
The fixed snapshots above retain their historical scope and hashes.
