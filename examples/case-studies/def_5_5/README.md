# Case study: `def_5_5`

## What went wrong

The initial subject compiled because it exported Mathlib's `iIndepSet`
directly. That did not make it a source-faithful definition: the public
Interface hid the finite-subfamily equation being formalized, and the retained
review basis supplied no verified equivalence bridge or explicit probability
and measurability domain.

## Review and repair

1. Review failed with `interface_bridge_incomplete`.
2. The owner was redesigned as the finite intersection/product equation.
3. A reusable theorem bridged that textbook-first predicate to `iIndepSet`
   under the actual probability-space and measurable-event assumptions.
4. Three successive passes checked the owner, then advancing direct consumers,
   without weakening the definition or moving premises into a task-shaped
   wrapper.

This is an Adapter-depth case: a one-line alias is a shallow Module when its
hidden contract is the central mathematical claim. The repaired Interface is
explicit; Mathlib remains behind a checked bridge.

## Files

- [`initial.lean`](initial.lean): compiling library alias.
- [`final.lean`](final.lean): textbook-first definition plus reusable bridge.
- [`review-timeline.json`](review-timeline.json): four hash-bound reviews.

The Lean files are sanitized Interface slices. Full prompts, source excerpts,
consumer snapshots, and mutable pack pointers remain private.
