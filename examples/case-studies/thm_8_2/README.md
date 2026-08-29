# Case study: `thm_8_2`

## What went wrong

The initial theorem statement was correct and the proof compiled. It selected
Mathlib's already-constructed product measure, invoked its rectangle theorem,
and used uniqueness.

The bound task, however, was proof-bearing: its mathematical route constructs a
set function, proves the measure axioms, extends it to a measure, and only then
uses uniqueness. Calling the finished library object proved the final
proposition but omitted the requested construction spine.

## Review and repair

1. Fail: `adapter_only_shortcut`.
2. Repair defined the fibre set function, proved empty-set and disjoint-union
   laws, and constructed the measure with `Measure.ofMeasurable`.
3. The rectangle formula was proved for that independently constructed object.
4. `Measure.prod_eq` was used only afterward as a reusable uniqueness bridge.
5. Pass: a downstream real-carrier product example consumed the resulting
   `ExistsUnique` Interface.

This case distinguishes proposition truth from proof-route fidelity. That
distinction is important when the project is intended to expose how a
mathematical construction works, rather than merely restate a library theorem.

## Files

- [`initial.lean`](initial.lean): finished-object shortcut.
- [`final.lean`](final.lean): checked set-function construction followed by
  uniqueness.
- [`review-timeline.json`](review-timeline.json): fail and two hash-bound
  passes.

Both snapshots compile independently and omit the textbook excerpt.
