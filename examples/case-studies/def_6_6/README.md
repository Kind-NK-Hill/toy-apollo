# Case study: `def_6_6`

## What went wrong

An early review passed an Option-valued complex integral because it appeared to
preserve the componentwise formula and an explicit `none` branch. A later
prompt-v11 review tested the real support Interface more strictly and reversed
that conclusion.

The real predicate required finite positive and negative lower integrals but
omitted measurability. Worse, its real value remained publicly callable without
an integrability proof, and `EReal.toReal` could totalize a non-finite result.
The code could therefore expose a value where the mathematical Interface says
the integral is undefined.

## Review and repair

1. Prompt v9 passed the initial candidate.
2. Prompt v11 reviewed the same candidate hash and failed it with
   `definition_interface_failed`.
3. Repair removed the custom totalized real support layer.
4. The final gate uses standard `Integrable` for both components, retains
   `Option ℂ`, and proves agreement with the complex Bochner integral.

This case demonstrates that a pass is scoped to its rubric and evidence basis.
It is not an immutable label attached to a file.

## Files

- [`initial.lean`](initial.lean): missing measurability and publicly callable
  totalized value.
- [`final.lean`](final.lean): guarded Option Interface and standard bridge.
- [`review-timeline.json`](review-timeline.json): pass → fail → pass on
  hash-bound subjects.

The files are sanitized Interface slices, not the complete private candidates.
