# Case study: `def_8_5`

## What went wrong

The source definition is total variation distance between two probability
measures. The initial Lean subject compiled, but its public Interface accepted
arbitrary measures. That was not a harmless generalization: infinite event
masses pass through `ENNReal.toReal`, and an unbounded real supremum can hit a
fallback value. The implementation could therefore return a misleading value
outside the source domain.

## Review and repair

1. The existing output compiled.
2. Semantic review failed with
   `definition_interface_semantic_mismatch`: the probability-measure domain
   was absent from the Interface.
3. A repaired candidate added `IsProbabilityMeasure` guards and compiled.
4. Semantic review failed again with
   `definition_interface_downstream_migration_incomplete`: two direct
   consumers did not yet supply the required evidence.
5. The consumers were migrated and checked against the exact candidate.
6. A fresh, hash-bound review passed as `textbook_definition_completed`.
7. A later review of the landed official output confirmed the same result.

This case shows three separate claims:

- build gate: the Lean subject elaborates;
- review gate: the Interface is source-faithful and downstream-usable;
- apply gate: only a valid `phase2_status=pass` may land completion.

## Files

- [`initial.lean`](initial.lean): compiling but semantically over-general
  Interface.
- [`final.lean`](final.lean): probability guards added to the public
  Interface.
- [`review-timeline.json`](review-timeline.json): curated structured verdicts
  plus private-evidence hashes.
- [`ToyApollo/Output/def_8_5.lean`](../../../ToyApollo/Output/def_8_5.lean):
  current repository owner.

## Scope

The public export omits the mutable prompt, context, local absolute paths,
diagnoser prompts, and complete source corpus. Those remain preserved in the
private evidence plane. The counts and hashes in the timeline are taken from
the retained runtime pack; no performance claim is inferred from this one
case.
