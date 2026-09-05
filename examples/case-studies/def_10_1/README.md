# Case study: `def_10_1`

## What went wrong

This Interface represents sure and almost-sure convergence. The first public
subject compiled, but it mixed an almost-everywhere predicate for an arbitrary
measure with an event predicate requiring `μ E = 1`. Those forms are not
equivalent for a general measure. After that defect was repaired, a later,
stricter review found a second problem: the predicates did not require the
sequence or its limit to be random variables.

The second defect had high fanout. A nonmeasurable function used as both the
constant sequence and its limit satisfied the weakened convergence predicates,
and many downstream files consumed the Interface.

## Review and repair

The retained evidence contains eight semantic-review results:

1. fail: the event form is not a full-measure formulation for arbitrary
   measures and no reusable bridge relates the two exported forms;
2. fail: the owner is repaired, but a direct downstream Interface still uses
   the old event contract;
3. pass: the event/a.e. bridges and 14 direct importers are compatible;
4. fail: a stricter source-domain review detects the missing random-variable
   carrier across a 40-target campaign fanout;
5. pass: the carrier is added and all 39 real consumers are inspected;
6–8. pass: fresh evidence bases rebind the unchanged owner to advancing
   downstream files.

The important behavior is not “more passes.” A pass is tied to a review basis,
prompt/rubric version, subject hash, and downstream evidence. New evidence may
correctly invalidate an older conclusion.

## Files

- [`initial.lean`](initial.lean): compiling Interface without a coherent
  full-measure bridge or random-variable carrier.
- [`final.lean`](final.lean): carrier-preserving a.e., full-event, and
  probability-one Interfaces with reusable bridges.
- [`review-timeline.json`](review-timeline.json): eight curated structured
  verdicts plus private-evidence hashes.
- [`ProbabilityTheory/chapter_10/def_10_1.lean`](../../../ProbabilityTheory/chapter_10/def_10_1.lean):
  current repository owner.

## Scope

The public export deliberately omits the full source corpus and mutable prompt
pack. “40 targets” is the scope recorded by review round 5, not a general
benchmark result or an accuracy claim.
