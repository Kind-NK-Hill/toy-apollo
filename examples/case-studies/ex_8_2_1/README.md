# Case study: `ex_8_2_1`

## What went wrong

The initial candidate compiled and proved a correct rectangle calculation, but
for a product measure on `ℕ × ℝ`. The bound mathematical contract used a
real-valued discrete law and a product on `ℝ × ℝ`, together with its Borel and
support Interfaces.

This was not a missing lemma. It was a carrier decision with two mutually
exclusive outcomes:

- preserve the real-carrier contract and build a reusable `ℕ → ℝ`
  pushforward bridge; or
- explicitly change the accepted mathematical contract to the intrinsic
  carrier.

Silently keeping the first proof while describing the second object would be
mathematical statement drift.

## Review and repair

1. Review failed as
   `partial_formula_proof_unbridged_carrier_encoding`.
2. Diagnosis marked `statement_mismatch=true`, `route_wrong=true`, and
   `local_repair_allowed=false`; an owner decision was required.
3. The source-faithful real-carrier option was selected.
4. The repaired subject exported the pushforward law, real support, rectangle
   and concentration APIs, and consumed the product-measure theorem.
5. A fresh review passed on the new candidate hash.

## Files

- [`initial.lean`](initial.lean): valid formula on the wrong carrier.
- [`final.lean`](final.lean): minimal real-carrier Interface slice.
- [`review-timeline.json`](review-timeline.json): fail → owner decision →
  pass evidence.

The full final proof contains additional uniqueness, singleton-mass, support,
and dependency-route details; they remain in the private evidence plane.
