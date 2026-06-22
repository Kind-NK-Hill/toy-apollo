# Semantic Review Report for thm_13_14

- Verdict: `pass`
- Proof class: `textbook_proof_completed`
- Completion class: `source_route_proof_completed`
- Needs class normalization: `False`
- Task status: ``
- Confidence: `high`
- Recommended disposition: `accept`
- Cache hit: `False`

## Summary

Pass. The parent/support Lean route is source-route proof complete: the parent keeps the source text and final public theorems, imports the support layer, and the support layer proves the density, Fubini, kernel-integrability, pi-lambda, and final assembly spine at theorem level. The project text/LF hash for both the parent file and official snapshot matches the request-bound candidate/review_subject hash 4c59d11f4a930f4d7b7067dc54142fa246f84334776b057daa4eb0fb9cb29ee8; the differing raw-byte hash is only a CRLF artifact and is not stale evidence under src/toy_apollo/phase2_pack_shared/io.py sha256_text.

## Reviewer Independence

- Role: `independent_read_only_reviewer`
- Read-only: `True`
- Edited candidate: `False`
- Used current request: `True`

## Interface Contract

- Status: `covered`
- Summary: The output-health parent/support split preserves public names and final theorem statements semantically. The support theorem thm_13_14_from_intervalFubini_piLambda is public and callable by the parent. The parent retains thm_13_14 and thm_13_14_identity with source-facing assumptions and conclusions, and it does not expose proof-step packages as public final theorem premises.

## Proof Obligations

- Status: `covered`
- Summary: All five obligations in proof_obligations.json were checked against the split parent/support files. The definitional obligation is not applicable as a theorem-level proof contract. The four proof obligations have theorem landings with verified proof contract fields and no public-premise relocation in the final public theorem statements.

## Downstream Adequacy

- Status: `covered`
- Summary: No direct downstream consumers are listed in the review context. Existing importers of ToyApollo.Output.thm_13_14 still receive the support declarations transitively through the parent import.

## Forbidden Weakenings

- `not_present` `unnamed`:
- `not_present` `unnamed`:
- `not_present` `unnamed`:

## Findings

- No findings reported.
