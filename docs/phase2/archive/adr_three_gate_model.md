# ADR: Phase2 Three-Gate Authority Model

Status: accepted

## Decision

Phase2 completion authority is split into three gates:

1. Build gate decides only whether the Lean subject builds. Its canonical
   artifacts are `candidate_vN.lean` and `build_result_vN.json`.
2. Review gate is the only proof-status verdict. A valid review must inspect
   source TeX, the Lean subject, `proof_obligations.json`, audit signals,
   classification history, dependency status, downstream/import evidence,
   ledger runtime status, and freshness/hash evidence.
3. Apply gate only lands a passing review. Failed existing-output review records
   repair-required/open-debt evidence by default and preserves official output.
   Quarantine of official output is explicit opt-in maintenance after downstream
   import checks.

## Consequences

`proof_obligations.json`, classification files, audit outputs, and batch-state
JSON remain useful evidence, caches, or reports. They do not independently mark
a task complete and cannot override the latest valid semantic review verdict.

Complex tasks still use obligation-style decomposition when the source proof
has independently reviewable steps. The decomposition is review context, not a
separate runtime completion state.
