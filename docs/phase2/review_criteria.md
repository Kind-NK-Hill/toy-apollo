# Semantic Review Criteria

Semantic review is an independent textbook-fidelity review. It is not a build
check, audit pass, classification check, or ledger check.

A valid review must:

- be performed by an independent read-only reviewer;
- bind to the current review request, prompt version, rubric version,
  candidate hash, review-basis hash, and review subject;
- inspect the source TeX and the Lean subject directly;
- map source claims to Lean declarations, assumptions, and conclusions;
- preserve the source proof spine at an appropriate abstraction level;
- inspect proof obligations as checklist/context when present;
- inspect audit, classification, dependency, downstream/import, ledger, and
  hash evidence without letting any one of them decide completion;
- check direct downstream consumers when listed;
- reject missing, weakened, public-premise, private-axiom, adapter-only, or
  open-debt routes as clean proof completion;
- state `proof_class` and `completion_class`.

## Pass

A `pass` verdict requires:

- non-empty source claims and claim mapping;
- covered spine alignment;
- covered or not-applicable evidence classes;
- covered interface contract;
- covered downstream adequacy;
- no forbidden weakening;
- proof obligations either covered, not applicable, or explicitly classified as
  non-clean proof debt;
- a `proof_class` that can project to task-level `phase2_status=pass`.

The reviewer verdict alone does not make the task pass.

## Fail Or Inconclusive

Use `fail` or `inconclusive` when:

- the source claim is missing or weakened;
- a source proof step is hidden in an assumption;
- a public theorem requires a new non-source premise;
- the proof is a Mathlib-backed adapter for a proof-bearing source task;
- the result carries open math debt or proof debt;
- direct downstream consumers would need extra assumptions;
- freshness/hash evidence is stale or inconsistent.

Failed existing-output review does not quarantine official output by default.
It records repair-required evidence.
