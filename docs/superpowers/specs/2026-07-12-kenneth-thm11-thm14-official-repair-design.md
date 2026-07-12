# Kenneth Theorem 1.1 and 1.4 Official Repair Design

## Authority

Kenneth `wkshum/ProbabilityTheory` commit
`1dc1b65e6eb5fc4c0a8018240d8490add673fa41` is the prioritized candidate
source. A Kenneth declaration becomes ToyApollo official code only after:

1. Kenneth-layout build and axiom/forbidden-token checks;
2. independent source-fidelity semantic review;
3. ToyApollo Phase 2 candidate review and `review-apply` with
   `phase2_status=pass`.

ToyApollo's older Lean files are regression and proof references. They do not
replace newer Kenneth proof bodies merely because they are shorter or already
build.

## Scope

- Repair Kenneth's revised `thm_1_4` while preserving its proof body. Replace
  the unauthorized global `Monotone alpha` premise with source-faithful
  `MonotoneOn alpha (Icc a b)` throughout its public/helper chain.
- Repair the Kenneth `thm_1_1` proof family against the prioritized Kenneth
  Definition 1.2 contract. Preserve the finite-discontinuity proof spine;
  repair namespace, partition, tag-index, and integration boundaries instead
  of replacing the proof with the older ToyApollo theorem.
- Keep already reviewed Kenneth `def_1_3` discrete/continuous RS special cases
  intact and include them in regression verification.
- Do not push Kenneth's remote or overwrite ToyApollo official output before a
  passing Phase 2 apply gate.

## Repair Architecture

Each theorem gets a fresh campaign candidate seeded from the Kenneth file.
Kenneth import paths are translated mechanically to `ToyApollo.Output.*`.
Mathematical edits are restricted to review findings and mechanically necessary
consumer/support repairs.

`thm_1_4` is repaired first because its route is already buildable and its
semantic defect is isolated. `thm_1_1` follows because it requires the complete
support family and an interface reconciliation with Definition 1.2.

The Phase 2 loop is:

```text
pack -> seed Kenneth candidate -> RED build -> repair/build-check
     -> independent review -> review-apply
```

Failed or inconclusive review returns to `auto-loop`; build success alone never
promotes the candidate.

## Acceptance

- `ToyApollo.Output.thm_1_4` and `ToyApollo.Output.thm_1_1` build directly.
- `ToyApollo.Output.def_1_3`, `thm_1_2`, `thm_1_3`, `def_1_4`, and `Main` have
  no regression caused by the repairs.
- Active `sorry`, `admit`, `axiom`, and `native_decide` scans are empty.
- Checked public declarations report no non-standard proof dependency debt.
- Independent reviews map all source claims and proof-spine steps and return a
  pass-compatible proof/completion class.
- `review-apply` records `phase2_status=pass` for both tasks against fresh
  candidate hashes.

