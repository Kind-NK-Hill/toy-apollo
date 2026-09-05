# Explain review invalidation and test target identity

Review requests still use the complete existing `review_basis` hash. Diagnostics
explain which inputs changed; they do not authorize reuse, change a cache key,
relax `review-apply`, or rewrite historical evidence. The existing narrowly
scoped retirement compatibility rule is unchanged.

## Inspect two saved inputs

```powershell
python tools/review_basis_pilot.py --before path/to/semantic_review_input_v1.json --after path/to/semantic_review_input_v2.json
```

Either input may also be a bare basis JSON object. The tool reads only the two
explicit files. It writes JSON to stdout, or to a caller-specified `--output`
path. Its comparison reports changed JSON paths and these diagnostic dimensions:

| Dimension | What is observed |
|---|---|
| `target_context` | Source content, task metadata, ownership and declaration names |
| `subject_bundle` | Complete subject-file hashes, imports and candidate/output identity |
| `dependency_bundle` | Dependency identity, existence and complete file hashes |
| `environment` | Lean toolchain, Lake manifest and Lake configuration |
| `review_evidence` | Audit, classification, route criteria, downstream evidence and build receipt hash |
| `runtime_mirrors` | Ledger statuses, confirmation timestamps and operational file locations |
| `unclassified` | Other inputs, including future top-level fields |

Every input leaf, including empty containers, contributes to one fingerprint.
No field is discarded. These labels explain changes, not their significance:
a state change may be important and still requires the existing gate. Whole
dependency-file hashes cannot tell whether a definition or only a proof changed.
`target_context` is therefore explicitly **not a frozen goal identity**.

At the production basis rejection point, the existing error now includes the
changed dimensions. Earlier rejection points (a changed subject, an altered
request hash, missing evidence) retain their specific errors. The comparison
command supports deeper inspection without adding generated files to prompt
packs or the state database.

For a promoted candidate replay, the rejection compares the current basis hash
to the post-apply receipt. That receipt stores a hash, not a second full basis.
The diagnostic therefore labels its dimensions as changes from the **original
request**; it does not claim to localize changes from the post-apply state.

## Run the bounded identity experiment

```powershell
python tools/review_basis_pilot.py
```

This executes seven deterministic probes against an explicitly supplied target
manifest. The target consists of a declaration, its definition dependency map,
and its toolchain; proof bytes, review evidence and runtime state are separate.

| Probe | Identity that changes |
|---|---|
| No change | None |
| Runtime status | Runtime state |
| Proof text only | Proof version |
| Declaration | Target |
| Definition dependency | Target |
| Toolchain | Target |
| Review observation | Review evidence |

The checked-in [identity report](../examples/review-basis-pilot/identity-check.json)
was produced by this command with `--output` and all seven checks passed. The
fixture uses built-in natural numbers and explicit declaration text. It does
not extract declarations from Lean, elaborate a dependency closure, attest a
new theorem, estimate historical invalidation rates, or measure model quality.
The declaration-change probe only checks identity and does not claim its old
proof still proves the new goal.

## Decision boundary

The implemented result is observability plus a reproducible identity-design
check. Promoting target identity into an authority or caching policy would
require an elaborated declaration/definition closure, explicit source and
proof-route contracts, and independent validation that the proposed reuse does
not miss semantic changes. This experiment alone does not justify that change.

The separate [prospective review comparison](review_comparison_pilot.md)
prepares matched-budget ordinary and blind-translation-assisted review inputs.
Its pending human adjudications are not supplied by historical PASS records.

## Verification

```powershell
python -m unittest tests.test_review_basis_diagnostics tests.test_phase2_review_request tests.test_phase2_review_apply
```

The focused tests cover unknown fields, type changes, operational state versus
dependency bytes, immutable input hashes and the manifest requirements. The
existing request/apply regression tests continue to reject changed source,
toolchain, subject and dependency evidence and preserve permitted historical
retirement replay.
