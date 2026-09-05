# Strict evidence bridges

`state_evidence_bridge.py` provides a fail-closed, non-semantic authority edge
for exact current MAT bundles. It is not a review workflow. Its final122 batch
emitter is an explicit operator action and publishes only after a complete
snapshot replay; inspection and validation remain read-only.

The closed routes are:

- `kenneth_author_exact_bridge`: an immutable Kenneth author-exact decision;
- `reviewed_mat_sync_reassembly_bridge`: an exact historical recovery, MAT
  review-apply, or explicit author-controlled MAT sync selection.

There is no C route. An item without an existing exact author/review/sync
decision is rejected before state access. Build success, a comparator result,
chat/audit text, commit chronology, or a same-stem file cannot create authority.

Every accepted input fixes `semantic_upgrade=false`, `rubric_upgrade=false`,
and `creates_review=false`; binds full source/target bundles, ordered Lean token
and declaration comparison, proof/support ownership, pinned exact-build and
current direct-consumer evidence; and uses immutable path/hash references.

## CLI

Inspect a prepared fixture/input manifest:

```text
python tools/mat_evidence_bridge.py inspect \
  --input <evidence_bridge_input.json> \
  --source-repo <source-repository> \
  --target-repo <pinned-mat-repository> \
  --kenneth-repo <pinned-kenneth-repository>
```

`validate --receipt ...` replays a single-item receipt against its bound input.
`inspect-final122` is read-only. `emit-final122-batch` captures the complete
indexed evidence graph into content-addressed immutable snapshots, replays it,
and atomically publishes one no-replace batch receipt. It never imports state,
builds Lean, creates a review, or changes rubric/head state. The separate
`validate-final122-batch` command replays that snapshot-bound receipt.

## State projection

Migration discovery recognizes both canonical single-item receipts and the
`ProbabilityTheoryFormalization.validated-evidence-bridge-batch-receipt.v1` schema. A batch is fully
replayed and all active MAT targets are checked before its first write; all
bindings are then imported under one transaction/savepoint and one batch import
marker binds the batch hash with the exact item count. A conflict rolls back the
whole batch.
It never writes `reviews`, review metadata, task heads, rubric versions, or
catalog heads.

Typed capabilities remain distinct:

- `author_current_exact_acceptance`;
- `reviewed_source_mechanical_projection`;
- `sync_author_attested_acceptance`.

`review_coverage()` continues to mean actual exact semantic-review coverage.
`authority_coverage()` reports typed bridges. Status and bundle-delta output
expose `validated_evidence_bridge` separately, and state validation checks the
binding/route/capability/transformation relationships.

The final A/B index also pins the Kenneth repository root, e638 commit and tree;
rebuild fails closed if that exact repository binding is unavailable. It never
falls back to a different checkout that merely retains the Git object.
