# Workspace State

This page describes the complete local workspace and its evidence contract.
The public release omits the source catalog and operational database; use the
[development guide](development.md) for public-clone checks and the isolated demo.

The workspace has one operational state database, normally resolved at the
sibling `ProbabilityTheoryFormalization-artifacts/state.sqlite3` path. Runtime
settings and explicit environment overrides determine its actual location;
`formalize --status` reports the resolved roots without changing state.

SQLite is a protected, rebuildable index. Git history supplies repository
identity; immutable review, build, apply, transformation, and typed-binding
artifacts supply evidence. A database row does not create review authority.

## Current catalog and corpus

`src/formalization_engine/task_catalog.py` loads
`data/task_catalog/catalog_policy_v2.json`. Its pinned unified source resolves
plans, `manifest_by_chapter.csv`, and the `ProbabilityTheory/` corpus from this
repository. MAT commit `3acca18c01aebc1fedee47b56e380e0d30b5094c` identifies the
migration origin, not a second active output owner. The local `docs/cutover_v2.md`
records that migration; it is retained outside the public export.

The catalog contains 452 formal tasks, 445 printed-label families, and 584
Lean modules: 452 primary, 108 task-owned support, and 24 shared support modules.
Five printed labels map to multiple task IDs; families do not imply support
ownership. The historical 344-item MAT review-root set remains the named cohort
`mat_manifest_review_roots_20260706`, not the completion denominator.

## Completion and candidate maintenance

Run `formalize state validate --json` for the live catalog verdict. Keep these
dimensions separate:

- a modern-compatible PASS exists for a catalog task;
- that evidence covers the exact current unified subject bundle;
- a typed authority binding covers its declared scope;
- an alternative working-tree candidate needs maintenance.

`worklist` lists candidate, review, integration, and external-PR maintenance.
Its row count is not a count of unfinished required catalog tasks. Compatibility
does not establish exact-bundle coverage, and a build does not establish
textbook statement or proof-route fidelity.

State validation uses the active catalog and its stored subjects; it does not
refresh remotes or declare arbitrary dirty files reviewed. The unified report
places that verdict beside actual repository/worktree observations:

```powershell
formalize state validate --json
python .\tools\workspace_status.py --write --compare-latest-rebuild
```

The report is a projection, not additional review authority. A comparison with
the latest existing check-only rebuild is dated evidence, not a new rebuild.

## Current repository flow

- `ProbabilityTheory/` is the only canonical Lean corpus. Ordinary authoring,
  build, and review preparation use artifact staging.
- Only `review-apply`, after an exact-subject semantic review, may update a
  manifest-resolved canonical path; a failed application restores prior bytes.
- Kenneth and historical MAT repositories are external evidence and review
  sources. Unreviewed external candidates must not be copied into the corpus.
- `Kind-NK-Hill/ProbabilityTheory` remains PR transport. External PR review
  records exact-head coverage; it neither lands content nor changes readiness
  or merge state.
- State commands never commit, push, open, or merge a PR automatically.

The active review/apply rules are in [phase2/agent_review_contract.md](phase2/agent_review_contract.md).
The full completion definition remains in [phase2/status_contract.md](phase2/status_contract.md).

## Evidence binding

A review is bound to the task and complete subject bundle, including task-owned
support, rather than just a filename, branch, commit, or mutable status string.
Applying a review rechecks those inputs and the applicable build and dependency
evidence. Content changes require the corresponding review scope to be checked
again; a validated mechanical transformation can carry compatible evidence but
cannot upgrade an obsolete rubric or invent a verdict.

Typed authority uses the independent `authority_bindings` projection, through
`authority_coverage()` rather than `review_coverage()`. See
[evidence_bridge.md](evidence_bridge.md). A primary-only historical review remains
visible evidence, but cannot authorize a complete bundle without a validated
scope binding or fresh review.

## Operator commands

```powershell
formalize status <task_id>
formalize worklist
formalize state validate --json
formalize state snapshot --output <dataset.json>
formalize state bundle-delta --task <task_id>
formalize state rebuild --check-only
formalize pr-review prepare --task <task_id> --repo wkshum/ProbabilityTheory --pr <number> --checkout <clean-exact-head-checkout>
formalize pr-review apply --request <external_pr_subject.json> --result <semantic_review_result_v1.json>
```

`status` and `worklist` refresh local repository and GitHub observations by
default. `--no-refresh` requests a cached view. Offline observations must be
reported as unavailable, not silently described as freshly verified.

`pr-review prepare/apply` requires a current open draft PR, an exact clean head,
a focused build, hash-bound inputs, and an independent schema-valid review.
Apply rechecks base/head/file identities before recording
`kenneth_pr_exact_head_review` coverage. It does not mutate `ProbabilityTheory/`.
The narrow `pr-review adopt` compatibility path validates previously produced
exact-head evidence under the same boundary.

`state rebuild --check-only` writes and validates a temporary database; it does
not replace the live database. A normal explicit rebuild replaces live state
only after validation and a timestamped backup. Do not use rebuild as an
incidental read operation. Release-audit copies are excluded from evidence
inventory so they cannot displace original evidence.

## Historical interoperability and recovery

The complete pre-correction MAT integration and recovery reference is retained at
`docs/archive/workspace_state_pre_unified_index_20260905.md` in the local workspace,
outside the public export. It preserves old repository flow, historical receipt schemas, transformation and
exact-build tools, recovery rules, and examples. Use those sections only for
their declared pinned historical subjects; the current corpus boundary above
always controls active writes. Historical names in schemas and receipts retain
their original meaning and must not be rewritten merely to match new branding.

Existing `project_ledger.json`, `state_ch*.json`, `reviews_ch*.json`, notebooks,
and prompt-pack metadata remain protected import evidence. After SQLite
activation they are not an alternative current ledger and must not be rewritten
or deleted as cleanup. The local `docs/workspace_inventory.md` describes the
current report and preservation policy; publication boundaries are documented in
[repository_scope.md](repository_scope.md).
