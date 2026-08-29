# Workspace State

The workspace has one operational state database:

```text
D:\Grad_Study\Practimum\Formalization\toy-apollo-artifacts\state.sqlite3
```

It is local runtime state, not a Git-tracked report. Git commits and GitHub PRs
remain the authority for repository history; immutable review/build JSON files
remain the authority for their evidence. SQLite only joins those facts and
derives the current worklist.

Strict evidence bridges use the independent `authority_bindings` projection;
see `docs/evidence_bridge.md`. These rows never create target reviews or
upgrade prompt/rubric/catalog-head state. Callers use `authority_coverage()`
rather than interpreting them as `review_coverage()`.

The database is therefore disposable in principle but protected in practice:
it must be reproducible from the pinned catalog and immutable evidence before
replacement. A row in SQLite does not create review authority. It records and
queries authority supplied by validated review/apply/rebind evidence.

## Catalog and Families

The fixed catalog is loaded by `src/toy_apollo/task_catalog.py` from
`data/task_catalog/catalog_policy_v1.json` and pinned ToyApollo/MAT commits. Its
required counts are:

```text
452 formal tasks
445 printed-label families
452 primary task modules
108 task-owned support modules
24 shared support/bridge modules
584 MAT Lean modules in total
```

Five printed textbook labels contain multiple formal task IDs, which explains
the difference between 452 tasks and 445 families. Family membership does not
mean support-file ownership.

The historical 344-item MAT review-root set remains available as the named
cohort `mat_manifest_review_roots_20260706`. It is useful for reproducing the
old 344/344 review statement, but it is not the full task denominator. The
worklist starts from all 452 catalog tasks and left-joins their current state;
missing rows can no longer make tasks disappear.

State validation and rebuild completion require a modern-compatible PASS for
every catalog task. The 344-item cohort is reported only under the named
`historical_metrics.legacy_review_root_compatible_pass` reproducibility metric;
it is not part of, and cannot satisfy, `all_required_pass`.

## Completion Versus Candidate Maintenance

`state validate` is the catalog-completion query. `worklist` is a different
projection: it lists actions for alternative working-tree candidates, review
scope rebinds, promotion queues, integrations, and active runs. A non-empty
worklist does not imply that the authoritative catalog has missing or failed
tasks. Operators and agents must report both scopes explicitly rather than
describing worklist rows as unfinished required tasks.

`state validate` checks the live database against the fixed catalog and its
stored catalog-pinned heads. It does not reinterpret dirty working-tree files
as `mat_main`, and it does not refresh remotes. Display the catalog verdict
beside actual Git/worktree dirtiness with:

```powershell
python .\tools\workspace_status.py --write --compare-latest-rebuild
```

That unified report also keeps compatible PASS, exact current MAT coverage,
typed authority, and candidate maintenance as separate per-task fields.

The CLI therefore prints authoritative catalog completion before candidate
maintenance counts. Its JSON keeps them in separate
`authoritative_completion` and `candidate_maintenance` objects.

## Repository Flow

- New ToyApollo output may be reviewed and promoted into MAT.
- A Kenneth file that needs review is copied into a MAT review branch. The
  accepted MAT version returns to Kenneth only through an explicit PR.
- Provisionally, when Kenneth already has the file, the latest Kenneth `main`
  file supplies textbook wording and public interface while the reviewed MAT
  file supplies proof evidence to be reconciled into it. This operating rule
  may change after author feedback; changing it does not rewrite old evidence.
- Kenneth candidates never enter `ToyApollo/Output`.
- The PR transport fork is not another refinement repository.
- No state command commits, pushes, opens a PR, or merges automatically.

## State Rules

- A review is bound to `task_id + subject bundle hash`, not to a filename,
  branch name, mutable status string, or Git commit alone.
- “Compatible PASS exists” and “current exact-bundle authority” are separate
  queries. For Phase 2, compatibility requires prompt 9, 10, or 11 with rubric
  9 and a PASS verdict. A raw semantic result may not yet have a
  `phase2_status`; an explicit non-pass status is excluded, while apply
  authority additionally requires a successful apply/receipt. A strict
  hash/build/dependency rebind may carry that compatible verdict to an exact or
  mechanically relocated bundle, but it cannot convert an older rubric into
  rubric 9.
- A subject bundle contains the public task file and every task-owned support
  file (for example `thm_1_1_support/**` and `thm_1_1_*.lean`). New review
  inputs hash that full bundle, and review-apply refuses promotion if any bound
  support file has changed or disappeared.
- A verified path-only/mechanical transformation may carry review coverage to
  the transformed bundle. A Lean-token change requires another review.
- `authority_eligible` records that a review passed the apply gate. Whether it
  covers a current head is always derived again from the current bundle.
- Kenneth main records author intent. It is not automatically reviewed MAT
  content.
- MAT current means committed `main`. A reviewed working-tree candidate enters
  the serialized `mat_promotion` queue; it is not treated as MAT main early.
- A PR whose head is older than the latest reviewed local bundle is reported as
  behind. A reviewed MAT bundle with no matching PR is reported as ready for PR.
- Dependent parallel work may pin an explicit dependency candidate, but
  promotion waits for that dependency and revalidates after it lands.
- Offline GitHub refreshes are marked unavailable. Cached remote observations
  are never silently presented as freshly verified.

## Commands

```powershell
python .\run_chapter.py status <task_id>
python .\run_chapter.py worklist
python .\run_chapter.py state rebuild --check-only
python .\run_chapter.py state rebuild --refresh-remotes
python .\run_chapter.py state validate
python .\run_chapter.py state snapshot --output <dataset.json>
python .\run_chapter.py state bundle-delta [--task <task_id>]
python .\run_chapter.py state transformation inspect --task <task_id> --checkout <clean-pinned-MAT-checkout>
python .\run_chapter.py state transformation emit --task <task_id> --checkout <clean-pinned-MAT-checkout> --output-dir <immutable-evidence-dir>
python .\run_chapter.py state transformation emit-batch --task-file <tasks.txt> --checkout <clean-pinned-MAT-checkout> --output-dir <immutable-evidence-root>
python .\tools\mat_catalog_exact_build_batch.py --task-file <tasks.txt> --checkout <clean-pinned-MAT-checkout> --output-root <artifact-root>\exact_builds\<mat-commit> --batch-size 12
python .\tools\mat_catalog_exact_build_batch.py --action-manifest <manifest.json> --checkout <clean-pinned-MAT-checkout> --output-root <artifact-root>\exact_builds\<mat-commit> --batch-size 12
python .\run_chapter.py pr-review prepare --task <task_id> --repo wkshum/ProbabilityTheory --pr <number> --checkout <clean-exact-head-checkout>
python .\run_chapter.py pr-review apply --request <external_pr_subject.json> --result <semantic_review_result_v1.json>
python .\run_chapter.py pr-review adopt --task <task_id> --pr <number> --review <exact-review.json> --classification <classification.json> --builder-evidence <builder.json>
```

`status` and `worklist` refresh local repositories and GitHub by default. Use
`--no-refresh` only when an explicitly cached view is wanted. The older
`python .\run_chapter.py --status` command remains a strictly read-only roots
diagnostic and never creates the database.

`pr-review prepare` is the external-candidate path. It requires the PR to be
open and draft, verifies that the supplied checkout is clean and exactly at the
current GitHub head, runs the focused `lake build` for the task module, and
writes a hash-bound review bundle under
`toy-apollo-artifacts/external_pr_reviews/`. The bundle identity includes the
repository, PR number, base/head SHAs, changed-file set, task-owned GitHub
manifest, primary content hash, and exact-head build receipt.

`pr-review apply` refreshes GitHub again and refuses stale base/head/file sets,
non-draft PRs, changed build receipts, changed review inputs, self-review, and
schema-invalid results. A clean pass is recorded against the exact PR subject
with authority scope `kenneth_pr_exact_head_review`. It does not copy anything
to `ToyApollo/Output`, promote MAT, push a branch, mark a PR ready, or merge it.
Any Lean-token change creates a new PR head and therefore requires a new pack
and independent review.

`pr-review adopt` is a narrow compatibility path for an exact-head review that
finished before `prepare/apply` existed. It accepts only the tracked exact
review, classification-supplement, and builder-evidence schemas; rechecks every
identity/hash/build/independence field against the current open draft PR; then
writes a new apply receipt. It does not convert an ordinary historical Toy/MAT
review into PR coverage. The receipt stores the complete immutable PR subject
manifest so an exact-head pass can be reconstructed without treating a later
repository snapshot as the reviewed subject.

`state rebuild` inventories all registered evidence roots once, hashes and
deduplicates their contents, imports every path as provenance, refreshes pinned
repository heads, and checks the catalog and legacy-cohort invariants in a
temporary database. `--check-only` never replaces the live database. A normal
rebuild replaces it only after all checks pass and first creates a timestamped
SQLite backup. A legacy-schema database is reported as requiring this explicit
rebuild rather than being silently altered by a read command.

A legacy review result is historical by default; it receives apply authority
only when its file, canonical result hash, input hash, and subject hash match a
recorded review-apply receipt. External PR apply receipts are also rediscovered:
rebuild rechecks their semantic review, canonical classification, builder
evidence, reviewer-independence attestation, and complete subject manifest
before restoring eligible exact-head coverage.

`state validate` checks the live database against the pinned catalog.
`state bundle-delta` reports whether each current MAT bundle is already exact,
needs a mechanical rebind, has substantive primary/support changes, or lacks a
compatible review basis; it never grants authority itself. `state snapshot`
serializes the stable analysis dataset and hashes the canonical payload, so two
independent rebuilds can be compared without relying on nondeterministic SQLite
file bytes or ingestion timestamps.

The current snapshot schema is `toy-apollo.analysis-dataset.v2`. It excludes
rebuild-observation timestamps and the redundant `subject_observed` and
`subject_transformed` events. Subjects, transformations, reviews, evidence
paths/hashes, and receipt-import events remain represented. Therefore two
independent databases with the same semantic projection receive the same
dataset ID even when they were rebuilt at different times.

Reviews created before full bundle binding may have a valid apply receipt but
only a primary-file hash. Status reports these as
`primary_only_bundle_mismatch` / `review_scope_rebind_required`. They remain
visible evidence, but they cannot authorize MAT promotion until the support
scope is rebound or freshly reviewed. This distinction prevents both false
"never reviewed" reports and false full-bundle passes.

When an old applied review demonstrably inspected the unchanged task support,
`workspace_review_binding_*.json` stores one narrow, immutable scope-rebind
receipt under `toy-apollo-artifacts`. It must name the eligible basis review,
the exact Toy/MAT manifests, a successful build and forbidden scan, and a
byte-for-byte MAT relocation check. A primary-file change is rejected unless
the receipt is explicitly a verified boundary delta with unchanged public
declarations. Rebuilding SQLite revalidates and imports these receipts; it does
not rewrite the old review artifacts.

Some historical Phase 2 runs completed canonical `review-apply` before the
runtime emitted a standalone rebuild receipt. For that narrow case,
`historical_review_apply_recovery_receipt_*.json` uses schema
`toy-apollo.historical-review-apply-recovery.v1`. Generate it with
`tools/mat_review_authority_recover.py inspect|emit`. The tool is read-only
except for emitting the immutable receipt and never writes SQLite. It
revalidates the versioned result, input, request, rendered prompt, context, and
successful `verify_result` (`mode=review-apply`, applied runner, legal PASS
disposition, successful final build), plus exact subject manifest, modern
prompt/rubric, task-status projection, and reviewer independence. Rescue or
sidecar results, failed builds, altered hashes, invalidation/quarantine, later
conflicting evidence, and dependency drift fail closed. Rebuild restores the
original result as authority only on its original source subject under
`recovered_historical_phase2_review_apply`; this neither invents a new semantic
review nor binds the current MAT target. A separate validated transformation
receipt is still required for any path relocation. Import is intentionally a
clean-rebuild operation: if an older generic review row already occupies the
same result/subject identity, incremental import refuses promotion instead of
rewriting that row in place.

An old `mat.rubric78.review-apply-receipt.v1` with a non-empty
`invalidated_by` is never edited or reactivated. When its p9/10/11+r9 PASS
reviewed exactly the same primary and complete bundle as current MAT main, a
new `resolved_invalidation_recovery_receipt_*.json` may use schema
`toy-apollo.resolved-invalidation-current-exact-recovery.v1`. Generate or
inspect it with `tools/mat_resolved_invalidation_recover.py`; generate the
current direct-import manifest with `tools/mat_current_direct_consumers.py`.
The receipt is fail-closed: it requires the immutable old receipt/result/input,
a current pinned-MAT exact build with a clean forbidden-token scan, the named
invalidator's exact build/scan on that same commit, and exact builds/scans for
every consumer in the current direct-import manifest. Rebuild checks that the
target is still the active MAT head before recording authority under
`resolved_invalidation_current_exact_recovery`. It creates no new semantic
verdict, never clears `invalidated_by`, and retains rejected recovery receipts
as state events.

For a current MAT bundle that differs from an authority-eligible reviewed
bundle only by file paths, `validated_transformation_receipt_*.json` is the
rebuildable authority bridge. Its schema is
`toy-apollo.validated-transformation-receipt.v1`. The receipt binds one task,
the complete source and target subject identities/manifests, the exact source
review identity and evidence hash, the pinned MAT commit, and hash-addressed
build and forbidden-token-scan evidence. Rebuild imports it only after current
MAT heads are refreshed, recomputes the bundle comparison, and records a
`path_relocation` transformation only when the source is an explicit applied
prompt-9/10/11, rubric-9 PASS and the primary hash plus complete content
multiset are unchanged. It never creates a replacement review or upgrades an
old rubric. Primary/support content deltas, non-authority reviews, stale MAT
commits, failed checks, and altered hashes are rejected; the reason is retained
as a `validated_transformation_receipt_rejected` state event.

`state transformation inspect` is read-only. It requires local `origin/main`
to equal the catalog MAT pin, reconstructs the complete pinned Git bundle,
selects only an existing modern authority source, and reports the exact focused
build command. `emit` repeats those checks, requires a clean checkout whose
HEAD equals that pin, runs the focused `lake build` and full-bundle forbidden
scan, and writes three new hash-linked JSON files. It refuses existing output
paths and never updates SQLite; the next explicit state rebuild performs the
independent receipt validation and import.

`emit-batch` performs the same fail-closed checks with one catalog/MAT
inventory pass and one combined `lake build` command over all pending primary
modules. Every task still receives its own subject-bound build, scan, and
receipt JSON under `<output-dir>/<task-id>/`; the build evidence records the
complete module list and the task's own required module. A complete existing
three-file set is skipped only after its hashes, source review, current target,
build command, and scan are revalidated. Partial or mismatched existing
evidence is rejected and never overwritten.

`mat_catalog_exact_build_batch.py` is the review-independent current-MAT build
equivalent for recovery and audit workflows. It accepts explicit tasks, task
files, or action manifests containing `unique_exact_builds`; loads the catalog
and pinned Git subject inventory once; and splits complete task-owned module
sets into bounded combined `lake build` commands. Each task receives exactly one
`<output-root>/<task-id>/exact_mat_build_receipt_v1.json` using schema
`mat.catalog.exact-build.v1`, with the complete task-owned subject manifest,
commit/subject/bundle/primary identities, combined command and logs, explicit
task-module membership, forbidden-token scan, and clean-Lean-tree equivalence.
An existing receipt is skipped only after strict current-subject validation.
Partial directories, mismatches, unexpected sibling files, concurrent output,
and overwrite attempts fail closed. The tool never writes SQLite, Lean,
semantic-review results, or review-apply receipts. Give it a dedicated
`exact_builds/<mat-commit>` root rather than a directory that also contains
direct-consumer manifests, policies, or other recovery artifacts.

When content hashes changed only because a reviewed bundle was moved across
repository module boundaries, the stricter
`validated_boundary_delta_receipt_*.json` channel may be used instead. Its
schema is `toy-apollo.validated-boundary-delta-receipt.v1`; generate or inspect
it with `tools/mat_verified_boundary_delta.py emit|inspect`. The emitter can
consume a validated `historical_review_apply_recovery_receipt_*.json` directly,
so source authority need not already be present in SQLite. It additionally
requires the historical complete-bundle scope binding, both source and target
Git blob manifests, an exact target build/clean-tree/forbidden scan at the
pinned MAT commit, the current direct-consumer manifest plus exact builds for
every consumer, and Kenneth provenance or an explicit author-decision artifact
when a same-task Kenneth file exists.

`author_exact` is not a self-attestation: the tool reads every matching Lean
blob from the pinned Kenneth commit, records its Git/blob/content identities,
and requires an explicit Kenneth-to-target file pairing whose bytes are equal.
The non-exact `mat_retained_reviewed` and `explicit_author_decision` routes must
instead reference hash-addressed, already-existing Gate2, review-apply, or chat
history evidence; a newly authored decision JSON by itself has no authority.

The policy input uses schema `toy-apollo.boundary-delta-policy.v1` and declares
a bijective `file_pairs` list plus the only allowed fully qualified
`module_rewrites`. Validation removes comments and import commands, applies
only those named module rewrites, and requires equal Lean token streams for
every paired file. It also independently hashes an unchanged manifest of all
public declaration prefixes and compares normalized direct imports. This
allows path relocation, import/namespace spelling, documentation/whitespace,
and whole-file reassembly; it does not allow declaration split/merge or proof
body edits. Source-scope formats are handled by an explicit validator registry;
the registered `recovery_subject_exact_scope` route accepts the same validated
recovery receipt only when its source is a non-legacy, fully content-addressed
`review_input_bundle`. That route binds the already-imported recovered review
row directly; it does not invent a scope-rebind review. An unregistered
historical full-bundle layout fails rather than falling back to guessed fields.
Any public contract, mathematical representation, dependency, or
unclassified Lean-token delta fails closed.

The command never writes SQLite or Lean and refuses to overwrite a receipt.
During a clean rebuild, source recovery and scope-review evidence are imported
first, repository heads are refreshed, and the boundary receipt is revalidated
last before recording only a `verified_boundary_delta` transformation. It
does not create a semantic review or change the original prompt/rubric.

Repository-specific filenames do not create new task identities. In
particular, Kenneth's `ProbabilityTheory/chapter_01/thm_1_2_4.lean` is support
owned by canonical task `thm_1_2`, corresponding to ToyApollo's
`thm_1_2_restriction_support.lean`. Path, case, and import-prefix relocation may
inherit an eligible review only with exact transformation evidence and a fresh
build.

## Legacy Files

Existing `project_ledger.json`, `state_ch*.json`, `reviews_ch*.json`, and prompt
pack metadata remain protected evidence. They are imported as scoped history
or compatibility data and are not rewritten after SQLite activation. Tools
that formerly rewrote `project_ledger.json` fail closed when the canonical
database exists.
