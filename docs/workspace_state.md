# Workspace State

The workspace has one operational state database:

```text
D:\Grad_Study\Practimum\Formalization\toy-apollo-artifacts\state.sqlite3
```

It is local runtime state, not a Git-tracked report. Git commits and GitHub PRs
remain the authority for repository history; immutable review/build JSON files
remain the authority for their evidence. SQLite only joins those facts and
derives the current worklist.

## Repository Flow

- New Phase 2 candidates are reviewed against, and applied to, their single
  configured MAT `ProbabilityTheory/chapter_XX` target. ToyApollo stores the
  candidate and immutable review/build evidence, not a second Lean result.
- A Kenneth file that needs review is copied into a MAT review branch. The
  accepted MAT version returns to Kenneth only through an explicit PR.
- Provisionally, when Kenneth already has the file, the latest Kenneth `main`
  file supplies textbook wording and public interface while the reviewed MAT
  file supplies proof evidence to be reconciled into it. This operating rule
  may change after author feedback; changing it does not rewrite old evidence.
- Kenneth candidates never enter a ToyApollo Lean-output tree.
- The PR transport fork is not another refinement repository.
- No state command commits, pushes, opens a PR, or merges automatically.

## State Rules

- A review is bound to `task_id + subject bundle hash`, not to a filename,
  branch name, mutable status string, or Git commit alone.
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
python .\run_chapter.py state rebuild --refresh-remotes
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
with authority scope `kenneth_pr_exact_head_review`. It does not alter the MAT
formal output, push a branch, mark a PR ready, or merge it.
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

`state rebuild` scans immutable evidence and repository heads into a temporary
database, runs an integrity check, backs up any existing database, and then
replaces it. A legacy review result is historical by default; it receives apply
authority only when its file, canonical result hash, input hash, and subject
hash match a recorded review-apply receipt. External PR apply receipts are also
rediscovered: rebuild rechecks their semantic review, canonical classification,
builder evidence, reviewer-independence attestation, and complete subject
manifest before restoring eligible exact-head coverage.

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
