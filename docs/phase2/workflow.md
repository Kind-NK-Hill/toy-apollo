# Phase2 Workflow

This is the current operator workflow for local Phase2 formalization. For proof
meaning and completion classes, use `proof_fidelity_contract.md`.

Responsibility: tell operators which Phase2 mode to run next and how artifacts
flow through pack, build, review, repair, and apply. Non-responsibility: defining
what proof completion means or preserving historical redesign notes.

## Main Path

For ordinary task authoring:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
# edit phase2_prompt_packs/<task_id>/draft.lean
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
```

After review:

- failed candidate: `review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate`;
- accepted candidate: `review-apply`;
- accepted proof debt: `debt-fix -> review-fix -> build-check -> review-now --review-subject candidate -> review-apply`;
- existing official output review: `review-now --review-subject existing`.

`review-pack` and `review-existing` are prepare-only low-level modes. They are
not the preferred Codex path unless the user explicitly asks only to prepare
materials.

Semantic review must be read-only and independent for current repair-loop
candidates. The authoring worker does not review its own candidate. Use a
separate reviewer subagent or configured reviewer runner to write
`semantic_review_result_vM.json`, then immediately continue `auto-loop`.

## Review Target Routing

Use the review subject that matches the object being judged:

- already-repaired official output in `ToyApollo/Output/<task_id>.lean`:
  `review-now --review-subject existing`;
- active candidate repair: edit `draft.lean`, run `build-check`, then run
  `review-now --review-subject candidate`;
- current review request: reuse only when the runtime freshness checks pass.

If the official output is newer than and differs from the latest
`candidate_vN.lean` or `draft.lean`, candidate build/review is a stale-target
error. Do not snapshot or ask a reviewer to judge the old candidate. Either
review the official output with `review-now --review-subject existing`, or
intentionally copy/sync the official output into `draft.lean` and rerun
`build-check` before candidate review.

## Source And Dependency Recording

For proof-bearing tasks, record the inspected TeX span and proof spine in the
task-local artifact that explains the decision, such as
`semantic_review_result_vM.json`, `semantic_review_report_vM.md`,
`failure_summary.md`, or `hard_failure_note.md`.

If an existing output discharges an obligation but metadata is missing, treat
that as metadata repair and surface the declaration in review context before
inventing new scaffold.

Operational classifications:

- `interface_translation` is only for representation mismatch between textbook
  notation, Mathlib, and existing ToyApollo declarations.
- Substantive source mathematics must be proved, classified as open math debt,
  or explicitly placed in the single accepted beyond-book exception.
- `proof_debt_support` is exceptional and auditable; it is not the default path
  for normal tasks and is never equivalent to `proved`.
- When a step has both interface and mathematical content, split the bridge from
  the mathematical obligation.

## Pack Artifact Roles

- `draft.lean` is the live editable work file.
- `pack` initializes `draft.lean`; later pack runs must not overwrite active
  work.
- `build-check` snapshots `draft.lean` into immutable `candidate_vN.lean`.
- `build_result_vN.json` is the authority for whether a candidate is technically
  build-ready. It has no proof-completion authority.
- `operator_prompt.md` is an agent behavior contract, not proof evidence.
- `context.md` is a runtime view; it does not replace source TeX, Lean build
  results, or semantic review.
- `verify_result_vK.json` records verify/audit/review-apply diagnostics; it is
  evidence for review and repair, not proof completion by itself.
- Semantic review artifacts include `semantic_review_input_vM.json`,
  `semantic_review_prompt_vM.md`, `semantic_review_context_vM.md`,
  `semantic_review_result_template_vM.json`,
  `semantic_review_result_vM.json`, `semantic_review_report_vM.md`,
  `semantic_review_request_vM.json`, `review_repair_request_vM.json`, and
  `review_repair_summary_vM.md`.

Before editing `draft.lean`, read the grounding files relevant to the current
state: `context.md`, `failure_summary.md` when present, `proof_obligations.json`
when present, audit results, classification history, dependency/downstream
evidence, ledger runtime status, hash/freshness evidence,
`search_manifest.json` / `search_notes.md`, `imports.lean`, and
`target_stub.lean`. These files guide the next attempt; they do not override the
source TeX or current build/review artifacts.

Mode constraints:

- `pack`, `build-check`, `verify`, `review-pack`, `review-existing`,
  `review-now`, `review-fix`, `debt-fix`, `auto-loop`, and `review-apply`
  operate on exactly one task id.
- `review-apply` requires an explicit `--review-result` path.
- `review-existing-queue` scans official outputs and may be filtered with
  `--tasks`.
- `promote-obligations` is for turning blocking proof obligations into
  first-class ledger child tasks.
- `debt-fix` is only for tasks whose `proof_obligations.json` or ledger
  proof-obligation summary records `accepted_as_proof_debt`.
- `soft-pack` and `soft-apply` accept one or more `Problem` task ids;
  `soft-apply` requires `--selection`.
- The low-level `current` review subject is only a runtime continuation for an
  already prepared request whose freshness checks pass. Operators should choose
  `--review-subject existing` for official outputs or `--review-subject
  candidate` for build-ready candidates.
- `review-pack --candidate ToyApollo/Output/<task_id>.lean` is a compatibility
  alias for existing-output review. External candidate files must go through
  `build-check --candidate` first.

## Semantic Review Gates

Review pass requires:

1. statement fidelity;
2. source proof or construction spine fidelity;
3. interface contract;
4. downstream adequacy;
5. explicit response to the required evidence bundle: source TeX, Lean subject,
   proof obligations, audit, classification, dependency status, downstream
   imports/consumers, ledger status, and hashes.

The required evidence bundle is not a set of independent completion verdicts.
`proof_obligations.json`, classification, audit, dependency status, and batch
state are review inputs. The semantic review result is invalid if it does not
explain them, but none of them may bypass the review verdict.

Statement fidelity includes public-assumption expansion: unfold local
`def`/`structure`/package assumptions, classify extra fields, and reject hidden
strengthening unless it is removed or honestly reclassified.

`statement preserved + downstream usable` is insufficient when the source proof
spine cannot be traced into Lean.

## Complex Tasks

Use Level 2 obligation tracking only when the source proof has independently
reviewable steps, repeated partial progress, downstream-sensitive interfaces, or
temporary scaffold that could hide mathematics. Otherwise keep the ordinary
Phase2 path.

For complex tasks:

- replace generated `source_proof_spine` placeholders with concrete source-step
  obligations;
- include source TeX file/span, complexity reasons, source obligation nodes in
  textbook order, dependencies between nodes, Lean landing plans/status, and
  scaffold classifications;
- record expected theorem-level landings;
- assemble proved obligations into the public theorem;
- do not expose hard obligations as public theorem parameters.

For complex tasks retried after an under-evidenced hard stop, continue until the
task is completed, explicitly interrupted by the user, blocked by a documented
mechanism failure, or one of the two Phase2 failure streak counters reaches 15.
The counters are independent: `phase2_build_fail_counter` counts consecutive
failed build checks before semantic review, and `phase2_review_fail_counter`
counts failed or inconclusive semantic reviews of build-ready candidates.

## Textbook Complete Upgrade Path

For selected hard targets, the normal route is: select target, harden the
contract, extract the source route and public assumptions, produce required
bridge/foundation lemmas, assemble the public theorem, then review and update
classification. Source-route extraction records the intended statement and does
not substitute for proof production.

The active target list is `docs/phase2/textbook_complete_targets.json`. Older
target-selection JSON under `docs/modification_0525_steps/` is legacy evidence,
not the current target source.

This is the normal Phase2 repair loop for selected textbook-completion targets,
not a one-off external proof challenge. A reusable bridge or foundation lemma
landed during bridge/foundation production is an intermediate repair artifact.
After landing it, the same target remains active: return to the task theorem,
wire the bridge into the proof, and continue until the selected public theorem
is assembled, an accepted statement patch is landed, or a concrete hard blocker
is recorded. Do not end a selected-target repair merely because one bridge file
now builds.

For a selected main theorem target, success means `textbook_proof_completed`.
`foundation_lemma_landed`, `bridge_landed`, and `contract_clean` are progress
states only unless the user explicitly asked only for a foundation batch.

If the worker cannot close the selected public theorem in the same repair run,
the report must be one of:

- `statement_patch_landed`: the source-faithful public statement or assumptions
  were actually changed, downstream uses were repaired, and Lean builds;
- `hard_blocked_with_failed_lean_attempt`: the worker made a concrete Lean
  proof attempt, recorded the exact blocker, and identified the missing public
  bridge/foundation dependency.

Do not downgrade a selected textbook target to adapter/open-debt merely because
the first proof attempt found a missing bridge. Build the bridge when it is a
public reusable dependency, then return to the selected theorem in the same
Phase2 repair loop.

For selected textbook-completion targets, reviewer independence is mandatory.
The orchestrator may author Lean locally, but semantic review must be delegated
to a distinct read-only reviewer subagent or configured reviewer runner. A
review result without a valid `reviewer_independence` attestation is not
applyable proof-fidelity evidence.

Files under `docs/modification_0525_steps/` are historical execution evidence.
Do not treat them as policy unless the rule also appears under `docs/phase2/`.

## Required Checks

Use the smallest relevant checks for the task. Common checks:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
python -m unittest tests.test_phase2_completion_classification tests.test_phase2_clean_debt_surface_audit
```

For draft candidates, prefer the Phase2 `build-check` mode rather than directly
editing official output.

## Review JSON Discipline

When writing or repairing a semantic review result:

- use the current `semantic_review_result_template_vM.json`;
- follow `reviewer_schema_hints` from the template when filling a pass result;
- keep binding fields and hashes unchanged;
- use parent obligation ids exactly as shown in the request;
- include one `downstream_adequacy.consumers_checked` entry for every direct
  downstream consumer listed in the review input;
- use schema status values only;
- if `review-apply` says the basis changed, discard the result, run fresh
  `review-now`, write a new result, and apply immediately;
- if `pack` reports a hard dependency still carries proof debt, clear the
  dependency first instead of editing a stale pack to bypass the gate.

## Build Triage

After a failed candidate build, inspect the generated build artifacts before
editing again:

- `build_result_vN.json` for the authoritative build status;
- `build_feedback.txt` for the user-facing compiler feedback;
- `failure_summary.md` for primary failure kind, blocking symbols, and repair
  hints when present.

Common failure kinds include `missing_import`, `unknown_identifier`,
`missing_local_foundation_lemma`, `unresolved_elaboration`,
`noncomputable_required`, `temp_build_failed`, and `final_build_failed`. Repair
the primary cause rather than regenerating an unchanged candidate or using
semantic review to bypass a build failure.

`missing_local_foundation_lemma` means the candidate called a theorem/lemma name
that looks local to the current task, usually prefixed by the task id, but never
proved it. This is proof work inside the current task or a real import lookup;
it is not a valid reason to stop as externally blocked.

If a dependency is missing from `project_ledger.json` but a buildable official
output exists under `ToyApollo/Output/<task_id>.lean`, treat it as metadata
repair evidence, not proof that the dependency is unavailable.

## Stops

Do not stop after preparing a review when the user asked for a chapter, section,
or ordered task-set review. Continue through apply/repair unless the user asked
for prepare-only behavior.

Valid same-session stop reasons include: completed, freshness error, hard
failure, nonprogress, max rounds, build budget exhausted, or explicit user
interruption.

For a proof task, `hard_failure` is valid only after the source/dependency
evidence required by `proof_fidelity_contract.md` is recorded and the applicable
retry threshold is reached: `phase2_build_fail_counter >= 15` or
`phase2_review_fail_counter >= 15`. Do not add build and review failures
together. Timed-out or aborted runs without canonical result files are mechanism
blockers, not proof failures.
