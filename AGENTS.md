# Toy Apollo Agent Contract

This is the canonical root contract for coding agents working in `toy-apollo`.

If this file conflicts with older notes, trust current runtime code and the rule files under `.claude/rules/`.

## Always Do

- Keep active execution under `python run_chapter.py --phase {0,1,2}`. Phase 3 remains only as a deprecated migration error, Phase 4 remains only as an unavailable error, and both exit nonzero.
- Keep `python run_chapter.py --status` strictly read-only. Its resolved roots describe only the current process, not an active campaign's global authority.
- Use `python run_chapter.py status <task>` or `worklist` for live derived repository/review/PR state; these refresh GitHub by default and never commit, push, open, or merge a PR.
- Use `python run_chapter.py pr-review prepare/apply` for an exact Kenneth PR head. This path records external review coverage only; it never lands the candidate in Toy output or changes PR readiness/merge state.
- Treat `.claude/rules/10-phase-runtime.md` as the phase behavior source of truth before making any phase-routing decision.
- Prefer active package paths under `src/toy_apollo/*` for new code.
- Treat `toy-apollo-artifacts/state.sqlite3` as the workspace operational state described in `docs/workspace_state.md`. Legacy `project_ledger.json` is protected, frozen import evidence after SQLite activation.
- Remember that must-protect is not the same as must-track: important runtime/provenance files may be ignored by Git while still being protected from deletion or cleanup.
- Validate changes with the smallest relevant check before finishing.

## Repository Flow (Hard Boundary)

- Active formalization code flows from `ToyApollo/Output` to the
  `MAT3280-formalization-output` refinement repository only. Reviewed MAT code
  does not flow back into `ToyApollo/Output`.
- Kenneth's `wkshum/ProbabilityTheory` is bidirectional only with MAT: copy an
  exact current Kenneth file into a MAT review branch, review/repair it there,
  then return the accepted MAT version through a PR branch.
- Never copy, port, or merge an active Kenneth candidate into
  `ToyApollo/Output`. Review tools may run from this checkout, but that does not
  make ToyApollo the owner of the candidate.
- `Kind-NK-Hill/ProbabilityTheory` is PR transport only. It is not a refinement
  repository or an additional source of truth.
- Frozen Kenneth snapshots under provenance/history paths are read-only
  evidence, not active imports and not authorization for Kenneth-to-Toy code
  flow.

## Phase Map

- Phase 0:
  - `pack` prepares ingestion materials from source PDFs/pages
  - `validate` checks `draft_input.tex`
  - `apply` writes cleaned `inputs/<source>.tex`
- Phase 1:
  - `pack` prepares `phase1_prompt_packs/<source>/`
  - agent/human writes `draft_plan.json`
  - `apply` validates the draft and writes `plans/*_plan.json`
  - register discovery state in the ledger
  - the middle `draft_plan.json` authoring step is not a CLI mode; CLI supports only `--phase1-mode pack` and `--phase1-mode apply`
  - CLI `apply --input` points to the source `.tex` or `inputs/` directory, not to `phase1_prompt_packs/<source>/draft_plan.json`
- Phase 2:
  - before any authoring, review, repair, hard-failure decision, or chapter/task-set batch, use the repo skill `.agents/skills/toy-apollo-phase2-entrypoint/SKILL.md`; if the Codex skill system has not auto-loaded it, read that file manually and follow its entry report before task-specific work
  - proof-fidelity verdicts are governed by `docs/phase2/status_contract.md` and `docs/phase2/review_criteria.md`; do not treat Lean build success, `#print axioms` cleanliness, ledger cleanliness, audit cleanliness, or classification cleanliness as textbook proof completion
  - `#print axioms` cleanliness is only a proof-dependency-debt check for checked declarations; it does not prove source fidelity, human validation, or semantic completion. For detailed proof-status semantics, follow `docs/phase2/status_contract.md`.
  - default authority is three-gate: build gate only proves technical build readiness; review gate supplies a strict semantic verdict and proof class; apply gate lands clean completion only when `phase2_status=pass`
  - CLI completion [active phase=2]: `pack -> build-check -> review-now -> review-apply`
  - for chapter-wide or task-set work, start with `batch-plan`; use `--batch-task-kinds theorem,definition --batch-limit 15 --batch-workers <n>` for a non-Problem worker queue, and use `batch-run --batch-max-actions 1` only as a bounded dispatcher over existing review/auto-loop actions
  - CLI modes [active phase=2, non-default examples]: `batch-plan`, `batch-run`, `review-pack`, `review-existing`, `review-support`, `review-existing-queue`, `review-fix`, `debt-fix`, `auto-loop`, `verify`, `audit`, `soft-pack`, `soft-apply`; these modes do not independently decide clean completion
  - `soft-pack` and `soft-apply` are the Problem soft-dependency special case inside Phase 2
- Phase 3:
  - CLI modes [deprecated phase=3]: `soft-pack`, `soft-apply`
  - old Phase 3 entries must exit nonzero and report the two Phase 2 migration commands
  - ordinary failed local tasks stay in Phase 2 review/repair workflows
- Phase 4:
  - unavailable; the compatibility entry exits nonzero
  - do not document a successful no-op, manual ledger update, or automated closeout path

## Key Boundaries

- Do not touch high-risk protected state unless the user explicitly scopes that exact path: ledger files, Chapter 1-8 outputs, retired bridge/provider state, `dependency_decisions/`, prompt packs, and `.claude/worktrees/`.
- `soft-apply` means apply selected soft imports to the ledger and soft-dependency pack artifacts.
- `soft-apply` does not call an external provider, does not generate execution batches, and does not perform a Lean verification gate.
- Removed Phase 3 provider and post-processing artifacts remain protected local/historical state, not active workflow inputs.
- Do not describe AI-generated Lean, docs, review files, prompt-pack contents, or audit artifacts as handwritten by the user unless local authorship evidence explicitly proves it.

## Recommended Routing

- Problem soft-dependency workflow:
  - `--phase 2 --phase2-mode soft-pack`
  - operator writes the selection JSON
  - `--phase 2 --phase2-mode soft-apply`
- If the task is about prompt-pack formalization, build failure, semantic review failure, or Problem soft-dependency selection, route through Phase 2 modes, not Phase 3.
- The Phase 2 entry skill is a routing checklist, not a second policy source; it points agents back to this contract and the Phase 2 docs before execution.
- Phase 2 Codex semantic review workflow:
  - task-set routing view: `batch-plan`
  - non-Problem worker queue: `batch-plan --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers <n>`
  - bounded same-session dispatcher: `batch-run --batch-max-actions 1`
  - existing official output: `review-now --review-subject existing`
  - current build-ready candidate: `review-now --review-subject candidate`
  - failed review follow-up: use `auto-loop`; the default repair budget and CLI floor are 15 review rounds and 15 build-check attempts before each review round
  - `review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate` is a diagnostic/manual decomposition of the loop, not a replacement for the loop
  - accepted proof-debt follow-up is maintenance only: `debt-fix -> review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate -> review-apply`
  - same-session orchestration: `auto-loop`
  - current default workflow: `docs/phase2/workflow.md`
  - `review-pack` / `review-existing` are low-level prepare-only modes and should not be presented as the preferred Codex operator path.
- If `ToyApollo/Output/<task_id>.lean` is newer than and differs from the latest
  `draft.lean` / `candidate_vN.lean`, the candidate review target is stale.
  Do not build-check or review that stale candidate. Review the official output
  with `review-now --review-subject existing`, or intentionally sync the output
  into `draft.lean` and rerun `build-check`.

## Codex Review Contract

- Before chapter-wide review or state reconciliation, investigate each task's
  exact current status and actual formalization route. Record the textbook
  claim, exact subject/hash that was reviewed, review verdict/class/evidence,
  current Toy/MAT/Kenneth subjects, and any drift between them.
- For a theorem, "actual proof route" means the proof spine that Lean really
  checks: principal Mathlib theorem or construction, locally proved helpers,
  task-owned support files, important premises, and downstream declarations
  that consume the result. For a definition/example/problem, record the
  corresponding construction/API or solution route. Do not infer this route
  from filenames, imports, comments, build success, or a stored `pass` alone.
- Treat `review_scope_rebind_required` as a request to investigate bundle
  coverage, not as proof failure and not as permission for automatic rebind.
  Decide mechanical rebind versus fresh semantic review only after comparing
  the reviewed route and bundle with the exact current route and bundle.
- For chapter-wide or task-set Phase 2 work, prefer Codex durable goals (`/goal`) when the
  current Codex client supports them.
- Use `/goal` for requests that require continuing across many build/review/repair iterations,
  such as completing all non-remark/non-problem tasks in a chapter.
- The durable goal must include explicit stop conditions: `completed`, `hard_failure`,
  `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption.
- If `/goal` is unavailable, create an explicit local batch state/checklist and run a pre-final
  guard before ending the turn.
- `review-now`, `review-fix`, and `auto-loop` are agent-assisted composite actions.
- `review-apply` remains the only step that lands a Codex semantic-review result.
- Failed existing-output review must preserve official output by default; quarantine is explicit opt-in maintenance after downstream import checks.
- `auto-loop` is not an unattended reviewer/author daemon.
- Semantic review is an independent read-only role unless a document explicitly
  declares a prepare-only non-review action. In active auto-loop repair,
  the authoring agent must delegate reviewer work to a separate reviewer
  subagent or configured reviewer runner, and the review result must include
  `reviewer_independence`.
- Build-fail and review-prepared states are not normal waiting points; the current Codex agent continues in the same session.
- Pre-final guard: if `current_auto_loop_status = active`, do not end the turn with a completion-style summary unless the ledger also shows a documented stop reason.
- The documented stop reasons are only `completed`, `freshness_error`, `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption.
- Needing a substantial semantic rewrite, wanting to summarize current blockers, or waiting for the current Codex agent to perform reviewer/repair work are not stop reasons.
- `nonprogress` is a semantic stop reason, not a generic build stop.
- Only stop the same-session loop on `completed`, `freshness_error`, `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption.
- For proof-bearing tasks, adapter/debt decisions, complex decomposition, hard-failure admission, and public proof-package rules, follow `docs/phase2/status_contract.md` and `docs/phase2/review_criteria.md`; prompt-pack mirrors, clean ledgers, and successful builds are not substitutes for that contract.
- Before inventing a new proof obligation, bridge, or foundation API, search existing `ToyApollo/Output`, bridge/foundation files, ledger state, dependency decisions, plans, and Mathlib; reuse or repair metadata before adding new scaffold.
- Timed-out or manually aborted build/review runs without a canonical result file are mechanism blockers, not substantive proof failures; record them and continue with a narrower diagnostic.
- When the user asks to review an existing chapter, section, or ordered task set, interpret that as a same-session self-driving existing-output batch review unless the user explicitly asks for prepare-only behavior.
- In chapter-wide or task-set Phase 2 goals, a hard-stopped task makes its hard-dependency downstream tasks dependency-failed for that goal; mark/skip those blocked tasks and continue with independent tasks instead of stopping the whole goal.
- `COMPLETED_WITH_PROOF_DEBT` is terminal only for the debt-bearing task. Do not consume it as a clean hard or selected soft dependency; downstream tasks are `DEPENDENCY_PROOF_DEBT` until `debt-fix` discharges the accepted debt and the blocker lands cleanly.
- In that existing-output batch mode:
  - use `review_subject=existing`, not `current`
  - process tasks in deterministic `block_id` order
  - do not stop after `review-now`, build failure, or a prepared review request; the current Codex agent continues the author step or delegates the read-only reviewer step in the same session
  - for pass results, continue to `review-apply` automatically
  - for fail/inconclusive results, run `review-apply` only to record the failed review and repair request, then continue through `review-fix -> build-check -> review-now --review-subject candidate -> review-apply`; do not quarantine existing official output by default
- Only treat `review existing` as prepare-only when the user explicitly asks to inspect or prepare review materials without landing/apply behavior.
- When the user asks to "review existing", "review pack", or "review now" in the Codex path, do not stop at `codex_handoff_pending` unless the user explicitly wants prepare-only behavior.
- When the user asks to continue after a failed semantic review, do not rerun `review-existing` on the rejected object; route through `review-fix` and the build loop.
- When the user asks to repair to completion, naming a precise missing lemma, bridge theorem, API, or source-route gap is not a terminal result; it is the next target inside `auto-loop`.
- When `auto-loop` is active, ledger runtime metadata is the only live loop state source; `metadata.json`, `context.md`, `failure_summary.md`, and `operator_prompt.md` are mirrors.
- For ad hoc single-task review requests, if the user does not explicitly ask to apply the review result, stop after the reviewer result is generated and report the verdict plus the result path.
- The explicit single-task prepare-only rule above does not override the existing-output batch rule; chapter/section/task-set `review existing` requests default to landing/apply behavior unless the user asks otherwise.

## Ask First

- Deleting or bulk-moving runtime outputs, prompt packs, logs, or historical plans.
- Changing ledger status names, plan JSON schema, or stable CLI flags.
- Reworking directory layout for `ToyApollo/Output`, `output_lean_files`, or artifacts sync.
- Reintroducing retired external-provider behavior or adding new external service dependencies.

## Never Do

- Commit secrets, tokens, or `.env` files.
- Treat archive notes as runtime truth unless active code implements them.
- Use `plans/unsolved_tasks.json` as the default soft-dependency source of truth.
- Describe `soft-apply` as external-provider execution or as a Lean acceptance gate.
- Describe removed Phase 3 provider/post-processing tracks as active workflow.
- Reformat the repository by hand in agent prompts; use dedicated tooling when formatter/linter policy is added.

## Repo Map

- Runtime entry: `run_chapter.py`
- Active CLI: `src/toy_apollo/cli/app.py`
- New package home: `src/toy_apollo/`
- Root-level `src/*.py` modules are retained only where active package code imports them; old direct-generation/orchestrator modules are not a supported runtime layer.
- Lean output module root: `ToyApollo/Output`
- Runtime state and generated outputs: artifact-rooted paths from `src/toy_apollo/core/settings.py`

## Minimum Verification

- `python run_chapter.py -h`
- `python run_chapter.py --status`
- `python tools/check_repo_hygiene.py`
- `lake build ToyApollo.Output.<block_id>` for any touched Lean-facing task path

## Progressive Disclosure

Read only the rules needed for the task:

- `@.claude/rules/00-repo-boundary.md`
- `@.claude/rules/10-phase-runtime.md`
- `@.claude/rules/20-artifacts-and-ledger.md`
- `@.claude/rules/30-security-secrets.md`
- `@.claude/rules/40-folder-playbooks.md`

Then read the nearest folder-level `AGENTS.md` before editing inside that subtree.
