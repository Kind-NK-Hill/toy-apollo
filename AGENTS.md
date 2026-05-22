# Toy Apollo Agent Contract

This is the canonical root contract for coding agents working in `toy-apollo`.

If this file conflicts with older notes, trust current runtime code and the rule files under `.claude/rules/`.

## Always Do

- Keep the stable entrypoints working: `python run_chapter.py --phase {0,1,2,3}` and `python run_chapter.py --status`; Phase 3 now reports a migration message, and Phase 4 is currently disabled/no-op.
- Treat `.claude/rules/10-phase-runtime.md` as the phase behavior source of truth before making any phase-routing decision.
- Prefer active package paths under `src/toy_apollo/*` for new code.
- Treat `project_ledger.json` as persistent runtime state, not disposable scratch data.
- Remember that must-protect is not the same as must-track: important runtime/provenance files may be ignored by Git while still being protected from deletion or cleanup.
- Validate changes with the smallest relevant check before finishing.

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
  - supported operator modes: `pack`, `build-check`, `review-pack`, `review-existing`, `review-now`, `review-fix`, `debt-fix`, `auto-loop`, `review-existing-queue`, `review-apply`, `verify`, `audit`, `soft-pack`, `soft-apply`
  - default local path is prompt-pack driven, with `build-check` as the normal technical gate, `review-now` as the Codex-facing semantic review entrypoint, `review-fix` as the semantic-repair entrypoint after failed review, `debt-fix` as the accepted-proof-debt repair entrypoint, and `auto-loop` as the same-session Codex orchestration mode
  - `soft-pack` and `soft-apply` are the Problem soft-dependency special case inside Phase 2
- Phase 3:
  - merged into Phase 2; old Phase 3 soft-dependency commands should report the migration path
  - ordinary failed local tasks stay in Phase 2 review/repair workflows
- Phase 4:
  - CLI branch is currently disabled/no-op
  - do not document or route work as if it were an active automated path

## Key Boundaries

- Do not touch high-risk protected state unless the user explicitly scopes that exact path: ledger files, Chapter 1-8 outputs, retired bridge/provider state, `dependency_decisions/`, prompt packs, and `.claude/worktrees/`.
- `soft-apply` means apply selected soft imports to the ledger and soft-dependency pack artifacts.
- `soft-apply` does not call an external provider, does not generate execution batches, and does not perform a Lean verification gate.
- Removed Phase 3 provider and post-processing artifacts remain protected local/historical state, not active workflow inputs.

## Recommended Routing

- Problem soft-dependency workflow:
  - `--phase 2 --phase2-mode soft-pack`
  - operator writes the selection JSON
  - `--phase 2 --phase2-mode soft-apply`
- If the task is about prompt-pack formalization, build failure, semantic review failure, or Problem soft-dependency selection, route through Phase 2 modes, not Phase 3.
- The Phase 2 entry skill is a routing checklist, not a second policy source; it points agents back to this contract and the Phase 2 docs before execution.
- Phase 2 Codex semantic review workflow:
  - existing official output: `review-now --review-subject existing`
  - current build-ready candidate: `review-now --review-subject candidate`
  - failed review follow-up: `review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate`
  - accepted proof-debt follow-up: `debt-fix -> review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate -> review-apply`
  - same-session orchestration: `auto-loop`
  - detailed same-session loop semantics: `docs/phase2_review_loop_protocol.md`
  - `review-pack` / `review-existing` are low-level prepare-only modes and should not be presented as the preferred Codex operator path.

## Codex Review Contract

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
- `auto-loop` is not an unattended reviewer/author daemon.
- Build-fail and review-prepared states are not normal waiting points; the current Codex agent continues in the same session.
- Pre-final guard: if `current_auto_loop_status = active`, do not end the turn with a completion-style summary unless the ledger also shows a documented stop reason.
- The documented stop reasons are only `completed`, `freshness_error`, `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption.
- Needing a substantial semantic rewrite, wanting to summarize current blockers, or waiting for the current Codex agent to perform reviewer/repair work are not stop reasons.
- `nonprogress` is a semantic stop reason, not a generic build stop.
- Only stop the same-session loop on `completed`, `freshness_error`, `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or explicit user interruption.
- For proof-bearing tasks, inspect the original `inputs/<source>.tex` proof or solution span before authoring, reviewing, or declaring a blocker; prompt-pack mirrors are not a substitute for the source file.
- For proof-debt repair, keep the textbook proof spine as the primary route. Use Mathlib as a formal substrate for atomic facts and APIs, not as a high-level shortcut that erases source proof steps unless the local Lean wrapper explicitly maps that theorem back to the textbook step.
- Treat `hard_failure` as a last-resort semantic stop: it requires source proof-spine decomposition, resource search/attempt evidence for the blocking obligation, and a task-local hard-failure note. Proof length or missing one-shot library theorem is not enough.
- Complex proof tasks require a task-local `decomposition_plan.md` or `decomposition_plan.json` before serious authoring/review. If a complex task is retried after an under-evidenced hard stop, do not declare another `hard_failure` before completion or 15 substantive build/review failures in the renewed attempt.
- Before inventing a new proof obligation for a complex task, check `ToyApollo/Output`, the ledger, dependency decisions, plans, and Mathlib for existing task outputs; include older textbook tasks, definition files, and bridge/foundation files that may already encode the needed idea. Repair missing metadata and reuse existing outputs before adding new black-box bridges.
- Before building a new foundation/API for proof debt, run a similarity scan across existing `ToyApollo/Output` foundation files, older chapter outputs, bridge files, and downstream tasks. Prefer extending or factoring a shared source-aligned foundation over creating theorem-local wheels. Good models include the `thm_9_5` split into Fubini, Dirichlet, kernel, and final assembly layers.
- Large accepted proof debt should be discharged by staged foundation files and internal source-spine assembly, not by keeping support structures as public theorem parameters. A public theorem is clean only when the support/source-spine package is constructed internally from proved lemmas or eliminated.
- Timed-out or manually aborted build/review runs without a canonical result file are mechanism blockers, not substantive failures toward the complex retry budget; record them and continue with a narrower diagnostic.
- When the user asks to review an existing chapter, section, or ordered task set, interpret that as a same-session self-driving existing-output batch review unless the user explicitly asks for prepare-only behavior.
- In chapter-wide or task-set Phase 2 goals, a hard-stopped task makes its hard-dependency downstream tasks dependency-failed for that goal; mark/skip those blocked tasks and continue with independent tasks instead of stopping the whole goal.
- `COMPLETED_WITH_PROOF_DEBT` is terminal only for the debt-bearing task. Do not consume it as a clean hard or selected soft dependency; downstream tasks are `DEPENDENCY_PROOF_DEBT` until `debt-fix` discharges the accepted debt and the blocker lands cleanly.
- In that existing-output batch mode:
  - use `review_subject=existing`, not `current`
  - process tasks in deterministic `block_id` order
  - do not stop after `review-now`, build failure, or a prepared review request; the current Codex agent continues the author/reviewer step in the same session
  - for pass results, continue to `review-apply` automatically
  - for fail/inconclusive results, continue through `review-apply -> review-fix -> build-check -> review-now --review-subject candidate -> review-apply`
- Only treat `review existing` as prepare-only when the user explicitly asks to inspect or prepare review materials without landing/apply behavior.
- When the user asks to "review existing", "review pack", or "review now" in the Codex path, do not stop at `codex_handoff_pending` unless the user explicitly wants prepare-only behavior.
- When the user asks to continue after a failed semantic review, do not rerun `review-existing` on the rejected object; route through `review-fix` and the build loop.
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
