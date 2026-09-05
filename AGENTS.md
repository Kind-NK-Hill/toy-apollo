# Formalization Engine Agent Contract

This is the canonical root contract for coding agents working in `ProbabilityTheoryFormalization`.

If this file conflicts with older notes, trust current runtime code and the rule files under `.claude/rules/`.

## Always Do

- Keep active execution under `formalize --phase {0,1,2}`. No other phase is part of the current CLI.
- Keep `formalize --status` strictly read-only. Its resolved roots describe only the current process, not an active campaign's global authority.
- Use `formalize status <task>` or `worklist` for live derived repository/review/PR state; these refresh GitHub by default and never commit, push, open, or merge a PR.
- Use `formalize pr-review prepare/apply` for an exact Kenneth PR head. This path records external review coverage only; it never lands the candidate in `ProbabilityTheory/` or changes PR readiness/merge state.
- Treat `.claude/rules/10-phase-runtime.md` as the phase behavior source of truth before making any phase-routing decision.
- Prefer active package paths under `src/formalization_engine/*` for new code.
- Treat `ProbabilityTheoryFormalization-artifacts/state.sqlite3` as the workspace operational state described in `docs/workspace_state.md`. Legacy `project_ledger.json` is protected, frozen import evidence after SQLite activation.
- Load the pinned task catalog through `src/formalization_engine/task_catalog.py`; do not infer the task denominator or support ownership from whichever rows happen to exist in SQLite. The catalog contains 452 formal tasks, 445 printed-label families, and 584 MAT Lean modules. The named 344-item legacy review cohort is a retained projection, not the complete task catalog.
- Treat SQLite as a rebuildable index over immutable evidence, not as review authority by itself. Keep “a compatible PASS exists” separate from “that PASS is bound to the exact current subject bundle”; a validated rebind can carry a compatible verdict across an exact/mechanical transformation, but it cannot upgrade an obsolete rubric.
- Remember that must-protect is not the same as must-track: important runtime/provenance files may be ignored by Git while still being protected from deletion or cleanup.
- Validate changes with the smallest relevant check before finishing.

## Repository Flow (Hard Boundary)

- `ProbabilityTheory/` is the only canonical Lean corpus in this repository.
- Its migration baseline is the exact Git object at MAT commit
  `3acca18c01aebc1fedee47b56e380e0d30b5094c`; ordinary author/build/review
  operations work in artifact staging and do not write this tree.
- Only `review-apply`, after exact-subject semantic review, may update a
  manifest-resolved canonical path. It must restore the prior bytes on failure.
- Kenneth and historical MAT repositories are external evidence/review sources,
  not alternative active output trees. Never copy an unreviewed external
  candidate directly into `ProbabilityTheory/`.
- `Kind-NK-Hill/ProbabilityTheory` remains PR transport only. Frozen external
  snapshots are read-only evidence, not authorization for source mutation.

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
  - before any authoring, review, repair, hard-failure decision, or chapter/task-set batch, use the repo skill `.agents/skills/formalization-engine-phase2-entrypoint/SKILL.md`; if the Codex skill system has not auto-loaded it, read that file manually and follow its entry report before task-specific work
  - proof-fidelity verdicts are governed by `docs/phase2/status_contract.md` and `docs/phase2/review_criteria.md`; do not treat Lean build success, `#print axioms` cleanliness, ledger cleanliness, audit cleanliness, or classification cleanliness as textbook proof completion
  - `#print axioms` cleanliness is only a proof-dependency-debt check for checked declarations; it does not prove source fidelity, human validation, or semantic completion. For detailed proof-status semantics, follow `docs/phase2/status_contract.md`.
  - default authority is three-gate: build gate only proves technical build readiness; review gate supplies a strict semantic verdict and proof class; apply gate lands clean completion only when `phase2_status=pass`
  - CLI completion [active phase=2]: `pack -> build-check -> review-now -> review-apply`
  - for chapter-wide or task-set work, start with `batch-plan`; use `--batch-task-kinds theorem,definition --batch-limit 15 --batch-workers <n>` for a non-Problem worker queue, and use `batch-run --batch-max-actions 1` only as a bounded dispatcher over existing review/auto-loop actions
  - CLI modes [active phase=2, non-default examples]: `batch-plan`, `batch-run`, `review-pack`, `review-existing`, `review-existing-queue`, `review-fix`, `auto-loop`, `soft-pack`, `soft-apply`; these modes do not independently decide clean completion
  - `soft-pack` and `soft-apply` are the Problem soft-dependency special case inside Phase 2

## Key Boundaries

- Do not touch high-risk protected state unless the user explicitly scopes that exact path: ledger files, Chapter 1-8 outputs, retired bridge/provider state, `dependency_decisions/`, prompt packs, and `.claude/worktrees/`.
- `soft-apply` means apply selected soft imports to the ledger and soft-dependency pack artifacts.
- `soft-apply` does not call an external provider, does not generate execution batches, and does not perform a Lean verification gate.
- Retired provider and post-processing artifacts remain protected local/historical state, not active workflow inputs.
- Do not describe AI-generated Lean, docs, review files, prompt-pack contents, or audit artifacts as handwritten by the user unless local authorship evidence explicitly proves it.

## Recommended Routing

- Problem soft-dependency workflow:
  - `--phase 2 --phase2-mode soft-pack`
  - operator writes the selection JSON
  - `--phase 2 --phase2-mode soft-apply`
- If the task is about prompt-pack formalization, build failure, semantic review failure, or Problem soft-dependency selection, route through Phase 2.
- The Phase 2 entry skill is a routing checklist, not a second policy source; it points agents back to this contract and the Phase 2 docs before execution.
- Phase 2 Codex semantic review workflow:
  - task-set routing view: `batch-plan`
  - non-Problem worker queue: `batch-plan --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers <n>`
  - bounded same-session dispatcher: `batch-run --batch-max-actions 1`
  - existing official output: `review-now --review-subject existing`
  - current build-ready candidate: `review-now --review-subject candidate`
  - failed review follow-up: use `auto-loop`; the default repair budget and CLI floor are 15 review rounds and 15 build-check attempts before each review round
  - `review-fix -> edit draft.lean -> build-check -> review-now --review-subject candidate` is a diagnostic/manual decomposition of the loop, not a replacement for the loop
  - legacy accepted proof debt must be re-evaluated with `review-now --review-subject existing`; failed or inconclusive review continues through `review-apply -> auto-loop` and the ordinary candidate repair path
  - same-session orchestration: `auto-loop`
  - current default workflow: `docs/phase2/workflow.md`
  - `review-pack` / `review-existing` are low-level prepare-only modes and should not be presented as the preferred Codex operator path.
- If the manifest-resolved canonical file for a task is newer than and differs from the latest
  `draft.lean` / `candidate_vN.lean`, the candidate review target is stale.
  Do not build-check or review that stale candidate. Review the official output
  with `review-now --review-subject existing`, or intentionally sync the output
  into `draft.lean` and rerun `build-check`.

## Codex Review Contract

Read `docs/phase2/agent_review_contract.md` before chapter-wide review, task-set
review, state reconciliation, `auto-loop`, or existing-output batch work. The
deep contract lives there so ordinary repository tasks do not have to load the
entire review state machine.

The non-negotiable entry rules are:

- investigate the actual proof/solution route and exact subject bundle;
- keep review authority, typed authority, and mechanical transformation distinct;
- `review-apply` is the only landing step for a Codex semantic review;
- reviewer independence is required for active author/repair loops;
- do not stop an active loop without one of the documented stop reasons;
- preserve official output by default after a failed existing-output review.

## Ask First

- Deleting or bulk-moving runtime outputs, prompt packs, logs, or historical plans.
- Changing ledger status names, plan JSON schema, or stable CLI flags.
- Reworking directory layout for `ProbabilityTheory`, `output_lean_files`, or artifacts sync.
- Reintroducing retired external-provider behavior or adding new external service dependencies.

## Never Do

- Commit secrets, tokens, or `.env` files.
- Treat archive notes as runtime truth unless active code implements them.
- Use `plans/unsolved_tasks.json` as the default soft-dependency source of truth.
- Describe `soft-apply` as external-provider execution or as a Lean acceptance gate.
- Describe retired provider/post-processing tracks as active workflow.
- Reformat the repository by hand in agent prompts; use dedicated tooling when formatter/linter policy is added.

## Repo Map

- Runtime entry: installed `formalize` command
- Active CLI: `src/formalization_engine/cli/app.py`
- New package home: `src/formalization_engine/`
- All active Python modules live under `src/formalization_engine/`; there is no `src` compatibility package.
- Lean output module root: `ProbabilityTheory`
- Runtime state and generated outputs: artifact-rooted paths from `src/formalization_engine/core/settings.py`

## Minimum Verification

- `formalize -h`
- `formalize --status`
- `python tools/check_repo_hygiene.py`
- `lake build <manifest-resolved ProbabilityTheory module>` for any touched Lean-facing task path

## Progressive Disclosure

Read only the rules needed for the task:

- `@.claude/rules/00-repo-boundary.md`
- `@.claude/rules/10-phase-runtime.md`
- `@.claude/rules/20-artifacts-and-ledger.md`
- `@.claude/rules/30-security-secrets.md`
- `@.claude/rules/40-folder-playbooks.md`

Then read the nearest folder-level `AGENTS.md` before editing inside that subtree.
