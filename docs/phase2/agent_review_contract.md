# Codex Phase 2 Review Contract

Read this contract before chapter-wide review, task-set review, state
reconciliation, `auto-loop`, or existing-output batch work. Root `AGENTS.md`
keeps only the entry rules and routes specialized work here.

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
- For chapter-wide or task-set Phase 2 work, prefer Codex durable goals
  (`/goal`) when the current Codex client supports them.
- Use `/goal` for requests that require continuing across many
  build/review/repair iterations, such as completing all
  non-remark/non-problem tasks in a chapter.
- The durable goal must include explicit stop conditions: `completed`,
  `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or
  explicit user interruption.
- If `/goal` is unavailable, create an explicit local batch state/checklist and
  run a pre-final guard before ending the turn.
- `review-now`, `review-fix`, and `auto-loop` are agent-assisted composite
  actions. `review-apply` remains the only step that lands a Codex
  semantic-review result.
- Failed existing-output review must preserve official output by default;
  quarantine is explicit opt-in maintenance after downstream import checks.
- `auto-loop` is not an unattended reviewer/author daemon.
- Semantic review is an independent read-only role unless a document explicitly
  declares a prepare-only non-review action. In active auto-loop repair, the
  authoring agent must delegate reviewer work to a separate reviewer subagent
  or configured reviewer runner, and the review result must include
  `reviewer_independence`.
- Build-fail and review-prepared states are not normal waiting points; the
  current Codex agent continues in the same session.
- Pre-final guard: if `current_auto_loop_status = active`, do not end the turn
  with a completion-style summary unless the ledger also shows a documented
  stop reason.
- The documented stop reasons are only `completed`, `freshness_error`,
  `hard_failure`, `nonprogress`, `max_rounds`, `build_budget_exhausted`, or
  explicit user interruption.
- Needing a substantial semantic rewrite, wanting to summarize current
  blockers, or waiting for the current Codex agent to perform reviewer/repair
  work are not stop reasons.
- `nonprogress` is a semantic stop reason, not a generic build stop.
- For proof-bearing tasks, adapter/debt decisions, complex decomposition,
  hard-failure admission, and public proof-package rules, follow
  `status_contract.md` and `review_criteria.md`; prompt-pack mirrors, clean
  ledgers, and successful builds are not substitutes for that contract.
- Before inventing a new proof obligation, bridge, or foundation interface,
  search existing `ToyApollo/Output`, bridge/foundation files, ledger state,
  dependency decisions, plans, and Mathlib; reuse or repair metadata before
  adding new scaffold.
- Timed-out or manually aborted build/review runs without a canonical result
  file are mechanism blockers, not substantive proof failures; record them and
  continue with a narrower diagnostic.
- When the user asks to review an existing chapter, section, or ordered task
  set, interpret that as a same-session self-driving existing-output batch
  review unless the user explicitly asks for prepare-only behavior.
- In chapter-wide or task-set Phase 2 goals, a hard-stopped task makes its
  hard-dependency downstream tasks dependency-failed for that goal; mark/skip
  those blocked tasks and continue with independent tasks instead of stopping
  the whole goal.
- `COMPLETED_WITH_PROOF_DEBT` is terminal only for the debt-bearing task. Do not
  consume it as a clean hard or selected soft dependency; downstream tasks are
  `DEPENDENCY_PROOF_DEBT` until direct existing-output review and the ordinary
  repair/review/apply path land the blocker cleanly.
- In existing-output batch mode:
  - use `review_subject=existing`, not `current`;
  - process tasks in deterministic `block_id` order;
  - do not stop after `review-now`, build failure, or a prepared review request;
  - for pass results, continue to `review-apply` automatically;
  - for fail/inconclusive results, use `review-apply` to record the failed
    review and repair request, then continue through
    `review-fix -> build-check -> review-now --review-subject candidate -> review-apply`;
    do not quarantine existing official output by default.
- Only treat `review existing` as prepare-only when the user explicitly asks to
  inspect or prepare review materials without landing/apply behavior.
- Do not stop at `codex_handoff_pending` unless the user explicitly wants
  prepare-only behavior.
- After a failed semantic review, do not rerun `review-existing` on the rejected
  object; route through `review-fix` and the build loop.
- Naming a precise missing lemma, bridge theorem, interface, or source-route
  gap is the next repair target, not a terminal result.
- When `auto-loop` is active, ledger runtime metadata is the only live loop
  state source; `metadata.json`, `context.md`, `failure_summary.md`, and
  `operator_prompt.md` are mirrors.
- For ad hoc single-task review requests, if the user does not explicitly ask
  to apply the review result, stop after the reviewer result and report the
  verdict plus result path.
- The single-task prepare-only rule does not override the existing-output batch
  rule; chapter/section/task-set review defaults to landing/apply behavior
  unless the user asks otherwise.
