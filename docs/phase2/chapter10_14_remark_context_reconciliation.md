# Chapter 10-14 Remark Context Reconciliation

> **Superseded 2026-06-30.** The Lean string carriers and ledger task entries for
> these `intro_*` / `rem_*` remarks were removed. Chapters 9-14 now follow the
> Chapters 1-8 norm: remark/intro blocks are plan-only narrative
> (`plans/*_plan.json`), **not** Phase 2 Lean tasks — no `ToyApollo/Output`
> carrier and no ledger entry is retained. The retain-as-carrier decision below
> is kept for history only.

Date: 2026-06-22

## Decision

The remaining `intro_*` and `rem_*` Phase 2 tasks in Chapters 10-14 that were
still `DISCOVERED` are non-proof textual remark carriers. They preserve textbook
narrative context but are not proof-bearing tasks, definition interfaces, or
operational hard dependencies.

Current status projection for these tasks:

- `phase2_status`: `pass`
- `phase2_proof_class`: `non_proof_textual_remark_carrier`
- `phase2_task_role`: `remark`

## Dependency Boundary

No global `context_dependencies` mechanism is introduced. Textual context
remains available through source-plan content and retained Lean string carriers.
It is not represented as `dependencies` or `soft_imports`.

Operational corrections:

- Remaining Chapter 10-14 textual remarks have no hard dependencies.
- Chapter 10 definitions no longer hard-depend on section intros:
  - `def_10_1` no longer depends on `intro_10_1`.
  - `def_10_2` keeps `def_10_1` and no longer depends on `intro_10_1`.
  - `def_10_3` no longer depends on `intro_10_2`.
  - `def_10_4` no longer depends on `intro_10_3`.

Historical dependency decision logs remain audit history. They are superseded
for current queueing and pack projection by this reconciliation note and the
updated source plans.

## Lean Boundary

Each retained output is a zero-argument `String` declaration named after the
task id. These declarations are compatibility carriers for source narrative and
should not import mathematical interfaces unless the declaration body actually
uses them.
