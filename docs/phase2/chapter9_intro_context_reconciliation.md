# Chapter 9 Intro Context Reconciliation

Date: 2026-06-22

## Decision

`intro_9`, `intro_9_1`, and `intro_9_2` are non-proof textual remark
carriers. They keep the local textbook narrative available through retained
Lean string declarations, but they are not Phase 2 proof/definition tasks and
must not gate operational task selection.

Current status projection:

- `phase2_status`: `pass`
- `phase2_proof_class`: `non_proof_textual_remark_carrier`
- `phase2_task_role`: `remark`

## Dependency Boundary

No global `context_dependencies` mechanism is introduced in this pass. The
intro text remains available in source text, task content, and review prompt
context when needed, but it is not represented as `dependencies` or
`soft_imports`.

Operational corrections:

- `intro_9` has no hard dependencies or soft imports.
- `intro_9_1` has no hard dependency on `intro_9`.
- `intro_9_2` has no hard dependency on `intro_9`, `def_9_2`, or `def_6_6`.
- `def_9_1` has no hard dependency on `intro_9_1`.
- `def_9_3` keeps only the real interface dependency `def_6_6`.

Historical `dependency_decisions/*.jsonl` entries that recorded intro hard
edges remain audit history. They are superseded for current queueing and pack
projection by this reconciliation note and the updated source plans.

## Lean Boundary

The retained `ToyApollo.Output.intro_9*` declarations are compatibility
carriers. They should not import each other or import mathematical interfaces
unless the declaration body actually uses them.
