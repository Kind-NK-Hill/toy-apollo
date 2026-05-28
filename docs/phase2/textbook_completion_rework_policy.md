# Textbook Completion Rework Policy

This file keeps the stable lessons from the May 2026 rework without importing
the temporary execution history.

Responsibility: capture durable strategy for upgrading selected targets to
textbook completion. Non-responsibility: command syntax, review schema details,
or task-specific case studies.

## Core Lesson

Proof production and proof-status honesty are separate. A task can build and
have clean metadata while still not be textbook-complete.

Before proof production:

- inspect the original source statement and proof;
- expand public theorem assumptions;
- check hard dependencies and earlier ToyApollo outputs;
- decide whether the target is textbook proof, adapter, bridge, open debt, or
  beyond-book exception.

## Proof Production

For hard proof targets, use narrow all-in proof production only after the
statement and dependency shape are clear.

When a main theorem has been selected for textbook completion, require
`textbook_proof_completed` as the success target. A foundation theorem, bridge
file, clean contract, or cleaner metadata is useful only if it is used to remove
the selected theorem's hidden/public proof obligation. Treat those artifacts as
in-run progress, not as completion.

Valid all-in target:

- source statement is not being silently strengthened;
- dependencies are known;
- missing work is proof production, not statement decision;
- public proof packages are forbidden;
- success requires theorem-level Lean landings.

Invalid all-in target:

- statement/interface is undecided;
- hard dependencies carry open debt;
- proof obligation is hidden in a package;
- completion would require a Mathlib-backed adapter while claiming textbook
  proof completion.

Valid non-completion result:

- `statement_patch_landed`: the source-faithful statement change was made in
  Lean and downstream calls were repaired;
- `hard_blocked_with_failed_lean_attempt`: the proof attempt reached a concrete
  Lean blocker, not just a natural-language concern.

Invalid non-completion result:

- `foundation_lemma_landed` reported as if the selected theorem were done;
- `bridge_landed` without returning to the selected public theorem;
- reclassifying the selected theorem as adapter/open debt without a concrete
  statement decision or failed Lean attempt.

## Foundation Pattern

Use the `thm_9_5` pattern for large source proofs: prove focused foundation
layers first, assemble any source-spine/support package internally, and expose a
public theorem whose assumptions are source-facing.

If several tasks need the same missing bridge or estimate, build one shared
foundation theorem or file first, then return to the task files. Do not patch
each task with its own theorem-local support object for the same mathematical
gap.

For a selected hard target, a shared bridge is not the terminal deliverable.
It is a normal Phase2 repair step. Once the bridge builds, immediately return
to the selected target, remove the public proof-step premise it replaces, and
continue the same repair loop. Stop only when the target theorem is assembled,
an accepted source-faithful statement patch is landed, or a concrete Lean hard
blocker is documented.

When a Mathlib theorem discharges a source proof step, record the source-step
mapping in the local wrapper or obligation metadata. Otherwise it is only a
black-box adapter and should not be classified as textbook proof completion.

See `examples.md` for short task examples such as `thm_11_7` and `prob_11_10`.
