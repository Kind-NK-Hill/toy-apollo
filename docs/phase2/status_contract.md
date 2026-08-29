# Phase2 Status Contract

`phase2_status` is the task-level Phase2 status. It is the only clean landing
guard.

Allowed values:

- `pass`
- `fail`
- `blocked`
- `allowed_exception`

The older `phase2_task_status` field may exist for compatibility, but new code
and reports should prefer `phase2_status`.

## Report-Only Statuses

Batch/status reports may derive additional display states from missing or stale
evidence. Reports must show these under a derived `report_status` or repair-hint
field, not under canonical `phase2_status`:

- `needs_fresh_review`
- `needs_class_normalization`

These are report-only repair hints. They are not canonical `phase2_status`
values and must not be written or interpreted as clean completion.

A single-task dependency reconciliation therefore clears canonical PASS fields
and records `dependency_reconciliation_requires_fresh_review=true`; the batch
projection derives `needs_fresh_review` from that marker. A later fresh,
successful `review-apply` clears the marker and records the reconciliation id
that the new review superseded.

## Projection Inputs

The apply gate projects:

- semantic review verdict;
- reviewer `proof_class` / `completion_class`;
- source task role.

Historical `proof_obligations.json` files are inert audit artifacts. They are
not projection inputs, review evidence, status authorities, planning inputs, or
apply targets. Ledger state, audit reports, classification files, batch state,
validation tools, and verify reports are likewise not status authorities.

## Proof Dependency Audits

`#print axioms` and related axiom-audit outputs are proof-dependency-debt
checks for the declarations that were actually checked under the recorded
command. A clean result can support a narrow claim such as "no reported
`sorryAx`, native-reduction debt, or external axiom dependency for this checked
term under this environment."

This audit does not decide source fidelity, statement strength, textbook proof
route, human validation, or Phase2 clean completion. It does not replace
semantic review, proof class projection, or `review-apply`.

## Pass Rules

Proof-bearing tasks include theorem, problem, exercise, and example tasks. They
pass only with source-route proof classes such as:

- `textbook_proof_completed`
- `textbook_problem_completed`
- `textbook_exercise_completed`
- `textbook_source_route_completed`
- `source_route_proof_completed`
- `source_faithful_proof_completed`
- `source_route_theorem`

Reusable proof material belongs in the parent file or stable support files
before review. Historical `Phase2ObligationTask` child completions and
checklist entries are not completion authority for the parent
theorem/problem/exercise. A parent is clean only after direct review maps every
essential source step to its parent/support Lean landing and the parent review
passes.

Definition/interface tasks may pass with:

- `textbook_definition_completed`
- `definition_only_completed`
- `source_faithful_definition_bridge_completed`
- `source_faithful_notation_bridge_completed`
- `interface_bridge_completed`

`interface_bridge_completed` passes only for definition/interface/bridge roles.
It does not pass a theorem/problem/exercise task.

## Fail Rules

These proof classes or markers are fail/blocker evidence for local completion:

- `mathlib_backed_adapter_completed`
- `adapter`
- `open_math_debt`
- `proof_debt`
- `statement_weakened`
- `public_premise`
- `private_axiom`
- `semantic_fail`
- a historical/imported pass record with no completion class after migration

They may be useful evidence or repair targets, but they are not clean
completion.

New semantic-review results must contain non-empty `proof_class` and
`completion_class`. Missing/empty fields are schema-invalid operational output
and never reach task-status projection; the historical fallback rule above is
retained only for ledger/report migration.

`mathlib_backed_adapter_completed` means adapter-only completion: a
proof-bearing source task was closed by importing or applying Mathlib without a
reviewed source-step landing or reusable equivalence bridge. It does not mean
that every proof using Mathlib fails. A proof-bearing task may still project to
`pass` when Mathlib use is routed through the source proof spine and reviewed as
reusable infrastructure or an explicit equivalence bridge.

## Blocked Rules

Dependency-gate markers such as `dependency_blocked`,
`dependency_failed`, and `fresh_review_refused_by_dependency_gate` project to
`blocked` unless the same class also contains local open-debt/adapter evidence,
which remains `fail`.

## Allowed Exception

`allowed_exception` is reserved for explicit task/class pairs and is not clean
textbook completion:

- `thm_1_2` with `source_statement_exception`: the closed-interval
  Riemann--Stieltjes concatenation clause is a source-statement decision
  boundary under the current formal interface, not ordinary proof debt.
- `ex_1_3_2` with `source_typo_statement_exception`: the mixed-type
  expectation example carries a source typo/statement-decision boundary around
  the displayed continuous part, so it is not an ordinary proof-repair target.
- `thm_11_8` with `cited_external_proof_exception`: the textbook explicitly
  cites Etemadi's external proof, and the current Lean statement is
  source-faithful and downstream-usable while the core proof remains an
  accepted external-proof boundary.

It must not be generalized silently.

`thm_14_8` is no longer an exception. Its former `beyond_book_exception`
interface was replaced by a complete proof route, its direct consumers were
migrated, and a fresh `review-apply` landed
`source_faithful_proof_completed` with `phase2_status=pass` on 2026-08-05.
