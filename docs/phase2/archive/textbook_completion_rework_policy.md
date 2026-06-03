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

The important pattern is not merely file splitting. The source proof
obligations should first become auditable through internal source-spine or
foundation lemmas, then the public theorem should eliminate that scaffold by
constructing the evidence internally. The public theorem must not ask
downstream users to provide the source spine.

If several tasks need the same missing bridge or estimate, build one shared
foundation theorem or file first, then return to the task files. Do not patch
each task with its own theorem-local support object for the same mathematical
gap.

Every large proof-debt repair should start with a similarity scan. Check, in
order:

- the source proof span and textbook-order obligations;
- `ToyApollo/Output` for older textbook task files, definition files, bridge
  files, and earlier local foundation files;
- proof-obligation ledgers for tasks with the same kind, theorem family, or
  bridge name;
- direct downstream users, because they often reveal the intended reusable
  interface better than the current task does;
- Mathlib for atomic APIs or source-aligned theorem implementations.

The scan does not change the proof spine. A high-level Mathlib theorem can
discharge a source step only when the local Lean wrapper makes the
correspondence explicit; otherwise it is a black-box adapter.

Reuse targets are expected. For example, quantile and distribution-to-weak
foundations may reduce both `thm_10_8` and `thm_14_2`; optional-stopping and
stopped-process foundations may be shared across `thm_13_17` and `thm_13_18`;
total-variation or Radon-Nikodym density foundations may help `thm_14_4`; and
triangular-array or characteristic-function power-limit work should be reused
by later CLT/distribution tasks when assumptions match.

For `thm_10_8`, preserve the intended foundation split: quantile-space witness,
quantile definitions, quantile law facts, quantile convergence, and final
public assembly. Each slice should build, introduce no public support
parameter, and reduce the public theorem's accepted debt rather than creating a
parallel theorem-local package.

The concrete `thm_10_8` split is:

1. `ToyApollo/Output/thm_10_8_quantile_space.lean`: choose the common
   probability space, define `thm_10_8_unitIntervalMeasure`, prove
   `thm_10_8_unitIntervalMeasure_univ`, register
   `IsProbabilityMeasure thm_10_8_unitIntervalMeasure`, and prove the unit
   interval has full mass under that witness measure.
2. `ToyApollo/Output/thm_10_8_quantile_defs.lean`: define the reusable
   probability-CDF wrapper, lower and upper generalized inverse quantiles, their
   defining sets, variables, sequences, and links to the textbook formulas.
3. `ToyApollo/Output/thm_10_8_quantile_law.lean`: prove measurability, the CDF
   identity for constructed variables, and law preservation by CDF equality.
4. `ToyApollo/Output/thm_10_8_quantile_convergence.lean`: prove lower/upper
   inverse comparison from CDF convergence at continuity points, use `prob_3_5`
   for discontinuity control, and prove almost-sure convergence of the coupled
   variables.
5. `ToyApollo/Output/thm_10_8.lean`: import the foundation files, keep
   `SkorokhodRepresentation` as the public conclusion, construct any private
   source-spine package from proved quantile lemmas, and remove public
   `SkorokhodQuantileSupport`, `common_unit_interval_space`, and
   `generalized_inverse_quantiles` proof-debt fields.

The corresponding `phase2_prompt_packs/thm_10_8/proof_obligations.json` should
track which slices are proved. At the current stable planning point, the first
two slices were the proved obligations; remaining debt was law preservation,
lower/upper inverse comparison, and almost-sure convergence.

Known reuse landings from this rework:

- `ToyApollo/Output/thm_14_7.lean` proves
  `thm_14_7_triangularPowerLimit_proved` from Mathlib's complex exponential
  power-limit theorem. The CLT setup should no longer ask downstream users to
  provide `triangular_power_limit`; only concrete characteristic-function
  convergence data remains as support.
- `ToyApollo/Output/thm_13_18.lean` defines the canonical real-valued
  representative `thm_13_18_stoppedValueReal`.
  `thm_13_18_stoppedValueReal_agreement` proves the finite stopped-value
  agreement interface, and `thm_13_18_stoppedValueReal_matches_option`
  connects it to Definition 13.8's Option-valued stopped value.
  `thm_13_18_canonical` exposes the source-aligned theorem using the canonical
  representative internally; remaining `thm_13_18` proof debt is limited to the
  two dominated-convergence routes in cases (ii) and (iii).

For a selected hard target, a shared bridge is not the terminal deliverable.
It is a normal Phase2 repair step. Once the bridge builds, immediately return
to the selected target, remove the public proof-step premise it replaces, and
continue the same repair loop. Stop only when the target theorem is assembled,
an accepted source-faithful statement patch is landed, or a concrete Lean hard
blocker is documented.

When a Mathlib theorem discharges a source proof step, record the source-step
mapping in the local wrapper or obligation metadata. Otherwise it is only a
black-box adapter and should not be classified as textbook proof completion.

Do not keep re-running `debt-fix` expecting it to write the foundation. When the
missing object is a reusable foundation, create the first narrow foundation
file, make it build, then return to the public target theorem.

See `examples.md` for short task examples such as `thm_11_7` and `prob_11_10`.
