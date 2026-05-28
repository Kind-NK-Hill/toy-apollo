# Phase2 Step 6 Route And Signature Freeze Plan

Created: 2026-05-25
Status: current Step 6 entry after Step 5.5 and Step 5.6

## Executive Rule

Step 6 is not a Lean proof-production step.

Step 6 has only two jobs:

1. **Step 6A: source route extraction.** Read the source proof, current Lean
   file, classification row, obligation contract, and reusable local/Mathlib
   declarations.
2. **Step 6B: expected signature freeze.** Freeze the theorem signatures,
   allowed imports, no-new-public-premise rule, and the queue that must be sent
   to Step 7 or Step 8.

Step 6 must not introduce a new Lean proof attempt. Step 6 must not create a
`Step 6C`. The former `Step 6C: Scoped Lean Proof Implementation` belonged to
the old mixed Step 6 design and is replaced by:

- Step 7: bridge / foundation lemma completion;
- Step 8: scoped target Lean implementation.

## Step 5.6 Baseline

Use this report as the current contract baseline:

- `docs/modification_0525_steps/phase2_step5_6_contract_reconciliation_report.md`

Verified Step 5.6 results:

- strict classification gate passes:
  `python tools/validate_phase2_completion_classification.py --require-proof-contract`
- six priority tasks have task-level contract audit `0 error / 0 warning`:
  - `prob_10_6`
  - `thm_11_7`
  - `thm_13_14`
  - `thm_14_5`
  - `thm_14_8`
  - `ex_14_4_3`
- global obligation-contract audit is not clean:
  - `error`: `2027`
  - `warning`: `50`
  - `error_task_count`: `136`

The global backlog is not a blocker for a selected target. It is also not proof
work. Do not spend Step 6 on bulk metadata cleanup.

## What Step 6 Is Not

Step 6 is not:

- global metadata cleanup;
- bulk migration of old proof obligations;
- Lean proof implementation;
- statement patching;
- final theorem assembly;
- a reason to edit `project_ledger.json`;
- a reason to promote `open_math_debt` to `textbook_proof_completed`;
- a reason to return a target to open debt and call proof-production complete.

If a target cannot proceed because a bridge, foundation lemma, or statement
decision is missing, Step 6 must hand it to Step 7 or Step 5. It must not end
the proof-production pipeline.

## Target Dispositions

| task_id | Step 5/5.6 state | Step 6 action | next step |
| --- | --- | --- | --- |
| `prob_10_6` | locked `textbook_proof_completed` | Preserve historical proof result; no new Step 6 work unless regression appears. | none |
| `thm_11_7` | contract-clean open debt | Freeze tail-summability route and expected foundation signatures. | Step 7 |
| `thm_13_14` | contract-clean open debt | Freeze interval-Fubini and generator-extension route/signatures. | Step 7 |
| `thm_14_5` | accepted adapter | Preserve adapter decision. Do not upgrade unless Step 5 is reopened. | none |
| `thm_14_8` | unique beyond-book exception | Preserve exception boundary. | none |
| `ex_14_4_3` | inherited exception plus local debt | Not selected unless explicitly pulled into a later route-freeze pass. | later Step 6, then Step 7 |

## Step 6A: Source Route Extraction

For each selected target, record:

- source locations inspected;
- current public theorem statement and any extra proof premise;
- current blocker declaration;
- source proof steps;
- existing ToyApollo declarations that actually prove or bridge part of the
  route;
- Mathlib APIs that may be used as local tools;
- missing bridge/foundation lemmas;
- statement sufficiency status;
- whether the target should go to Step 7, Step 8, or back to Step 5.

Allowed Step 6A dispositions:

- `locked_completed`: no proof work remains for this target.
- `ready_for_step7`: foundation or bridge lemmas must be proved before target
  assembly.
- `ready_for_step8`: all required foundation lemmas already exist, so target
  assembly can be attempted in Step 8.
- `needs_step5_statement_decision`: the statement or accepted route must change
  before proof work.
- `non_target`: accepted adapter, beyond-book boundary, or deferred backlog.

Do not use `ready_for_lean`. It was too ambiguous: in the old design it could
mean either foundation proof work or final target implementation. Use
`ready_for_step7` or `ready_for_step8`.

## Step 6B: Expected Signature Freeze

For every selected target that proceeds beyond Step 6A, freeze a handoff packet:

```text
task_id
selected_obligations
expected_theorem_signatures
write_scope_for_step7
write_scope_for_step8
allowed_imports
allowed_mathlib_role
no_new_public_premise_rule
forbidden_shortcuts
validation_commands
handoff_destination: Step 7 | Step 8 | Step 5
```

The `expected_theorem_signatures` do not need to be perfect one-shot final
statements, but they must be concrete enough that Step 7/8 can either land a
theorem or report a real Lean failure against a named signature.

If Step 6B cannot freeze even one meaningful theorem signature for the target,
send the target back to Step 5 for a statement/route decision. Do not write a
generic "needs foundation" report and stop.

## Current Frozen Handoffs

### `thm_11_7`

Handoff destination: Step 7.

Primary missing theorem:

```lean
theorem thm_11_7_tail_summability_from_fourth_moment :
  def_5_10_randomVariables P X ->
  (forall i : Nat, P[X i] = mu) ->
  (exists c : Real, thm_11_7_fourthMomentUniformBound P X mu c) ->
  thm_11_7_tailSummabilitySupport P X mu
```

Expected Step 7 foundation lemmas include:

- centered-variable measurability / integrability bridge;
- centered-variable independence bridge;
- fourth-moment expansion or a usable bound for finite sums;
- mixed-term cancellation under independence and zero mean;
- Cauchy-Schwarz or Holder bound for paired square terms;
- fourth-power Markov tail estimate;
- p-series summability in the current `ENNReal` tail interface.

Step 8 may only attempt final `thm_11_7` assembly after enough of these Step 7
lemmas have landed to remove the public `h_tail_summability` premise.

### `thm_13_14`

Handoff destination: Step 7.

Primary missing theorems:

```lean
theorem thm_13_14_interval_fubini_from_joint_density :
  thm_13_14_jointDensityLaw P fXY ->
  -- frozen density, measurability, and integrability prerequisites
  thm_13_14_intervalFubiniSupport P fXY g

theorem thm_13_14_pi_lambda_extension_from_intervals :
  thm_13_14_intervalFubiniSupport P fXY g ->
  -- frozen generator / finite-integral prerequisites
  thm_13_14_piLambdaExtensionSupport P g
    (thm_13_14_conditionalExpectationKernel fXY g)
```

Expected Step 7 foundation lemmas include:

- joint-density representation bridge;
- nonnegativity, measurability, and integrability facts for `fXY`;
- marginal-density measurability and finiteness facts;
- conditional-kernel measurability and integrability facts;
- closed-interval cylinder identity;
- Fubini/Tonelli bridge for the product-density integrand;
- conditional-density algebra rewrite under `fY y != 0`;
- interval-generator / pi-lambda extension theorem in the project interface.

Step 8 may only attempt final `thm_13_14` assembly after enough Step 7 lemmas
have landed to remove the public `hIntervals` and `hExtend` premises.

## Validation For Step 6

Run target contract checks, not global cleanup:

```powershell
python -m json.tool docs/phase2_completion_classification.json > $null
python -m json.tool docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json > $null
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/validate_phase2_obligation_contracts.py --task <task_id>
```

Lean build is optional in Step 6 unless Step 6 is verifying a historical result
or a file was already touched before this plan. Step 7 and Step 8 own Lean
proof-production validation.

## Completion Criteria

Step 6 is complete for a selected target only when:

- source route extraction exists;
- expected theorem signatures are frozen or the target is explicitly sent back
  to Step 5;
- the handoff destination is Step 7, Step 8, Step 5, or none for locked targets;
- no new public proof premise is introduced;
- no Lean proof-production claim is made.

Step 6 is not complete when it only says "open debt remains" without a Step 7,
Step 8, or Step 5 handoff.

## Historical Note

The prior Step 6 checkpoint used `Step 6C` language and allowed a target to be
returned to `open_math_debt` as a current-pass completion result. That was a
transitional artifact. Going forward, open debt discovered in Step 6 must become
either a Step 7 proof-production queue item or a Step 5 statement/route decision.
