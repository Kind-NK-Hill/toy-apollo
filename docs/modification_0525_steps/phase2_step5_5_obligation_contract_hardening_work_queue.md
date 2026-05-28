# Phase2 Step 5.5 Obligation Contract Hardening Work Queue

Created: 2026-05-25

Status: implemented on 2026-05-25; superseded by Step 5.6 reconciliation.

Controlling plan:

- `docs/modification_0525_steps/phase2_step5_5_obligation_contract_hardening_implementation_plan.md`

Stable policy source:

- `docs/phase2_proof_fidelity_contract.md`

## Queue Rule

This queue is mechanism work only. Do not edit `ToyApollo/Output/*.lean`. Do not
mark any task `textbook_proof_completed`. Do not update `project_ledger.json` by
hand.

## Required Work Items

| order | work item | write scope | expected output | validation |
| ---: | --- | --- | --- | --- |
| 1 | Normalize proof-contract fields | `src/toy_apollo/phase2_proof_obligations.py`, `tests/test_phase2_proof_obligations.py` | obligation items preserve `expected_theorem_signature`, `landing_kind`, `proof_contract_status`, and contract check fields | `python -m unittest tests.test_phase2_proof_obligations` |
| 2 | Add obligation contract validator | `tools/validate_phase2_obligation_contracts.py`, `tests/test_phase2_obligation_contracts.py` | standalone scanner with `--write-report`, `--fail-on-errors`, and `--task` | `python -m unittest tests.test_phase2_obligation_contracts` |
| 3 | Harden semantic review schema | `src/toy_apollo/phase2_proof_obligations.py`, `src/toy_apollo/phase2_semantic_review.py`, `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`, relevant tests | reviewer `covered` requires signature/body/public-premise contract evidence | `python -m unittest tests.test_phase2_proof_obligations tests.test_phase2_pack_generation` |
| 4 | Harden review apply | `src/toy_apollo/phase2_proof_obligations.py`, `src/toy_apollo/phase2_review_apply.py`, `tests/test_phase2_review_apply.py` | `covered` no longer becomes `proved` unless proof contract verifies | `python -m unittest tests.test_phase2_review_apply tests.test_phase2_obligation_tasks` |
| 5 | Connect classification validator | `tools/validate_phase2_completion_classification.py`, `tests/test_phase2_completion_classification.py` | textbook-complete classifications require proof-contract evidence or explicit Level 0 direct-proof reason | `python -m unittest tests.test_phase2_completion_classification` |
| 6 | Generate Step 5.5 audit | `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.md`, `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.json` | current corpus contract health report | `python tools/validate_phase2_obligation_contracts.py --write-report` |

## Implementation Result

Step 5.5 mechanism hardening is implemented. The current corpus is not
contract-clean: the new validator intentionally reports remaining contract
metadata errors rather than weakening them.

Completed work:

- Contract fields are normalized and rendered in proof-obligation ledgers.
- A standalone obligation contract validator exists with `--write-report`,
  `--fail-on-errors`, and `--task`.
- Semantic review pass validation now requires verified proof-contract evidence
  for `covered` blocking obligations.
- Review apply no longer promotes `covered` to `proved` unless the proof
  contract is verified and all three contract checks pass.
- Completion classification validation has an optional strict
  proof-contract gate for `textbook_proof_completed` rows.
- Step 5.5 audit reports are generated under `docs/modification_0525_steps/`.

Initial Step 5.5 audit summary before Step 5.6 reconciliation:

- `error`: 2089
- `warning`: 100
- `info`: 0
- `error_task_count`: 142

`python tools/validate_phase2_obligation_contracts.py --fail-on-errors` exits
`1` on the current corpus, as expected for `contract_active_with_errors`.

Step 5.6 reconciliation reduced the global audit to `2027` errors / `50`
warnings / `136` error tasks and wrote the remaining queue to
`docs/modification_0525_steps/phase2_step5_6_contract_reconciliation_report.md`.

## First Targets To Inspect

These are not Lean proof targets. They are contract-health examples for the
validator.

| task_id | why inspect | expected Step 5.5 result |
| --- | --- | --- |
| `prob_10_6` | good Step 6 case; should show what real theorem landing looks like if current proof obligations are accurate | either verified proof contract or missing contract metadata to add |
| `thm_11_7` | private axiom removed but proof burden moved to explicit premise | validator must not allow false `proved` status unless expected signature and body anti-reassumption checks pass |
| `thm_13_14` | same statement-boundary premise risk as `thm_11_7` | validator must expose missing source-route proof contract |
| `thm_14_5` | accepted adapter, not strict textbook proof | adapter landings must not satisfy textbook-complete obligations |
| `thm_14_8` | unique beyond-book exception | only `thm_14_8_ProofBeyondBook` may pass beyond-book exception rules |
| `ex_14_4_3` | inherited beyond-book plus non-beyond-book Lyapunov debt | validator must separate inherited exception from local open debt |

## Forbidden Success Criteria

The implementation is not complete if any of these are true:

- a reviewer `covered` item still directly becomes `proved` without proof
  contract verification;
- a proved obligation can land on `SomeSpine.some_field`;
- a proved obligation can land on a private axiom;
- an adapter landing can satisfy a `textbook_proof_completed` target;
- current corpus report is omitted because it contains errors;
- Lean proof files are changed to make the validator pass.

## Expected Final Commands

Run at the end:

```powershell
python -m py_compile tools/validate_phase2_obligation_contracts.py src/toy_apollo/phase2_proof_obligations.py src/toy_apollo/phase2_semantic_review.py src/toy_apollo/phase2_pack_shared/review_basis_parts.py src/toy_apollo/phase2_review_apply.py
python -m unittest tests.test_phase2_obligation_contracts tests.test_phase2_proof_obligations tests.test_phase2_review_apply tests.test_phase2_pack_generation tests.test_phase2_completion_classification
python tools/validate_phase2_completion_classification.py
python tools/validate_phase2_obligation_contracts.py --write-report
```

Then run:

```powershell
python tools/validate_phase2_obligation_contracts.py --fail-on-errors
```

If this final command fails on current corpus, that is acceptable only when the
new audit report names the remaining contract errors. Do not downgrade those
errors to make the command pass.

## Step 5.5 Exit Decision

After implementation, decide one of:

- `contract_clean`: validator active and current corpus has no contract errors;
- `contract_active_with_errors`: validator active and current corpus has named
  errors; proceed only to Step 6A/6B planning, not direct proof implementation;
- `mechanism_blocked`: validator or review/apply hardening could not be
  implemented; stop before any further Textbook Complete proof claims.
