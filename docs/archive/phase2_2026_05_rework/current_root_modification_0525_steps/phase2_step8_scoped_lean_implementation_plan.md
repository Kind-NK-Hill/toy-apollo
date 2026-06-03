# Phase2 Step 8 Scoped Lean Implementation Plan

Created: 2026-05-25
Status: current target-theorem implementation entry

## Executive Rule

Step 8 is the first step allowed to implement or rewrite the selected public
target theorem after Step 6/7 preparation.

Step 8 consumes:

- Step 5 target decisions;
- Step 5.5/5.6 obligation contract gates;
- Step 6 source-route and expected-signature freeze;
- Step 7 bridge/foundation lemmas or accepted statement patches.

Step 8 must not begin just because a target is important. It begins only when
there is enough Step 7 evidence to either remove a public proof premise, remove
a private axiom, or assemble a frozen target theorem from landed lemmas.

## Allowed Results

Every Step 8 target must end in exactly one of:

- `target_textbook_completed`: the public theorem builds, no forbidden public
  proof premise remains, selected obligations land on verified theorem/lemma
  evidence, and classification can honestly become `textbook_proof_completed`.
- `target_debt_reduced`: at least one public proof premise, private axiom, or
  open obligation was removed or replaced by theorem-level evidence, but the
  target is not yet textbook complete.
- `statement_patch_landed`: the public statement or local interface was changed
  by an accepted Step 5/7 decision, all downstream touched files build, and the
  proof status is classified honestly.
- `hard_blocked_with_failed_lean_attempt`: a concrete final-assembly attempt
  failed against the frozen signatures; broken code was removed; failure
  evidence is recorded.

Invalid Step 8 endings:

- analysis-only report;
- metadata-only cleanup;
- final theorem gains a new public source-proof premise;
- final theorem calls a wrapper that assumes the missing source step;
- adapter proof is promoted to `textbook_proof_completed`;
- `open_math_debt` is restated without a landed proof reduction or Lean failure
  evidence.

## Entry Checklist

Before editing a target in Step 8:

- Step 6 handoff names the target and expected final route;
- Step 7 has landed the required foundation lemma(s), or records that no Step 7
  lemma is needed for this target;
- the public theorem assumptions have been expanded through local packages, so
  hidden statement strengthening is either absent, repaired, or explicitly
  classified before completion is claimed;
- task-level obligation contract passes before editing;
- write scope is limited to the target file, direct local bridge/foundation
  files, task-local obligations, classification artifacts, and Step 8 report;
- final theorem statement changes, if any, were already accepted by Step 5 or
  Step 7.

## Implementation Rules

1. Start from the smallest final-theorem reduction.
2. Prefer replacing one public proof premise or private axiom at a time.
3. Keep final theorem statements source-faithful unless a prior statement patch
   explicitly changed the target.
4. Do not add public `Support`, `Spine`, `Bridge`, `ProofBeyondBook`, or source
   proof-step premises except the unique inherited `thm_14_8_ProofBeyondBook`
   boundary.
5. Use Step 7 lemmas by name; do not duplicate their proof bodies in final
   assembly.
6. Update `proof_obligations.json` only after the Lean landing exists and
   passes the proof-contract checks.
7. Update classification only to the level actually achieved.

## Validation

For each Step 8 target:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

If downstream callers were touched, run Lean on those files too.

Do not edit `project_ledger.json` by hand.

## Current Target Readiness

| task_id | Step 8 readiness | reason |
| --- | --- | --- |
| `prob_10_6` | complete / no action | Historical proof landed and is locked. |
| `thm_11_7` | complete / no action | Step 7/8 landed the fourth-moment route, removed `h_tail_summability`, and self-corrected the public fourth-moment package so centered assumptions are derived internally. |
| `thm_13_14` | not ready | Needs Step 7 interval-Fubini and generator-extension lemmas to remove `hIntervals` and `hExtend`. |
| `thm_14_5` | not selected | Accepted adapter unless Step 5 reopens source-spine upgrade. |
| `ex_14_4_3` | not ready | Needs fresh Step 6 selection and Step 7 local Lyapunov foundation work. |

## Completion Criteria

A Step 8 run is complete only when:

- it records the selected target and Step 7 inputs;
- it lands one of the allowed result classes;
- all touched Lean files build or failed proof attempts are removed and
  documented;
- task-local proof obligations and classification match the actual Lean result;
- no old Step 6C language is used to describe the proof-production work.
