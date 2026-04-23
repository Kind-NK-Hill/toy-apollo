# Chapter 7 Soft-Pack Selection Design

## Goal

Generate a first-pass `phase3` soft-dependency pack for chapter 7 problems, then produce:

1. a chapter-local `selection.json` that is valid for the current CLI and can be used with `soft-apply`
2. a separate advisory note listing cross-chapter candidates that may be semantically useful but cannot be written into the current `selection.json`

## Context

The active runtime root for this work is:

- `D:\Grad_Study\Practimum\Formalization\toy-apollo`

Relevant source materials already exist:

- chapter 7 problem input: `inputs/30_chap7_problems.tex`
- chapter 7 problem plan: `plans/30_chap7_problems_plan.json`
- chapter 7 supporting chapter plans: `plans/25_chap7_*.json` through `plans/29_chap7_*.json`
- ledger: `project_ledger.json`

Chapter 7 problem tasks are already present in the ledger as:

- `prob_7_1` through `prob_7_9`

Their current status is `DISCOVERED`, so the correct workflow is the operator-driven `phase3` problem path, not the default `FAILED_LOCAL` offload queue.

## Constraints

### Hard CLI constraint

The current `soft-pack` / `soft-apply` implementation only accepts selections from `allowed_material_ids.json`.

Implementation evidence:

- `src/toy_apollo/phase3_softdep_pack.py` instructs the operator to select only from `allowed_material_ids.json`
- `soft-apply` validates every selected id against that file and rejects any out-of-scope id

### Practical consequence

Cross-chapter support cannot be encoded into the current executable `selection.json` unless the CLI or pack-generation logic is changed first.

Therefore:

- executable output must remain chapter-local
- cross-chapter suggestions must be emitted separately as advisory analysis

## Selection Strategy

Use a balanced strategy:

- prefer the smallest sufficient chapter-local import set
- include direct chapter 7 theorems when the problem clearly targets Fatou/DCT, Stieltjes integration, change of variable, or product expectation ideas
- avoid selecting the whole chapter by default
- allow zero selections for problems whose chapter-local support is not clearly necessary from the statement alone

Cross-chapter allowance is handled as advisory review only:

- if a problem appears to need earlier chapter material semantically, record it in a side note
- do not place those ids into the executable `selection.json`

## Outputs

This work produces:

1. a generated `phase3_softdep_packs/<batch_id>/` directory for chapter 7 problems
2. a first-pass executable `selection.json` for `prob_7_1` through `prob_7_9`
3. a short advisory markdown note for cross-chapter candidate materials, if any are identified

This work does not:

- run `soft-apply`
- modify ledger soft imports
- run Aristotle offload
- change `phase3` implementation semantics

## Verification

The selection output is considered valid only if:

1. every key is one of `prob_7_1` through `prob_7_9`
2. every selected material id appears in the generated `allowed_material_ids.json`
3. the JSON is parseable and ordered as intended
4. no ledger state is changed during this pass

## Decision

Proceed with:

- chapter 7 `soft-pack`
- chapter-local executable selection draft
- separate cross-chapter advisory note

Do not attempt cross-chapter `soft-apply` within the current CLI contract.
