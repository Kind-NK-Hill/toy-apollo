# Phase3 Soft Dependency Review

## Purpose

This document records the first review pass of the new soft-dependency batch workflow.

It focuses on three questions:

1. whether chapter 4 batch generation works structurally
2. whether chapter 3 existing soft-import state is compatible with the new workflow
3. whether the current soft-pack method truly matches the operator-driven style of the new phase2 flow

## Artifacts Generated

Generated during review:

- `phase3_softdep_packs/ch4_batch1/`
- `phase3_softdep_packs/ch3_batch_5357306/`

No `soft-apply` was run.
No problem `phase2 pack/verify` was run.
No Aristotle calls were made.

## Chapter 4 Batch Generation Check

### Result

`ch4_batch1` was generated successfully.

The directory contains:

- `batch.json`
- `operator_prompt.md`
- `problem_statements.md`
- `chapter_materials.md`
- `allowed_material_ids.json`
- `selection_schema.json`
- `soft_imports_selection.json`
- `apply_report.md`

`problem_statements.md` and `chapter_materials.md` are populated from plan content, not just ids.

### Result after type-family fix

The current `allowed_material_ids.json` for `ch4_batch1` now includes both:

- definition-family plan entries
- theorem-family plan entries

Theorem-like entries such as:

- `Theorem_with_Proof`
- `Theorem_Statement`

are now treated as theorem-family materials and included in chapter materials.

### Assessment

The batch generation is now structurally sufficient for real soft-import selection at the material-collection level.

## Chapter 3 Compatibility Check

### State-layer result

Chapter 3 problem tasks already have persisted soft imports in the ledger.

Examples:

- `prob_3_1` -> `def_3_5, thm_3_3, def_3_4, thm_3_2`
- `prob_3_2` -> `def_3_4, def_3_5, thm_3_3, thm_3_2`
- `prob_3_5` -> `def_3_4, def_3_5, thm_3_2, thm_3_3`

These satisfy the new canonical expectations:

- stored in `candidate_snapshot.soft_imports`
- ordered `list[str]`
- canonical block ids
- mixed `def/thm` references

### Pack-layer result

A representative chapter 3 batch was generated:

- `phase3_softdep_packs/ch3_batch_5357306/`

The workflow correctly:

- inferred chapter `3`
- collected chapter 3 problems into `problem_statements.md`
- generated the same artifact shape as chapter 4

### Result after type-family fix

The generated chapter 3 batch now includes theorem-family materials as well, for example:

- `thm_3_2`
- `thm_3_3`
- `thm_3_5`
- `thm_3_7`
- `thm_3_8`

This matches the fact that existing chapter 3 ledger soft imports already reference theorem ids.

### Assessment

Chapter 3 is now compatible at both:

- the state layer
- the pack-material layer

## Consistency Review Against Phase2 Prompt-Pack

### Already aligned

- Both workflows are operator-driven.
- Both generate md/json artifacts before any semantic decision is applied.
- Both keep canonical runtime state in the ledger.
- Both separate preparation from later application/promotion.
- Both are meant to let an external or human agent do the semantic work.

### Not yet fully aligned

- `phase2 prompt-pack` is task-level; `soft-pack` is batch-level.
- `phase2` has a verification stage; `soft-pack` currently has direct `apply` without a review gate.
- `phase2` has `imports.lean` and `target_stub.lean` to constrain downstream output shape; `soft-pack` has no equivalent “selection draft with enforced review” layer.
- `phase2` material scope is currently richer and better constrained by downstream validation.
- `soft-pack` is still lighter than `phase2 prompt-pack`, but its chapter-material collection now includes theorem-family plan types.

### Conclusion

The current soft-pack workflow is genuinely in the new operator-driven family, but it is not yet fully equivalent in maturity or safety to phase2 prompt-pack.

The remaining gaps are now mostly workflow-maturity gaps, not material-collection gaps.

## Immediate Recommendation

Before using soft-pack for real soft-import selection on chapter 4 problems, the next implementation focus should be:

- improving review discipline around `soft-apply`
- deciding whether soft-pack needs a stronger intermediate review stage, similar to `phase2 verify`
