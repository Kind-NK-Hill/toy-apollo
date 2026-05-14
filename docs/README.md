# Docs Boundary

This directory is for current operator runbooks and stable policy notes. Historical migration, reorg, provider-offload, and one-off handoff notes were removed from the tracked docs; use git history if you need to audit them.

## Current Runtime Docs

Use these when operating or modifying the current pipeline:

- `phase2_prompt_pack_workflow.md`
- `phase2_candidate_guidelines.md`
- `phase2_review_loop_protocol.md`
- `phase3_soft_dependency_workflow.md`

## Policy Notes

Use these when changing dependency modeling or source-plan boundaries:

- `chapter1_2_cross_chapter_dependency.md`
- `dependency_decision_trail.md`
- `interface_dependency_policy.md`

## Runtime Boundary

- Current Phase 3 is only Problem soft dependency selection: `soft-pack` and `soft-apply`.
- Phase 3 does not run an external provider, create execution batches, repair harvested output, or verify Lean.
- Phase 4 is disabled/no-op in the current CLI.
- Removed legacy mode names such as `plan-batches`, `offload-batch`, `repair-pack`, and `repair-verify` are not active contracts.

## Search Boundary

Default active searches should use normal `rg`; `.rgignore` excludes backup, archive, generated pack, and artifact directories. Use `rg --no-ignore` only when intentionally auditing historical or generated content.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
