# Docs Boundary

This directory mixes active operator runbooks with historical audit notes. Treat the categories below as the default reading order.

## Active Runtime Docs

Use these when operating or modifying the current pipeline:

- `phase2_prompt_pack_workflow.md`
- `phase2_candidate_guidelines.md`
- `phase2_review_loop_protocol.md`
- `phase3_soft_dependency_workflow.md`
- `phase3_execution_batch_workflow.md`
- `phase3_post_harvest_workflow.md`
- `phase3_post_harvest_guidelines.md`
- `dependency_decision_trail.md`
- `interface_dependency_policy.md`

## Historical Or Inspection Docs

These are useful for understanding why the repo looks this way, but they are not runtime contracts:

- `unsolved_closure_runbook.md` (legacy closure guidance; current Phase 4 automation is disabled)
- `phase2_inventory.md`
- `phase3_softdep_review.md`
- `chapter1_2_cross_chapter_dependency.md`
- `workspaces.md`

## Archive And Migration Notes

These should not be searched as active surface unless you are auditing history:

- `reorg.md`
- `reorg/`
- `superpowers/`
- `2026-04-20-old-*.md`

## Search Boundary

Default active searches should use normal `rg`; `.rgignore` excludes backup, archive, generated pack, and artifact directories. Use `rg --no-ignore` only when intentionally auditing historical or generated content.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
