# Docs Boundary

This directory is for current operator runbooks and stable policy notes.
Historical migration, reorg, provider-offload, and one-off handoff notes should
not sit beside current policy.

## Current Runtime Docs

Use these when operating or modifying Phase 2:

- `phase2/README.md`
- `phase2/workflow.md`
- `phase2/status_contract.md`
- `phase2/review_criteria.md`
- `phase2/artifacts.md`
- `phase2/tools.md`
- `workspace_state.md`

`phase2/textbook_complete_targets.json` is a data artifact, not a policy entry.

## Current Generated Artifacts

These are generated or maintained artifacts that current tools may read or
refresh. Keep them in root `docs/` unless the tools are updated at the same time:

- `phase2_completion_classification.md`
- `phase2_completion_classification.json`
- `phase2_ch10_14_clean_debt_surface_audit.md`
- `phase2_ch10_14_clean_debt_surface_audit.json`
- `phase2_unfinished_tasks_audit.md`
- `phase2_unfinished_tasks_audit.json`
- `phase2_source_output_alignment_audit.md`

These are reports/cache. They do not decide Phase2 completion. Current state is
queried from the local workspace database; it is not checked in as a snapshot.

Short-lived manifest files produced by cleanup tools should not be kept in this
root directory unless a current tool reads them as input. Tools that need those
manifests can regenerate them.

## Step And Temporary Docs

Historical step plans, queues, decision records, postmortems, and one-off
diagnostic reports are audit trail only. They are not stable runtime policy and
should not appear in the default docs surface.

Current handoff notes for an active run should live with generated run reports,
for example under `phase2_prompt_packs/_reports/`, not in `docs/phase2/`.

## Policy Notes

Use these when changing dependency modeling or source-plan boundaries:

- `chapter1_2_cross_chapter_dependency.md`
- `dependency_decision_trail.md`
- `interface_dependency_policy.md`

## Runtime Boundary

- Problem soft dependency selection is a Phase 2 special case with two active entries: `--phase 2 --phase2-mode soft-pack` and `--phase 2 --phase2-mode soft-apply`.
- Phase 3 is deprecated/unavailable; its old entries exit nonzero with the Phase 2 migration commands and do not run an external provider, create execution batches, repair harvested output, or verify Lean.
- Phase 4 is unavailable and exits nonzero; clean completion remains under Phase 2 `review-apply`.
- Removed legacy mode names such as `plan-batches`, `offload-batch`, `repair-pack`, and `repair-verify` are not active contracts.

## Search Boundary

Default active searches should use normal `rg`; `.rgignore` excludes backup, archive, generated pack, and artifact directories. Use `rg --no-ignore` only when intentionally auditing historical or generated content.

## Archive Boundary

Archived material is audit trail only. Do not use archived handoff files or old
Phase2 policy drafts as current proof-debt policy. Current generated reports
remain cache/report artifacts and do not decide completion.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
