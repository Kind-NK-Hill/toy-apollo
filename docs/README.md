# Docs Boundary

Start with the [project homepage](../README.md) or its [Chinese version](../README.zh-CN.md).
Use the [development guide](development.md) for a public clone or the
[Chinese operator guide](getting_started.zh-CN.md) for both publication and full-workspace commands.
See [project notes](project_notes.md) for research context, authorship, and related work.

This directory is for current operator runbooks and stable policy notes.
Historical migration, reorg, provider-offload, and one-off handoff notes should
not sit beside current policy.

## Current authority and history

- [Architecture](architecture.md): active package, corpus, and artifact roots.
- [Workspace state](workspace_state.md): current catalog, evidence, and external review boundaries.
- [Publication scope](repository_scope.md): what is included in a public release and how to verify it.

The complete local workspace also retains `cutover_v2.md`,
`workspace_inventory.md`, and `archive/workspace_state_pre_unified_index_20260905.md`.
Those local history and inventory documents are omitted from public exports;
the archived MAT procedures do not authorize active corpus writes.

## Demonstrations and experiments

- [Workflow demonstration](workflow_demo.md): an executable teaching example of build, review, repair, downstream migration, and apply; replay is distinct from a new model review.
- [Review-basis identity pilot](review_basis_pilot.md): a small experiment separating identity dimensions and explaining why review evidence expires; it does not grant semantic authority.
- [Prospective review comparison](review_comparison_pilot.md): a comparison protocol and runner whose empirical claims require independent adjudication; historical verdicts are not ground truth.

## Current Runtime Docs

Use these when operating or modifying Phase 2:

- `phase2/README.md`
- `phase2/workflow.md`
- `phase2/status_contract.md`
- `phase2/review_criteria.md`
- `phase2/artifacts.md`
- `phase2/tools.md`
- `workspace_state.md`
- `evidence_bridge.md`
- `workspace_inventory.md`

`phase2/textbook_complete_targets.json` is a data artifact, not a policy entry.

## Generated artifacts in the complete local workspace

These are local generated or maintained artifacts that current tools may read or
refresh. They are omitted from public releases. Preserve their paths in the
complete workspace unless the tools are updated at the same time:

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
- Removed legacy mode names such as `plan-batches`, `offload-batch`, `repair-pack`, and `repair-verify` are not active contracts.

## Search Boundary

Default active searches should use normal `rg`; `.rgignore` excludes backup, archive, generated pack, and artifact directories. Use `rg --no-ignore` only when intentionally auditing historical or generated content.

## Archive Boundary

Archived material is audit trail only. Do not use archived handoff files or old
Phase2 policy drafts as current proof-debt policy. Current generated reports
remain cache/report artifacts and do not decide completion.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
