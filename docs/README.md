# Docs Boundary

This directory is for current operator runbooks and stable policy notes.
Historical migration, reorg, provider-offload, and one-off handoff notes should
not sit beside current policy. If a historical note must remain available, put
it under `docs/archive/` and mark it as non-authoritative.

## Current Runtime Docs

Use these when operating or modifying Phase 2:

- `phase2/README.md`
- `phase2/proof_fidelity_contract.md`
- `phase2/workflow.md`
- `phase2/candidate_guidelines.md`
- `phase2/review_loop_protocol.md`
- `phase2/debt_cleanup_playbook.md`
- `phase2/classification_policy.md`
- `phase2/tools.md`
- `phase2/current_corpus_status.md`
- `phase2/textbook_completion_rework_policy.md`
- `phase2/textbook_complete_targets.json`

Legacy root-level Phase 2 Markdown files are compatibility redirects only. Do
not use them as the default policy source.

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

## Step And Temporary Docs

- `modification_0525_steps/` contains temporary step plans, queues, decision
  records, and postmortems for the May 25 Phase2 redesign work. These files are
  execution-control evidence, not stable runtime policy. Current tools may keep
  a legacy fallback for old worktrees, but active target selection belongs under
  `docs/phase2/`.
- One-off diagnostic reports should go under `docs/archive/`, not root `docs/`.

## Policy Notes

Use these when changing dependency modeling or source-plan boundaries:

- `chapter1_2_cross_chapter_dependency.md`
- `dependency_decision_trail.md`
- `interface_dependency_policy.md`

## Runtime Boundary

- Problem soft dependency selection is a Phase 2 special case: `--phase 2 --phase2-mode soft-pack/soft-apply`.
- Phase 3 is merged into Phase 2 and does not run an external provider, create execution batches, repair harvested output, or verify Lean.
- Phase 4 is disabled/no-op in the current CLI.
- Removed legacy mode names such as `plan-batches`, `offload-batch`, `repair-pack`, and `repair-verify` are not active contracts.

## Search Boundary

Default active searches should use normal `rg`; `.rgignore` excludes backup, archive, generated pack, and artifact directories. Use `rg --no-ignore` only when intentionally auditing historical or generated content.

## Archive Boundary

- `docs/archive/outdated_agent_handoffs/` contains old batch/handoff service
  notes. They are audit trail only.
- `docs/archive/phase2_diagnostic_reports_2026-05-21/` contains one-off
  diagnostic reports and manifests from the May 2026 proof-debt cleanup.
- `docs/archive/phase2_2026_05_rework/` contains full copies of the old long
  Phase 2 docs and May 25 step records.
- Do not use archived handoff files as current proof-debt policy.
- Current Chapter 10-14 proof-debt truth comes from
  `tools/audit_phase2_clean_debt_surface.py` and its generated reports.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
