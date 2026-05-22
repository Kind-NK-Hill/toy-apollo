# Docs Boundary

This directory is for current operator runbooks and stable policy notes.
Historical migration, reorg, provider-offload, and one-off handoff notes should
not sit beside current policy. If a historical note must remain available, put
it under `docs/archive/` and mark it as non-authoritative.

## Current Runtime Docs

Use these when operating or modifying the current pipeline:

- `phase2_prompt_pack_workflow.md`
- `phase2_problem_soft_dependency_workflow.md`
- `phase2_candidate_guidelines.md`
- `phase2_review_loop_protocol.md`
- `proof_debt_next_llm_playbook.md`
- `phase2_ch10_14_clean_debt_goals.md`
- `phase2_ch10_14_clean_debt_surface_audit.md`

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
- Do not use archived handoff files as current proof-debt policy.
- Current Chapter 10-14 proof-debt truth comes from
  `tools/audit_phase2_clean_debt_surface.py` and its generated reports.

## Legacy Metadata

Names such as `legacy_ids`, `legacy_ids_for`, and `legacy_inferred` are compatibility and audit metadata. They are not the old Gemini/DeepSeek direct-generation pipeline.
