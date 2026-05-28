# Modification 0525 Step Documents

This directory groups the Phase2 rework step plans, work queues, decision
records, and step-local evidence files.

Canonical artifacts that are consumed by tools stay in `docs/` unless the
tools are updated as part of a separate change. In particular:

- `docs/phase2_completion_classification.md`
- `docs/phase2_completion_classification.json`

The files in this directory are the narrative and execution-control documents
for the May 2026 Phase2 rework sequence. They are not the default Phase2
operator entrypoint. The stable entrypoint is `docs/phase2/`.

The historical post-Step-5 sequence was:

```text
Step 5: target selection
Step 5.5: obligation contract hardening
Step 5.6: scoped contract reconciliation
Step 6: source route extraction and expected signature freeze
Step 7: bridge / foundation lemma completion
Step 8: scoped target Lean implementation
```

Stable target selection now lives at:

- `docs/phase2/textbook_complete_targets.json`

Step 5.5 handoff files:

- `phase2_step5_5_obligation_contract_hardening_implementation_plan.md`
- `phase2_step5_5_obligation_contract_hardening_work_queue.md`
- `phase2_step5_6_contract_reconciliation_report.md`

Current Step 6 entry:

- `phase2_step6_contract_gated_textbook_completion_plan.md`

Historical Step 6 execution checkpoint:

- `phase2_step6_contract_gated_execution_report.md`

Current Step 7 entry:

- `phase2_step7_bridge_foundation_completion_plan.md`
- `phase2_step7_bridge_foundation_work_queue.md`

Current Step 8 entry:

- `phase2_step8_scoped_lean_implementation_plan.md`
- `phase2_step8_scoped_lean_work_queue.md`

Older Step 6 route and work-queue files remain historical records and must be
read through the current Step 6-8 split. In particular, old `Step 6C` language
is obsolete; proof-production now belongs to Step 7 and Step 8.

They are intentionally temporary. If a rule becomes stable policy, extract the
short rule into a current runtime doc under `docs/` or a repository agent
contract, then leave the step file here as historical execution evidence.
