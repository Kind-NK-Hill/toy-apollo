# Modification 0525 Step Documents

This directory groups the Phase2 rework step plans, work queues, decision
records, and step-local evidence files.

Canonical artifacts that are consumed by tools stay in `docs/` unless the
tools are updated as part of a separate change. In particular:

- `docs/phase2_completion_classification.md`
- `docs/phase2_completion_classification.json`

The files in this directory are the narrative and execution-control documents
for Step 1 through Step 6.

They are intentionally temporary. If a rule becomes stable policy, extract the
short rule into a current runtime doc under `docs/` or a repository agent
contract, then leave the step file here as historical execution evidence.
