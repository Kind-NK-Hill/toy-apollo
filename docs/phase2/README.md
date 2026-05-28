# Phase2 Current Docs

This directory is the current Phase2 policy and operator entrypoint. Use these
files before reading historical notes.

## Reading Order

For normal execution, read only the files that match the role:

- deciding whether a task is really complete: `proof_fidelity_contract.md`;
- running Phase2 commands: `workflow.md`;
- writing Lean: `candidate_guidelines.md`;
- cleaning accepted debt: `debt_cleanup_playbook.md`;
- updating classification artifacts: `classification_policy.md`;
- finding validation commands: `tools.md`;
- checking a short pattern: `examples.md`.

Avoid reading every policy file before each task. The stable docs are an index
plus role-specific contracts, not a single linear manual.

## Current Policy Boundary

Current policy lives in `docs/phase2/`. Root-level legacy files such as
`docs/phase2_prompt_pack_workflow.md` are compatibility redirects. Historical
May 2026 redesign notes live under:

- `docs/archive/phase2_2026_05_rework/`
- `docs/modification_0525_steps/`

`docs/modification_0525_steps/` remains in place because current tools still
may read legacy evidence from there for compatibility. It is execution
evidence, not the default policy source.

## Migration Map

| Old path | Current path | Archive copy |
| --- | --- | --- |
| `docs/phase2_proof_fidelity_contract.md` | `docs/phase2/proof_fidelity_contract.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_proof_fidelity_contract.md` |
| `docs/phase2_prompt_pack_workflow.md` | `docs/phase2/workflow.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_prompt_pack_workflow.md` |
| `docs/phase2_candidate_guidelines.md` | `docs/phase2/candidate_guidelines.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_candidate_guidelines.md` |
| `docs/proof_debt_next_llm_playbook.md` | `docs/phase2/debt_cleanup_playbook.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/proof_debt_next_llm_playbook.md` |
| `docs/phase2_review_loop_protocol.md` | `docs/phase2/review_loop_protocol.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_review_loop_protocol.md` |
| `docs/phase2_problem_soft_dependency_workflow.md` | `docs/phase2/problem_soft_dependency_workflow.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_problem_soft_dependency_workflow.md` |
| `docs/phase2_batch_controller.md` | `docs/phase2/batch_controller.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_batch_controller.md` |
| `docs/phase2_ch10_14_clean_debt_goals.md` | `docs/phase2/current_corpus_status.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_ch10_14_clean_debt_goals.md` |
| `docs/phase2_proof_debt_foundation_plan.md` | `docs/phase2/textbook_completion_rework_policy.md` | `docs/archive/phase2_2026_05_rework/current_root_docs/phase2_proof_debt_foundation_plan.md` |
| `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json` | `docs/phase2/textbook_complete_targets.json` | `docs/archive/phase2_2026_05_rework/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json` |
| `docs/modification_0525_steps/*` | historical reports only | `docs/archive/phase2_2026_05_rework/modification_0525_steps/` |

## Rule For Agents

Do not treat Lean build success, clean ledger state, or clean audit output as
textbook proof completion. A proof-bearing task is clean only when the public
statement, public assumptions, proof route, dependencies, and metadata all match
the contract in `proof_fidelity_contract.md`.

## Doc Hygiene

Keep durable rules under `docs/phase2/` and avoid adding new policy only to
historical step reports. When a new rule is procedural, put it in `workflow.md`;
when it defines proof meaning, put it in `proof_fidelity_contract.md`; when it
guides Lean authoring, put it in `candidate_guidelines.md`. Do not duplicate the
same case study across all files.
