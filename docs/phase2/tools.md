# Phase2 Tools

Tools are diagnostics unless explicitly named as one of the three gates in the
default workflow.

## Build Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
```

This is the technical build gate. It does not prove textbook fidelity.

## Diagnostics

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>
python .\run_chapter.py --phase 2 --phase2-mode batch-run --tasks <task_id>,<task_id> --batch-max-actions 1
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id> --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers 5
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/validate_phase2_obligation_contracts.py --write-report
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
python .\run_chapter.py --phase 2 --phase2-mode verify --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode audit --tasks <task_id>
```

`batch-plan` is the thin scheduling view over the current ledger and Phase2
status metadata. It reports whether each selected task should run fresh existing
review, enter `auto-loop`, or wait for an upstream blocker. It does not run
repair, write completion, or replace review/apply.

`batch-run` executes a small number of actions from that same plan. It only
dispatches existing Phase2 actions such as fresh existing review and
`auto-loop`; it does not decide completion by itself.

For chapter-wide work, use `--batch-task-kinds theorem,definition` to prioritize
non-Problem root tasks, `--batch-limit` to cap the queue, and `--batch-workers`
to annotate worker slots for subagent assignment. Worker slots are coordination
labels only; the operator still creates independent author/reviewer subagents
and must not let two workers edit the same task pack or official output.

The other commands can find stale evidence, missing contracts, public-surface
debt, classification inconsistencies, and review/build diagnostics. These tools
are not completion authorities. Their results must feed semantic review or
repair.

## Maintenance

```powershell
python .\run_chapter.py --phase 2 --phase2-mode debt-fix --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode promote-obligations --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id> --review-subject current
```

`auto-loop` is the default repair runner after a failed semantic review. Its
normal budget and CLI floor are 15 review rounds and 15 build-check attempts
before each review round. After a semantic failure, unchanged candidates are
sent back to authoring instead of semantic review; change `draft.lean` or the
proof artifact before continuing. `debt-fix` prepares repair for accepted proof debt.
`promote-obligations` creates child obligation tasks. Both return to the
auto-loop/build/review/apply workflow.
