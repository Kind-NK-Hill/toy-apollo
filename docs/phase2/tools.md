# Phase2 Tools

Tools are diagnostics unless explicitly named as one of the three gates in the
default workflow.

## Build Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
```

This is the technical build gate. It does not prove textbook fidelity.
For Math Review Gate tasks, it refuses to write a candidate until the latest
`math_review_result_vN.json` verdict is `go`.

## Diagnostics

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>
python .\run_chapter.py --phase 2 --phase2-mode batch-run --tasks <task_id>,<task_id> --batch-max-actions 1
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id> --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers 5
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/validate_phase2_obligation_contracts.py --write-report
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
python tools/snapshot_phase2_current_status.py --write
python .\run_chapter.py --phase 2 --phase2-mode verify --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode audit --tasks <task_id>
```

`batch-plan` is the thin scheduling view over the current ledger and Phase2
status metadata. It reports whether each selected task should run fresh existing
review, enter `auto-loop`, run the Math Review Gate, or wait for an upstream
blocker. It does not run repair, write completion, or replace review/apply.
When a Math Review Gate row blocks authoring, the reason includes the compressed
pre-author checklist: source statement, no public premise relocation, reviewed
math skeleton with `go`, and independent semantic review after build.

`batch-run` executes a small number of actions from that same plan. It only
dispatches existing Phase2 actions such as fresh existing review and
`auto-loop`; it does not decide completion by itself.

For chapter-wide work, use `--batch-task-kinds theorem,definition` to prioritize
non-Problem root tasks, `--batch-limit` to cap the queue, and `--batch-workers`
to annotate worker slots for subagent assignment. Worker slots are coordination
labels only; the operator still creates independent author/reviewer subagents
and must not let two workers edit the same task pack or official output. A
`math_review_gate_required` row is not an author worker action; dispatch or run
the natural language proof skeleton and independent read-only math reviewer
first.

The default `batch-plan` view is parent-facing. Current ledgers should not keep
legacy `obl_*` child tasks, but the scheduler can quarantine legacy `obl_*` and
nested `obl_obl_*` rows when reading old fixtures or imported state. It also
hides diagnostic restore/rebuild rows that should not displace real
author/review work. The plan prints a `hidden legacy/audit items` summary line.
Use `--batch-include-legacy` only when deliberately auditing quarantined
obligation history.

`restore_or_rebuild_output` is default-queue work only when the parent has no
official output and no usable draft/build/review candidate. If a candidate
exists, the row is diagnostic context rather than top-queue work.

The other commands can find stale evidence, missing contracts, public-surface
debt, classification inconsistencies, and review/build diagnostics. These tools
are not completion authorities. Their results must feed semantic review or
repair.

`tools/snapshot_phase2_current_status.py --write` creates a small tracked
summary of the ignored runtime ledger. It is audit context for git history only;
it must not be used to declare completion outside `review-apply`.

## Maintenance

```powershell
python .\run_chapter.py --phase 2 --phase2-mode debt-fix --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id> --review-subject current
```

`auto-loop` is the default repair runner after a failed semantic review. Its
normal budget and CLI floor are 15 review rounds and 15 build-check attempts
before each review round. After a semantic failure, unchanged candidates are
sent back to authoring instead of semantic review; change `draft.lean` or the
proof artifact before continuing. `debt-fix` prepares repair for accepted proof debt.
Proof obligations are no longer promoted into `obl_*` child tasks. If a proof
obligation is real, absorb it into the parent file or a stable non-`obl_*`
support file, then return to the auto-loop/build/review/apply workflow.

`foundation-scan` and `foundation-propose` are reserved names for future
foundational-support planning tools. They are not current CLI modes. When they
exist, they must remain maintenance planning/report tools: they may identify
super-long official files and historical `obl_*` declaration dependencies, or
propose a specific reorganization, but they must not write `phase2_status`,
replace semantic review, or invoke the diagnoser.
