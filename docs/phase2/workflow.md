# Phase2 Workflow

The only default Phase2 workflow is:

```text
pack -> edit draft -> build-check -> review-now -> review-apply
```

## 1. Pack

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
```

This writes `phase2_prompt_packs/<task_id>/` with the task, source context,
dependency context, draft, proof-obligation checklist when applicable, and
review materials.

## 2. Edit Draft

Edit:

```text
phase2_prompt_packs/<task_id>/draft.lean
```

Do not edit `project_ledger.json` by hand. Do not treat old candidate,
classification, audit, or verify files as completion evidence.

## 3. Build Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
```

The build gate writes `candidate_vN.lean` and `build_result_vN.json`. Passing
this gate only means the candidate is technically ready for review. It does not
mean the theorem/problem/exercise is complete.

## 4. Semantic Review Gate

For a build-ready candidate:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
```

For an already runnable official output:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing
```

The reviewer must be independent and read-only. The reviewer must inspect the
source TeX, Lean subject, proof obligations, audit/classification/dependency
evidence, downstream/import evidence, ledger status, and freshness/hash
evidence. See [review_criteria.md](review_criteria.md).

## 5. Apply Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
```

`review-apply` validates the review result, freshness, hashes, schema, reviewer
independence, and task-level projection. It lands clean completion only when
the semantic review is valid and `phase2_status=pass`.

If reviewer verdict is `pass` but `phase2_status` is `fail`, `blocked`, or
`allowed_exception`, `review-apply` records the result and does not promote a
candidate as clean completion. `allowed_exception` is only for the explicit
`thm_14_8` beyond-book case.

Failed or inconclusive existing-output review preserves official output by
default and records repair-required evidence. Quarantine is explicit
maintenance after downstream/import checks, not the default apply outcome.

## 6. Repair Loop

After a failed or inconclusive review, repair with the runtime loop:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode auto-loop --tasks <task_id> --review-subject current
```

The default auto-loop budget and CLI floor are hard-coded to 15 review rounds
and 15 build-check attempts before each review round. Do not replace this with
an ad hoc sequence of `review-fix`, `build-check`, `review-now`, and
`review-apply` unless you are doing a local diagnostic and will immediately
return to `auto-loop`.

When `auto-loop` reports a reviewer step, the authoring agent must use an
independent read-only reviewer subagent, write the requested result file, and
continue the same loop. When it reports a build failure, repair `draft.lean`
and continue the same loop.

After a semantic review failure, `auto-loop` will not send the same candidate
hash back to semantic review. If build succeeds but the candidate is unchanged,
the loop returns to authoring; the agent must modify `draft.lean` or the
related Lean proof artifact before continuing. This counts against the current
round's build budget, not as a new review round.

A precise missing lemma, bridge theorem, or source-route gap is not a terminal
success condition. It is the next repair target for the loop unless the current
goal explicitly asks only for diagnosis.

## 7. Batch Planning

For a group of tasks, first ask the runtime for a read-only scheduling view:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>
```

`batch-plan` reads the ledger and existing Phase2 metadata, then tells the
operator which tasks need fresh existing review, which should enter `auto-loop`,
and which are blocked by upstream tasks. It is a scheduler/report only. It does
not execute repair and cannot land completion.

For a larger repair push, ask for a worker queue instead of manually picking
tasks:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id> --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers 5
```

This keeps Problem tasks out of the first queue, ranks candidates by downstream
fanout after dependency analysis, and prints worker slots plus conflict groups.
The worker slots are for subagent coordination only. They do not create
subagents, bypass review independence, or make batch planning a completion
authority.

To let the runtime advance a bounded number of selected actions:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-run --tasks <task_id>,<task_id> --batch-max-actions 1
```

`batch-run` is only a dispatcher over existing single-task actions. Completion
still lands only through `review-apply` with `phase2_status=pass`.

## Non-Default Paths

- `verify`: diagnostics/report only; it does not land completion.
- `audit`: diagnostics/report only; it does not quarantine by default and does
  not complete a task.
- `review-pack`, `review-existing`, `review-existing-queue`: prepare review
  materials; not completion authority.
- `debt-fix`: maintenance repair path for accepted proof debt; not proof.
- `promote-obligations`: maintenance path that creates child obligation tasks;
  child tasks still need the normal workflow.
- `soft-pack` and `soft-apply`: Problem soft-dependency selection only; not a
  Lean acceptance gate.

## Stops

Stop as clean only on `phase2_status=pass` through `review-apply`. Otherwise
report `fail`, `blocked`, or the explicit allowed exception and continue repair
or dependency handling.
