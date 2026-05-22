# Phase 2 Chapter 11-14 Runner B

## Scope

Runner B begins with the Chapter 11 problem set, then owns the later Chapter 13 and Chapter 14 side of the Chapter 11-14 Phase 2 run:

- Chapter 11 problem tasks: `prob_11_1` through `prob_11_10`
- Chapter 13.4-13.6 tasks
- Chapter 14 non-remark, non-problem tasks

Source units:

- `chapter11-problems`
- `chapter13-discrete-random-variable`
- `chapter13-continuous-random-variable`
- `chapter13-martingale-stopping-time`
- `chapter14-weak-convergence`
- `chapter14-tightness`
- `chapter14-prokhorov-sequential-compactness`
- `chapter14-central-limit-theorems`

## Required Waits

Runner B can work on independent tasks immediately, but these three tasks must wait for Runner A:

- `def_13_7` waits for `thm_12_6`
- `thm_13_15` waits for `thm_13_8`
- `thm_14_4` waits for `thm_13_5`

Do not start normal Phase 2 authoring for those three tasks until the corresponding Runner A task is completed and available in `ToyApollo/Output`.

## Chapter 11 Problems First

Before Chapter 13 or Chapter 14 work, Runner B should process the Chapter 11 problem tasks:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_11_1,prob_11_2,prob_11_3,prob_11_4,prob_11_5,prob_11_6,prob_11_7,prob_11_8,prob_11_9,prob_11_10
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks prob_11_1,prob_11_2,prob_11_3,prob_11_4,prob_11_5,prob_11_6,prob_11_7,prob_11_8,prob_11_9,prob_11_10 --selection <selection-json>
```

After soft imports are confirmed, run the normal single-task Phase 2 loop for each problem.

The Chapter 11 problem tasks are not part of Runner A's completed Chapter 11 non-remark, non-problem scope.

## Normal Route

For each unblocked task, run the normal single-task Phase 2 loop:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <result-json>
```

## Chapter 14 Bridge Note

`thm_10_6` is not a prerequisite for Chapter 14 work.

The direction is the other way around: `thm_10_6` is a downstream Chapter 10 bridge task whose proof depends on `thm_14_2` and `thm_14_4`. Runner B should not import or wait on `thm_10_6` when working on Chapter 14.

## Coordination Notes

- If Runner A reports `thm_12_6`, `thm_13_8`, or `thm_13_5` as hard-stopped, mark the dependent Runner B task as blocked for the current batch rather than trying to bypass the dependency.
- Do not edit Runner A's task files or prompt packs.
- Re-check `project_ledger.json` and `ToyApollo/Output/<dependency>.lean` before starting a waited task.
