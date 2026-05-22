# Phase 2 Chapter 11-14 Runner A

## Scope

Runner A owns the foundation side of the Chapter 11-14 Phase 2 run:

- Chapter 11 non-remark, non-problem tasks
- Chapter 12 non-remark, non-problem tasks
- Chapter 13.1-13.3 foundation tasks

Source units:

- `chapter11-bounds-inequalities`
- `chapter11-weak-law-large-numbers`
- `chapter11-strong-law-large-numbers`
- `chapter12-l2-norm-inner-product`
- `chapter12-closed-subspace-projection`
- `chapter12-orthogonality-principle`
- `chapter12-mmse-estimation`
- `chapter13-finite-partition`
- `chapter13-sub-sigma-algebra`
- `chapter13-properties`

## Priority Unblockers

Runner A should complete these early because Runner A or Runner B depends on them:

- `prob_12_2`: required before `thm_12_3`
- `prob_12_1`: required before `thm_12_4`
- `thm_12_6`: Runner B must wait for this before `def_13_7`
- `thm_13_8`: Runner B must wait for this before `thm_13_15`
- `thm_13_5`: Runner B must wait for this before `thm_14_4`

Textbook order for the Chapter 12 projection chain is mandatory:
complete `def_12_5` and `thm_12_5` after `thm_12_4` before attempting
`thm_12_6`. The nonlinear MMSE discussion in `thm_12_6` uses both the
Projection Theorem and the Orthogonality Principle.

Textbook order for the Chapter 13 conditional-expectation chain is mandatory:
complete `def_13_3`, `thm_13_4`, and `thm_13_6` before attempting `thm_13_8`.
Complete `thm_13_5` before `thm_13_6`, since existence of conditional
expectation is derived from Radon-Nikodym in the text.

`prob_12_1` and `prob_12_2` are Problem tasks. Run the Problem soft-dependency flow before normal Phase 2:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_12_1,prob_12_2
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks prob_12_1,prob_12_2 --selection <selection-json>
```

Then run the normal single-task Phase 2 loop task by task:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <result-json>
```

`review-apply` is not allowed to infer the result path. Use the exact
`expected_result_file` from the current `semantic_review_request_vM.json`, usually:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result .\phase2_prompt_packs\<task_id>\semantic_review_result_vM.json
```

For a pass result, keep the binding fields from
`semantic_review_result_template_vM.json` unchanged and use the schema hints in
that template. In particular:

- section statuses use `covered`, `partial`, `missing`, `violated`, or `unclear`
- `obligation_review.items[*].status` also allows `not_applicable` and `accepted_as_proof_debt`
- every direct downstream consumer needs a `consumers_checked` object:
  `{"block_id": "<consumer>", "status": "covered|not_applicable|blocked", "evidence": "..."}`
- `forbidden_weakenings[*].status` uses `not_present`, `present`, or `not_applicable`

## Coordination Notes

- Tell Runner B when `thm_12_6`, `thm_13_8`, and `thm_13_5` are completed.
- Do not edit Runner B's task files or prompt packs.
- If any priority unblocker hard-stops, record the stop reason and notify Runner B because it may create dependency-failed tasks in Runner B's scope.
