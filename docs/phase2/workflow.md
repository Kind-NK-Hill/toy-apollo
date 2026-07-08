# Phase2 Workflow

The only default Phase2 workflow is:

```text
pack -> edit draft -> build-check -> review-now -> review-apply
```

For tasks that trigger the Math Review Gate, the author/build entry is:

```text
pack -> natural language proof skeleton -> xhigh independent math review, 3 rounds -> theorem-shape go/stop -> edit draft -> build-check
```

## 1. Pack

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
```

This writes `phase2_prompt_packs/<task_id>/` with the task, source context,
dependency context, draft, proof-obligation checklist when applicable, and
review materials.

## 2. Math Review Gate

Most small tasks do not use this gate. It is mandatory before Lean author/build
when a task carries a route-risk signal such as:

- `semantic_fail_public_premise*` or another public-premise relocation signal;
- `source_mismatch` or statement/source mismatch;
- `needs_concrete_decomposition`;
- repeated build/review/auto-loop failures where the task is visibly
  struggling and the missing mathematical route is not yet clear;
- historical nested `obl_obl_*` evidence in an imported legacy ledger;
- dirty or blocked family state;
- parent theorem setup that exposes a core proof result as a public premise;
- pilot large analysis/probability tasks such as `prob_14_1` and `prob_14_8`.

For these tasks the normal practice is to write the mathematical proof route in
natural language first, before authoring more Lean.  The skeleton should state
the source claim, the textbook proof route, the intended theorem shape, the
available local/Mathlib support, and any support obligations that must be
proved.  Only after an independent read-only Math Review Gate result returns
`go` should the operator resume Lean author/build for the parent task.

The gate requires:

- `math_proof_skeleton_vN.md`: source statement, textbook proof route, theorem
  shape alignment, available Mathlib/local support, required parent-owned
  support theorems, public setup fields to delete or demote, and minimal Lean
  theorem skeletons;
- `math_review_result_vN.json`: independent read-only xhigh math review across
  three rounds: source statement, proof-route closure, and Lean theorem-shape
  feasibility.

The verdict controls only whether Lean author/build may start:

- `go`: authoring may proceed to `draft.lean` and `build-check`;
- `stop`: do not author Lean; report the minimal parent/support rewrite
  direction first.

The gate should stay compressed to four pre-author checks: source statement
identified; parent theorem/interface has no public premise relocation; the math
proof skeleton has been reviewed with verdict `go`; and any build-ready
candidate still goes through independent semantic review plus `review-apply`.

This gate is not completion authority. It must not edit `project_ledger.json` by
hand, must not restore `promote-obligations`, must not create nested `obl`
tasks, and must not replace semantic review or `review-apply`.

The runtime records Math Review Gate evidence in pack metadata/status fields:
`math_review_gate_required`, `math_review_gate_status`,
`latest_math_proof_skeleton_file`, `latest_math_proof_skeleton_hash`,
`latest_math_review_result_file`, `latest_math_review_result_hash`, and
`latest_math_review_verdict`. These fields are evidence for author/build
eligibility only.

## 3. Edit Draft

Edit:

```text
phase2_prompt_packs/<task_id>/draft.lean
```

Do not edit `project_ledger.json` by hand. Do not treat old candidate,
classification, audit, or verify files as completion evidence.

## 4. Build Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
```

The build gate writes `candidate_vN.lean` and `build_result_vN.json`. Passing
this gate only means the candidate is technically ready for review. It does not
mean the theorem/problem/exercise is complete.

For Math Review Gate tasks, `build-check` stops before writing a candidate until
the latest math review verdict is `go`.

## 5. Semantic Review Gate

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

### Route Inspection Gate

Route inspection is a small required section of semantic review, not a new
completion authority. It is meant to stop wrong-route work early while keeping
completion under the normal parent/support `review-apply` gate.

Route inspection is especially mandatory when any of these signals appear:

- `semantic_fail_public_premise*` or another public-premise relocation signal;
- `needs_concrete_decomposition`;
- historical nested `obl_obl_*` evidence or dirty/blocked family state;
- parent route and source statement/answer visibly disagree;
- family closure says old `obl` material was absorbed but the parent/support
  route has not been independently reviewed.

The reviewer records:

- `source_route`;
- `expected_answer_or_statement`;
- `local_mathlib_search`;
- `public_interface_check`;
- `support_or_reassembly_decision`;
- `stop_go_verdict`.

`obl` is no longer a task type or public import surface. `proof_obligations.json`
is checklist/review context only. A family closure report may say what should be
reassembled, renamed, or deleted, but it must not create child tasks, write clean
status, or replace parent/support `build-check -> review-now -> review-apply`.

## 6. Apply Gate

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <path>
```

`review-apply` validates the review result, freshness, hashes, schema, reviewer
independence, and task-level projection. It lands clean completion only when
the semantic review is valid and `phase2_status=pass`.

If reviewer verdict is `pass` but `phase2_status` is `fail`, `blocked`, or
`allowed_exception`, `review-apply` records the result and does not promote a
candidate as clean completion. `allowed_exception` is only for explicit
task/class pairs documented in [status_contract.md](status_contract.md), such as
`thm_11_8`'s cited external Etemadi proof boundary and the `thm_14_8`
beyond-book case.

Failed or inconclusive existing-output review preserves official output by
default and records repair-required evidence. Quarantine is explicit
maintenance after downstream/import checks, not the default apply outcome.

## 7. Repair Loop

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

Semantic review failures are triaged before ordinary repair. If the failed
review reads as a route/source/statement problem, such as a Mathlib-backed
adapter, public-premise relocation, private axiom, open math debt, source
mismatch, statement mismatch, or unclear semantic route failure, Phase2 writes:

```text
semantic_fail_triage_vN.json
prepared_diagnoser_prompt_vN.txt
```

and pauses ordinary `auto-loop` repair with `diagnoser_required`. The diagnoser
is read-only route diagnosis, not a second semantic reviewer and not an author.
It must not edit Lean files, official output, or the ledger. If the review only
reports a missing small/medium lemma inside an accepted route, Phase2 continues
ordinary repair without generating another diagnoser prompt.

`reviewer_required` and `diagnoser_required` are not user-blocked states when
subagent tools are available. They mean the main worker must dispatch an
independent read-only reviewer or diagnoser subagent, wait for the expected
result artifact, and then resume `review-apply` or `auto-loop`. Ask the user
only if no suitable subagent/tool is available, or if an external result is
needed outside the local runtime.

`math_review_gate_required` likewise means there is no ordinary author action.
Write or refresh the natural language proof skeleton, dispatch an independent
read-only math reviewer for the three required rounds, and resume author/build
only if the verdict is `go`.

## 8. Batch Planning

For a group of tasks, first ask the runtime for a read-only scheduling view:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id>
```

`batch-plan` reads the ledger and existing Phase2 metadata, then tells the
operator which tasks need fresh existing review, which should enter `auto-loop`,
which need Math Review Gate evidence, and which are blocked by upstream tasks.
It is a scheduler/report only. It does not execute repair and cannot land
completion.

By default, `batch-plan` omits legacy/audit rows from the ordinary
author/review queue. Current ledgers should not retain `obl_*` child tasks, but
the scheduler remains able to quarantine them when reading old fixtures or
imported legacy state:

- `obl_*` and nested `obl_obl_*` task ids;
- historical obligation children after the parent has already landed
  `phase2_status=pass` or the obligation has been absorbed into parent/support
  proof work;
- diagnostic `restore_or_rebuild_output` rows when a draft or build/review
  candidate already exists.

The rendered plan keeps a one-line `hidden legacy/audit items` summary so the
operator can see that rows were quarantined without spending queue space on
them. Use `--batch-include-legacy` only for explicit audit/legacy inspection.
Parent pass does not make old child obligations active work again; they remain
audit/quarantine evidence unless a parent-facing task reopens them through the
normal build/review/apply loop.

When `batch-plan` is run with `--batch-limit`/`--batch-workers`, its visible
table is an executable worker queue. It filters out `reviewer_required` and
`diagnoser_required`, and `math_review_gate_required` rows. An empty table
therefore means there are no ordinary author actions; it does not mean the goal
is blocked for user input. Inspect the underlying task states and dispatch
reviewer/diagnoser/math-review subagents as needed.

For a larger repair push, ask for a worker queue instead of manually picking
tasks:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode batch-plan --tasks <task_id>,<task_id> --batch-task-kinds theorem,definition --batch-limit 15 --batch-workers 5
```

This keeps Problem tasks out of the first queue, ranks candidates by downstream
fanout after dependency analysis, and prints worker slots plus conflict groups.
The default queue should be parent-facing failed/blocked tasks first; legacy
child obligations are not worker assignments unless `--batch-include-legacy` is
explicitly requested.
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
- foundational support: maintenance planning for splitting super-long official
  output and absorbing proof-obligation material into stable support or parent
  files. It may include already passing official outputs when their size or
  historical `obl_*` declarations create a reuse problem, but it does not land
  completion by itself.
- `soft-pack` and `soft-apply`: Problem soft-dependency selection only; not a
  Lean acceptance gate.

## Stops

Stop as clean only on `phase2_status=pass` through `review-apply`. Otherwise
report `fail`, `blocked`, or the explicit allowed exception and continue repair
or dependency handling.
