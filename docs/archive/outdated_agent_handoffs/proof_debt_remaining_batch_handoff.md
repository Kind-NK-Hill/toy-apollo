# Proof Debt Remaining Batch Handoff

Date: 2026-05-20.

This note supersedes the old "remaining proof debt" snapshot for the current
worktree. Batches 1 through 6 have been run through the normal Phase2 loop.

## Current State

The current ledger no longer has parent tasks whose
`proof_obligation_summary.status_counts.accepted_as_proof_debt` is nonzero.

The current `run_chapter.py --status` summary after Batch 4/5/6 was:

```text
DISCOVERED: 49
COMPLETED: 262
COMPLETED_WITH_PROOF_DEBT: 1
```

The lone `COMPLETED_WITH_PROOF_DEBT` entry observed at handoff time is:

- `obl_prob_11_6_tail_summability_support`

Its proof-obligation summary is already `{"proved": 1}`. Treat this as a
child-status normalization issue, not as a remaining parent mathematical proof
debt, unless a fresh audit proves otherwise.

Two open Chapter 14 child tasks may still appear:

- `obl_thm_14_4_triangle_density_bound`
- `obl_thm_14_4_adapted_theorem_8_6_identity`

The parent `thm_14_4` is currently `COMPLETED`, with its parent proof
obligations recorded as proved/obsolete. Treat these two child tasks as ledger
hygiene or obsolete-child cleanup, not as active mathematical proof debt, unless
the parent regresses.

## Remaining Batch Definition

The next batch should be a small cleanup batch, not another Chapter 14 repair
batch:

1. Reconfirm no parent task has `accepted_as_proof_debt`.
2. Normalize `obl_prob_11_6_tail_summability_support` if it still reports
   `COMPLETED_WITH_PROOF_DEBT` despite `proved: 1`.
3. Decide whether the two `thm_14_4` obsolete children should be marked closed,
   superseded, or left as historical discovered tasks according to the ledger
   mechanism.
4. Run targeted verification after any ledger mutation.

Do not invent new proof-debt children simply because those historical child
tasks are open. First inspect the parent task and current
`phase2_prompt_packs/<parent>/proof_obligations.json`.

## Audit Commands

Use these before touching anything:

```powershell
python .\run_chapter.py --status

python - <<'PY'
import json
from pathlib import Path
ledger = json.loads(Path("project_ledger.json").read_text())
for tid, task in sorted(ledger["tasks"].items()):
    summary = task.get("proof_obligation_summary") or {}
    counts = summary.get("status_counts") or {}
    debt = counts.get("accepted_as_proof_debt", 0)
    if debt or task.get("status") == "COMPLETED_WITH_PROOF_DEBT":
        print(tid, task.get("status"), counts)
PY

python - <<'PY'
import json
from pathlib import Path
ledger = json.loads(Path("project_ledger.json").read_text())
for tid, task in sorted(ledger["tasks"].items()):
    if task.get("type") == "Phase2ObligationTask" and task.get("obligation_task_state") != "closed":
        print(tid, task.get("status"), task.get("obligation_task_state"))
PY
```

On Windows PowerShell, if heredocs are awkward, put the Python snippets in a
temporary file and run them.

## Running Discipline

Use these rules for any remaining or newly discovered proof-debt work:

- Never apply a semantic review result after a sibling child has just promoted
  the same parent. Run a fresh `review-now`, write a fresh result, then apply
  immediately.
- The `obligation_review.items[*].obligation_id` must be the original parent
  obligation id, such as `obligation_3` or
  `theorem_14_3_characteristic_limit`, not the full child task id.
- If the review context lists direct downstream consumers, `downstream_adequacy`
  must contain one `consumers_checked` entry per consumer.
- If `pack` says a hard dependency carries accepted proof debt, stop and clear
  the blocker first. Do not bypass the dependency by editing stale packs.
- `ToyApollo/Output` may be ignored by Git. Always verify by reading files and
  running Lean, not by relying on `git status`.
- Treat green Lean as necessary but not sufficient. A claim is complete only
  after build-check, fresh semantic review, review-apply, parent reconciliation,
  and targeted Lean verification.

## Tao-Style Formalization Policy

For future work, keep the user-approved Tao-style discipline:

1. When a new concept is introduced, first formalize the textbook definition
   and the first few textbook properties.
2. Then prove a bridge theorem showing equivalence with, or a special case of,
   a Mathlib or existing ToyApollo interface.
3. Only after the bridge is present should downstream code use the Mathlib or
   existing ToyApollo interface directly.

This avoids both extremes: hand-rolling everything forever, and replacing the
textbook proof spine with a black-box theorem.

## Verification Before Declaring The Cleanup Done

Before reporting the remaining batch complete, verify:

1. No parent task has `accepted_as_proof_debt`.
2. No active child obligation that corresponds to a live parent debt is open.
3. Any open historical child is explained as obsolete/superseded or left with a
   documented reason.
4. The affected parent output files pass `lake env lean`.
5. The Phase2 obligation-task tests still pass:

```powershell
python -m pytest tests/test_phase2_obligation_tasks.py `
  tests/test_phase2_pack_generation.py::Phase2PackGenerationTests::test_codex_review_pack_reflects_pack_soft_imports -q
```

At the time this handoff was written, those tests passed with `12 passed`.
