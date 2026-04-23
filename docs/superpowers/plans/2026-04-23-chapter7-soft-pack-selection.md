# Chapter 7 Soft-Pack Selection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generate a chapter 7 `phase3` soft-pack, derive a first-pass executable chapter-local `selection.json`, and record any cross-chapter candidates in a separate advisory note.

**Architecture:** Use the existing `phase3` operator workflow without changing runtime code. First generate the pack, then derive selections from the generated pack plus the raw chapter 7 problem statements, and finally verify that every selected id is accepted by the current `allowed_material_ids.json` contract.

**Tech Stack:** PowerShell, Python CLI, JSON, Markdown, existing `toy-apollo` phase3 workflow

---

### Task 1: Generate the Chapter 7 Soft-Pack

**Files:**
- Create: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\*`
- Modify: none
- Test: command output and generated pack files

- [ ] **Step 1: Run chapter 7 soft-pack**

```powershell
cd D:\Grad_Study\Practimum\Formalization\toy-apollo
python .\run_chapter.py --phase 3 --phase3-mode soft-pack --tasks prob_7_1,prob_7_2,prob_7_3,prob_7_4,prob_7_5,prob_7_6,prob_7_7,prob_7_8,prob_7_9
```

- [ ] **Step 2: Verify the pack directory was created**

Run:

```powershell
Get-ChildItem .\phase3_softdep_packs | Sort-Object LastWriteTime -Descending | Select-Object -First 1 Name,FullName,LastWriteTime
```

Expected: a newest batch directory for chapter 7 exists.

- [ ] **Step 3: Verify required pack files exist**

Run:

```powershell
$pack = (Get-ChildItem .\phase3_softdep_packs | Sort-Object LastWriteTime -Descending | Select-Object -First 1).FullName
Get-ChildItem $pack | Select-Object Name
```

Expected files:

- `batch.json`
- `operator_prompt.md`
- `problem_statements.md`
- `selection_hints.md`
- `chapter_materials.md`
- `allowed_material_ids.json`
- `selection_schema.json`
- `soft_imports_selection.json`
- `apply_report.md`

### Task 2: Inspect Allowed Materials and Problem Statements

**Files:**
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\problem_statements.md`
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\chapter_materials.md`
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\allowed_material_ids.json`
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\inputs\30_chap7_problems.tex`
- Test: selection coverage against current CLI rules

- [ ] **Step 1: Read generated pack materials**

Run:

```powershell
$pack = (Get-ChildItem .\phase3_softdep_packs | Sort-Object LastWriteTime -Descending | Select-Object -First 1).FullName
Get-Content (Join-Path $pack 'problem_statements.md') -TotalCount 220
Get-Content (Join-Path $pack 'chapter_materials.md') -TotalCount 260
Get-Content (Join-Path $pack 'allowed_material_ids.json')
```

Expected: chapter 7 problem statements and chapter-local material ids are visible.

- [ ] **Step 2: Cross-check against raw chapter 7 input**

Run:

```powershell
Get-Content .\inputs\30_chap7_problems.tex -TotalCount 220
```

Expected: raw problem text matches the pack interpretation.

- [ ] **Step 3: Freeze the allowed-id contract**

Rule to enforce:

```text
Every value placed into selection.json must be present in allowed_material_ids.json.
Cross-chapter candidates may be recorded only in a separate markdown note.
```

### Task 3: Draft the Executable Selection JSON

**Files:**
- Create: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\selection_first_pass.json`
- Test: JSON parse and allowed-id validation

- [ ] **Step 1: Draft the first-pass selection payload**

Initial payload shape:

```json
{
  "prob_7_1": [],
  "prob_7_2": [],
  "prob_7_3": [],
  "prob_7_4": [],
  "prob_7_5": [],
  "prob_7_6": [],
  "prob_7_7": [],
  "prob_7_8": [],
  "prob_7_9": []
}
```

Populate it using the balanced strategy from the approved design.

- [ ] **Step 2: Save the draft into the newest pack directory**

Write to:

```text
D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\selection_first_pass.json
```

- [ ] **Step 3: Verify JSON parses**

Run:

```powershell
$pack = (Get-ChildItem .\phase3_softdep_packs | Sort-Object LastWriteTime -Descending | Select-Object -First 1).FullName
Get-Content (Join-Path $pack 'selection_first_pass.json') | python -c "import sys, json; json.load(sys.stdin); print('OK')"
```

Expected: `OK`

- [ ] **Step 4: Verify every selected id is allowed**

Run:

```powershell
$pack = (Get-ChildItem .\phase3_softdep_packs | Sort-Object LastWriteTime -Descending | Select-Object -First 1).FullName
@'
import json
from pathlib import Path
pack = Path(r"REPLACE_PACK")
allowed = set(json.loads((pack / "allowed_material_ids.json").read_text(encoding="utf-8")))
payload = json.loads((pack / "selection_first_pass.json").read_text(encoding="utf-8"))
bad = {k: [x for x in v if x not in allowed] for k, v in payload.items()}
bad = {k: v for k, v in bad.items() if v}
print("OK" if not bad else bad)
'@.Replace('REPLACE_PACK', $pack) | python -
```

Expected: `OK`

### Task 4: Record Cross-Chapter Advisory Candidates

**Files:**
- Create: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\cross_chapter_candidates.md`
- Test: manual semantic review only

- [ ] **Step 1: Identify chapter 7 problems that may depend semantically on earlier chapters**

Record only cases where chapter-local support appears insufficient from the statement alone.

- [ ] **Step 2: Write the advisory note**

Required structure:

```markdown
# Cross-Chapter Candidates

- `prob_7_x`: possible external support -> `...`
  reason: `...`
  action: advisory only, not included in selection_first_pass.json under current CLI contract
```

- [ ] **Step 3: Verify the advisory note does not change executable inputs**

Check:

```text
cross_chapter_candidates.md is informational only and is not passed to soft-apply.
```

### Task 5: Report the Results Without Applying

**Files:**
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\selection_first_pass.json`
- Read: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase3_softdep_packs\<batch_id>\cross_chapter_candidates.md`
- Test: confirm ledger unchanged

- [ ] **Step 1: Confirm ledger was not modified**

Run:

```powershell
python .\run_chapter.py --status
```

Expected: no `soft-apply` side effects were introduced by this workflow.

- [ ] **Step 2: Present the outputs**

Report:

- pack directory path
- executable `selection_first_pass.json`
- advisory `cross_chapter_candidates.md`
- any open questions before `soft-apply`
