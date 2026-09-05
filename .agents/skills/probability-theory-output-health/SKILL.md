---
name: probability-theory-output-health
description: "Use when auditing, planning, or refactoring Formalization Engine Phase 2 output health: large ProbabilityTheory files, shared or foundational support extraction, parent/support boundary cleanup, downstream import checks, semantic review/apply, or scan-to-commit maintenance work."
---

# Probability Theory Output Health

## Purpose

Use this skill to improve `ProbabilityTheory` structure without changing source-facing mathematics. It specializes the Phase 2 workflow for output-health work: scan first, classify ownership, extract only real shared support, verify Lean, run independent semantic review, apply review state, and commit without pushing.

This skill does not replace `.agents/skills/formalization-engine-phase2-entrypoint/SKILL.md`. Before output-health work, use that entrypoint and obey `AGENTS.md`, `CONTEXT.md`, and `docs/phase2/*`.

## Required Start

Before editing or recommending a refactor:

1. Run or read the Phase 2 entrypoint checklist.
2. Record `git status --short`.
3. Inspect relevant Lean files, imports, prompt-pack review artifacts, and downstream consumers.
4. If a parent statement, theorem statement, source wording, or source-statement risk may change, inspect the local textbook/input source before deciding.

Do not treat file size alone as a refactor reason.

## Ownership Classes

Use the project language from `CONTEXT.md`:

- `Task Parent`: source-facing module for one task. Keep task text, final theorem names, and final statement shape stable.
- `Proof-Layer Support`: task-owned proof machinery. It may stay large if it has one coherent responsibility and no real second consumer.
- `Interface Support`: stable bridge between textbook definitions, ProbabilityTheoryFormalization conventions, and Mathlib APIs.
- `Shared Support`: reusable support for more than one task family or a recurring textbook interface.
- `Source-Statement Risk`: textbook/current-definition mismatch requiring a decision, not ordinary proof cleanup.

Extract only when evidence shows shared support, interface support, obvious duplication, high fan-in/downstream pressure, or a stable textbook API boundary.

## Investigation Workflow

For a candidate chapter, family, or file set, gather:

- size summary
- import summary
- declaration summary
- downstream import scan
- forbidden scan
- review freshness and official-output/candidate hash alignment
- source inspection when parent statements or source-statement risk are involved

Produce a decision table before editing:

```text
candidate | owner classification | downstream imports | risk | recommended action | next implementation target
```

If the table shows task-owned proof support and no real reuse, recommend no split.

## Command Templates

Use PowerShell from repo root.

Size scan:

```powershell
Get-ChildItem ProbabilityTheory -Recurse -Filter *.lean |
  Sort-Object Length -Descending |
  Select-Object -First 25 Name,@{Name='KB';Expression={[math]::Round($_.Length/1KB,1)}}
```

Chapter/family exact scan:

```powershell
Get-ChildItem ProbabilityTheory -Recurse -Filter *.lean |
  Where-Object { $_.Name -match '^(def|thm|prob|ex)_14_|^chapter14_' } |
  Sort-Object Length -Descending |
  Select-Object Name,@{Name='KB';Expression={[math]::Round($_.Length/1KB,1)}}
```

Exact family warning: for `prob_14_1`, scan `prob_14_1.lean` plus `prob_14_1_*.lean`; do not use `prob_14_1*.lean`, which also catches `prob_14_10`, `prob_14_11`, and `prob_14_12`.

Import and downstream scan:

```powershell
rg -n "^import ProbabilityTheory\." <manifest-resolved-file>.lean
rg -n "import ProbabilityTheory\.<module_name>\b" ProbabilityTheory
```

Declaration scan:

```powershell
rg -n "^\s*(theorem|lemma|def|structure|class|abbrev)\s+" <manifest-resolved-file>.lean
```

Forbidden scan for selected files:

```powershell
rg -n "\b(sorry|admit|unsafe)\b|^\s*(private\s+)?axiom\b|^\s*import\s+ProbabilityTheory\..*\.obl_|^\s*(theorem|lemma|def)\s+obl_" <selected files>
```

Build checks:

```powershell
lake env lean <manifest-resolved-ProbabilityTheory-file>.lean
python -m unittest tests.test_phase2_health_improvements
```

Semantic review and apply:

```powershell
formalize --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject existing
```

Use an independent read-only reviewer subagent or configured reviewer runner to write the expected `semantic_review_result_vN.json`.

```powershell
formalize --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result $env:FORMALIZATION_ENGINE_ARTIFACT_ROOT\phase2_prompt_packs\<task_id>\semantic_review_result_vN.json
```

Commit:

```powershell
git add -f <ProbabilityTheory files> <review artifacts>
git diff --cached --check
git commit -m "<message>"
```

Do not push unless the user explicitly asks.

## Refactor Rules

- Preserve public theorem, lemma, def, and structure names unless the user explicitly requests a breaking rename.
- Preserve parent theorem statements and source-facing task declarations.
- Keep compatibility wrapper modules or aliases when downstream imports rely on old module names.
- Do not move task-specific proof spines into generic modules.
- Do not create a shared support module just to shorten one file.
- Do not hand-edit `project_ledger.json`, `phase2_status`, or review result verdicts.
- Do not run `review-apply` unless the review result is for the current official output or intended candidate and hashes/freshness are valid.
- If a refactor fails Lean or semantic review, revert only that family refactor; keep earlier completed families intact.
- Treat generated build caches as disposable, but protect prompt packs, ledger state, review artifacts, and ignored Output files from accidental deletion.

## Known Exceptions

These are not ordinary output-health targets unless the user explicitly scopes exception/status work:

- `thm_14_8`: documented beyond-book exception.
- `thm_11_8`: documented cited-external-proof exception.
- `thm_1_2`: Chapter 1 source-statement risk around interval concatenation.
- `ex_1_3_2`: source typo/statement-decision risk.

Always re-check current docs, source, prompt packs, and review artifacts before relying on this list.

## Review Discipline

For every modified task official output:

1. Run Lean on touched support and parent modules.
2. Run the health unittest.
3. Run the selected-file forbidden scan.
4. Run `review-now --review-subject existing`.
5. Delegate semantic review to an independent read-only subagent or configured reviewer.
6. Apply only passing current review results with `review-apply`.
7. Commit all Lean changes and review/apply artifacts together.

If only a read-only scan is requested, do not edit Lean, prompt packs, ledger, or `phase2_status`.
