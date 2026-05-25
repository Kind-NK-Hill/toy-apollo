# Phase2 Completion Classification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` if the user explicitly authorizes subagents for this run; otherwise use `superpowers:executing-plans` and execute task-by-task with checkpoints. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Create an independent, evidence-backed Phase2 completion classification layer so the project no longer treats "Lean builds" or "audit is clean" as equivalent to "textbook proof completed."

**Architecture:** Keep `project_ledger.json` as execution/status bookkeeping only. Create standalone classification artifacts under `docs/` and, if code is added, make the code validate/render classification evidence rather than infer mathematical truth from strings. Every classification entry must cite Lean declarations, line evidence, validation commands, and the reason for its proof-route class.

**Tech Stack:** Python stdlib, Markdown, JSON, Lean 4/Lake, existing ToyApollo output files and Phase2 prompt-pack metadata.

---

## Non-Negotiable Principles

- Do not edit `project_ledger.json`.
- Do not claim a task is `textbook_proof_completed` merely because its Lean file builds.
- Do not claim a task is `textbook_proof_completed` when the main proof route is a private axiom, public proof package, or direct specialization of a stronger Mathlib theorem.
- Do not use audit string matching as final evidence. Audit can identify candidates, but each classification must cite local Lean declarations and metadata lines.
- Do not erase or hide `open_math_debt`. If public debt was moved to a private axiom, classify it as `open_math_debt` with flag `private_axiom_internalized`.
- Do not classify inherited use of `thm_14_8_ProofBeyondBook` as ordinary proved debt. It must be `beyond_book_exception` on `thm_14_8` and `inherited_beyond_book_exception` on downstream tasks.
- Do not force every task into a single flat label without nuance. Each task has exactly one `primary_class`, but may have multiple `flags`.
- Do not update task metadata to `proved` unless the landing is a real theorem/lemma and the proof route classification is honest.

## Required First Reads

Read these docs before implementation:

- `docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md`
- `docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md`
- `docs/modification_0525_steps/phase2_ch14_worker_d_classification.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.json`

Read these representative Lean files before classifying:

- `ToyApollo/Output/prob_10_5.lean`
- `ToyApollo/Output/prob_10_6.lean`
- `ToyApollo/Output/prob_11_6.lean`
- `ToyApollo/Output/prob_11_8.lean`
- `ToyApollo/Output/prob_11_9.lean`
- `ToyApollo/Output/prob_11_10.lean`
- `ToyApollo/Output/thm_11_7.lean`
- `ToyApollo/Output/thm_13_14.lean`
- `ToyApollo/Output/thm_14_5.lean`
- `ToyApollo/Output/thm_14_6.lean`
- `ToyApollo/Output/thm_14_8.lean`
- `ToyApollo/Output/ex_14_4_3.lean`

Read these metadata files for proof-route claims:

- `phase2_prompt_packs/prob_10_5/proof_obligations.json`
- `phase2_prompt_packs/prob_10_6/proof_obligations.json`
- `phase2_prompt_packs/prob_11_6/proof_obligations.json`
- `phase2_prompt_packs/prob_11_8/proof_obligations.json`
- `phase2_prompt_packs/prob_11_9/proof_obligations.json`
- `phase2_prompt_packs/prob_11_10/proof_obligations.json`
- `phase2_prompt_packs/thm_11_7/proof_obligations.json`
- `phase2_prompt_packs/thm_13_14/proof_obligations.json`
- `phase2_prompt_packs/thm_14_5/proof_obligations.json`
- `phase2_prompt_packs/thm_14_6/proof_obligations.json`
- `phase2_prompt_packs/thm_14_8/proof_obligations.json`
- `phase2_prompt_packs/ex_14_4_3/proof_obligations.json`

## Output Files

Create these files:

- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`

Optional but recommended if implementation code is useful:

- `tools/validate_phase2_completion_classification.py`
- `tests/test_phase2_completion_classification.py`

The JSON should be the source of truth. The Markdown should be human-readable and generated from, or manually kept in lockstep with, the JSON.

## Classification Vocabulary

Each task must have exactly one `primary_class` from this closed set:

- `textbook_proof_completed`
- `mathlib_backed_adapter_completed`
- `interface_bridge_completed`
- `open_math_debt`
- `beyond_book_exception`
- `needs_decision`

Each task may also have zero or more `flags`:

- `public_interface_clean`
- `public_interface_leak`
- `private_axiom_internalized`
- `inherited_beyond_book_exception`
- `source_route_open`
- `metadata_only_cleanliness_risk`
- `mathlib_switch_without_textbook_route`
- `interface_bridge_present`
- `support_constructor_return_only`
- `setup_parameter_review_needed`
- `ledger_unchanged`

Use flags to record mixed reality. For example:

- `ex_14_4_3`: `primary_class = open_math_debt`, flags include `inherited_beyond_book_exception`, `private_axiom_internalized`, `public_interface_clean`.
- `thm_14_6`: `primary_class = mathlib_backed_adapter_completed`, flags include `interface_bridge_present`, `public_interface_clean`.
- `thm_14_8`: `primary_class = beyond_book_exception`, flags include `public_interface_clean` only if no other public proof package is exposed.

## JSON Schema

Use this shape exactly:

```json
{
  "schema_version": 1,
  "created": "2026-05-24",
  "scope": "ToyApollo Phase2 completion classification; ledger-independent",
  "allowed_primary_classes": [
    "textbook_proof_completed",
    "mathlib_backed_adapter_completed",
    "interface_bridge_completed",
    "open_math_debt",
    "beyond_book_exception",
    "needs_decision"
  ],
  "allowed_flags": [
    "public_interface_clean",
    "public_interface_leak",
    "private_axiom_internalized",
    "inherited_beyond_book_exception",
    "source_route_open",
    "metadata_only_cleanliness_risk",
    "mathlib_switch_without_textbook_route",
    "interface_bridge_present",
    "support_constructor_return_only",
    "setup_parameter_review_needed",
    "ledger_unchanged"
  ],
  "tasks": [
    {
      "task_id": "prob_11_10",
      "chapter": 11,
      "lean_file": "ToyApollo/Output/prob_11_10.lean",
      "declarations": [
        "prob_11_10",
        "prob_11_10_continuous_grid_uniformization_internal"
      ],
      "primary_class": "open_math_debt",
      "flags": [
        "public_interface_clean",
        "private_axiom_internalized",
        "ledger_unchanged"
      ],
      "evidence": [
        {
          "file": "ToyApollo/Output/prob_11_10.lean",
          "line": 64,
          "kind": "private_axiom",
          "text": "private axiom prob_11_10_continuous_grid_uniformization_internal"
        },
        {
          "file": "phase2_prompt_packs/prob_11_10/proof_obligations.json",
          "line": 7,
          "kind": "metadata_note",
          "text": "public theorem no longer exposes hUniform, but uniformization remains private axiom debt"
        }
      ],
      "validation": [
        "lake env lean ToyApollo/Output/prob_11_10.lean",
        "python tools/audit_phase2_clean_debt_surface.py --fail-on-errors"
      ],
      "classification_reason": "The public proof package was removed, but the finite-grid uniformization theorem is still supplied by a private axiom.",
      "next_action": "Replace the private axiom with theorem-level finite-grid uniformization evidence."
    }
  ]
}
```

Required entry fields:

- `task_id`
- `chapter`
- `lean_file`
- `declarations`
- `primary_class`
- `flags`
- `evidence`
- `validation`
- `classification_reason`
- `next_action`

Required evidence fields:

- `file`
- `line`
- `kind`
- `text`

Allowed `evidence.kind` values:

- `theorem`
- `def`
- `structure`
- `private_axiom`
- `public_parameter`
- `mathlib_adapter`
- `interface_bridge`
- `metadata_note`
- `audit_signal`
- `validation_command`

## Markdown Format

The Markdown file must have this structure:

```markdown
# Phase2 Completion Classification

Created: 2026-05-24
Status: ledger-independent classification

## Purpose

This document separates mathematical completion fidelity from execution ledger status.

## Class Definitions

...

## Summary

| primary_class | count |
| --- | ---: |
| textbook_proof_completed | N |
| mathlib_backed_adapter_completed | N |
| interface_bridge_completed | N |
| open_math_debt | N |
| beyond_book_exception | N |
| needs_decision | N |

## Task Classifications

| task | primary class | flags | evidence | next action |
| --- | --- | --- | --- | --- |
| `prob_11_10` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `ToyApollo/Output/prob_11_10.lean:64` private axiom | Replace private axiom with theorem-level uniformization proof. |

## Validation

List commands actually run.

## Ledger Boundary

`project_ledger.json` was not edited by this classification pass.
```

## Seed Classifications From Current Local Evidence

Use these as the first batch. Verify line numbers locally before writing final JSON/MD because the working tree is actively changing.

| task | primary class | required flags | local evidence to verify |
| --- | --- | --- | --- |
| `prob_10_5` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `ToyApollo/Output/prob_10_5.lean` has private axiom `prob_10_5_dominated_probability_to_mean_internal`; public `h_dominated_bridge` is gone. |
| `prob_10_6` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `ToyApollo/Output/prob_10_6.lean` has private axiom `prob_10_6_singleton_masses_to_distribution_internal`; public `h_countable_bridge` is gone. |
| `prob_11_6` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `prob_11_6_sixthMomentSupport_internal` remains private axiom debt; tail summability has theorem-level internal route. |
| `prob_11_8` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `prob_11_8_covarianceDecaySupport_internal` remains private axiom debt. |
| `prob_11_9` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `prob_11_9_occupancy_moment_calculation_internal` remains private axiom debt. |
| `prob_11_10` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `prob_11_10_continuous_grid_uniformization_internal` remains private axiom debt. |
| `thm_11_7` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `thm_11_7_tail_summability_internal` remains private axiom debt; `_hfourth` is a source assumption, not proof package debt. |
| `thm_13_14` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized` | `thm_13_14_conditional_expectation_internal` remains private axiom debt; public `hIntervals`/`hExtend` are gone. |
| `thm_14_5` | `mathlib_backed_adapter_completed` | `source_route_open`, `metadata_only_cleanliness_risk`, `interface_bridge_present` | Public theorem uses Mathlib `isTightMeasureSet_of_tendsto_charFun` plus `def_14_3_of_mathlibTight`; source route remains open. |
| `thm_14_6` | `mathlib_backed_adapter_completed` | `interface_bridge_present`, `public_interface_clean` | Main theorem uses Mathlib compactness/tightness route; interval bridge is theorem-level. |
| `thm_14_8` | `beyond_book_exception` | `ledger_unchanged` | `thm_14_8_ProofBeyondBook` is the only allowed beyond-book package. |
| `ex_14_4_3` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `inherited_beyond_book_exception` | `hLyapunov` is removed; `ex_14_4_3_lyapunov_condition_internal` remains private axiom debt; inherited `thm_14_8_ProofBeyondBook` remains. |

If the worker expands the scope, add all post-Chapter-9 tasks and any Chapter 1-8 comparison tasks needed to define the target standard. Do not silently omit a task if it appears in the audit report, prompt-pack metadata, or evidence docs.

## Task 1: Create JSON Source Of Truth

**Files:**

- Create: `docs/phase2_completion_classification.json`

**Steps:**

- [ ] Read required first-read files.
- [ ] Start the JSON with the schema shown above.
- [ ] Add the seed classifications from this plan.
- [ ] For every entry, verify the cited line numbers with local search before writing them.
- [ ] For every `open_math_debt` entry, include the exact private axiom or public proof package declaration causing that classification.
- [ ] For every `mathlib_backed_adapter_completed` entry, include the exact Mathlib theorem or bridge declaration used by the proof route.
- [ ] For every `beyond_book_exception`, verify that the declaration is exactly `thm_14_8_ProofBeyondBook`.

**Validation:**

```powershell
python -m json.tool docs/phase2_completion_classification.json > $null
```

Expected: exits successfully.

## Task 2: Create Human-Readable Markdown

**Files:**

- Create: `docs/phase2_completion_classification.md`

**Steps:**

- [ ] Use the Markdown structure from this plan.
- [ ] Include a clear statement that the file is ledger-independent.
- [ ] Include the class definitions.
- [ ] Include summary counts matching the JSON.
- [ ] Include a task table with `task`, `primary class`, `flags`, `evidence`, and `next action`.
- [ ] Include a validation section listing commands actually run.
- [ ] Include a ledger boundary section saying `project_ledger.json` was not edited.

**Validation:**

```powershell
rg -n "project_ledger|open_math_debt|mathlib_backed_adapter_completed|thm_14_8_ProofBeyondBook" docs/phase2_completion_classification.md
```

Expected: the document explicitly mentions ledger boundary, open debt, Mathlib-backed adapter status, and the unique beyond-book exception.

## Task 3: Add Optional Validator

Only do this if the user wants code, or if the JSON grows large enough that manual consistency checks are risky.

**Files:**

- Create: `tools/validate_phase2_completion_classification.py`
- Create: `tests/test_phase2_completion_classification.py`

**Validator behavior:**

- Load `docs/phase2_completion_classification.json`.
- Check required top-level keys.
- Check each task has all required fields.
- Check `primary_class` is in the allowed set.
- Check all `flags` are in the allowed set.
- Check every evidence item has `file`, `line`, `kind`, `text`.
- Check every evidence file exists.
- Check line numbers are positive integers.
- Check `thm_14_8_ProofBeyondBook` is the only task with `primary_class = beyond_book_exception`.
- Check tasks with `private_axiom_internalized` have at least one evidence item with `kind = private_axiom`.
- Check tasks with `mathlib_backed_adapter_completed` have at least one evidence item with `kind = mathlib_adapter` or `interface_bridge`.

**Validation commands:**

```powershell
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
```

Expected: both pass.

## Task 4: Cross-Check Against Current Lean And Audit

**Files:**

- Read-only: `ToyApollo/Output/*.lean`
- Read-only: `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- Read-only: `docs/phase2_ch10_14_clean_debt_surface_audit.json`

**Steps:**

- [ ] Run the audit:

```powershell
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

- [ ] Confirm the classification does not claim that audit success means textbook proof completion.
- [ ] For each `public_setup_parameter_review` task kept outside the first classification batch, either add a row or document why it is out of scope.
- [ ] For each `allowed_beyond_book_surface` or `inherited_beyond_book_surface`, verify the task has the correct `beyond_book_exception` or `inherited_beyond_book_exception` flag.

**Validation:** The final Markdown and JSON explain the distinction between audit cleanliness and completion classification.

## Task 5: Final Report

The implementing worker must report:

- Files created or modified.
- Whether `project_ledger.json` remained untouched.
- Count of tasks by `primary_class`.
- List of tasks still marked `open_math_debt`.
- List of tasks marked `mathlib_backed_adapter_completed`.
- Confirmation that `thm_14_8_ProofBeyondBook` is the only `beyond_book_exception`.
- Commands run and whether they passed.

## Recommended Commit Boundary

Commit Step 2 separately from Lean proof cleanup:

```powershell
git add docs/modification_0525_steps/phase2_completion_classification_step2_implementation_plan.md docs/phase2_completion_classification.md docs/phase2_completion_classification.json
git commit -m "docs: add phase2 completion classification"
```

If validator code is added:

```powershell
git add tools/validate_phase2_completion_classification.py tests/test_phase2_completion_classification.py
git commit -m "test: validate phase2 completion classification"
```

Do not mix this with Lean theorem edits.
