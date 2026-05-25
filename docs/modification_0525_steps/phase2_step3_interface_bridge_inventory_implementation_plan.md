# Phase2 Step 3 Interface Bridge Inventory Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` if the user explicitly authorizes subagents for this run; otherwise use `superpowers:executing-plans` and execute task-by-task with checkpoints. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a concept-level reuse and bridge inventory that answers whether post-Chapter-9 tasks actually reuse Chapter 1-8 outputs, merely import/name them, or re-assume the same mathematics through private axioms, support packages, setup fields, or adapters.

**Architecture:** Step 3 is an investigation/inventory pass, not a Lean proof pass. First freeze and validate the current Step 1/2/2.5 baseline; then inspect concept families; then write a ledger-independent inventory under `docs/`. Subagents, if used, should investigate disjoint concept families and return evidence; the main agent owns the final document to avoid conflicting edits.

**Tech Stack:** Local Lean files under `ToyApollo/Output`, Phase2 prompt-pack metadata, existing Step 2 classification JSON/Markdown, ripgrep, optional Python stdlib audit helper.

---

## Why Step 3 Exists

Step 2.5 showed that Tier A tasks were not simply "almost done":

- `prob_10_5` needs a DCT / convergence-in-probability / uniform-integrability bridge decision.
- `prob_10_6` needs a countable distribution / singleton-mass / TV bridge decision.
- `prob_11_6` needs a moment / integrability / independence interface decision.
- `prob_11_9` needs a Chapter 6 occupancy / balls-in-boxes model reuse decision.

Therefore Step 3 must not be a generic concept catalog. It must explain, with file-level evidence, why these tasks could not be closed by direct reuse of earlier Chapter 1-8 material.

## Non-Negotiable Rules

- Do not modify Lean files in Step 3.
- Do not edit `project_ledger.json`.
- Do not change `proof_obligations.json` unless the user explicitly expands Step 3 into metadata maintenance.
- Do not treat an import as theorem reuse.
- Do not treat a bridge file name as evidence that a bridge theorem exists.
- Do not treat Mathlib-backed adapter status as failure. Record it honestly.
- Do not hide Tier A outcomes. `prob_10_5`, `prob_10_6`, `prob_11_6`, and `prob_11_9` are mandatory case studies.
- Do not check GitHub or remote commits unless the user explicitly asks. This plan is local-repository only.

## Required Pre-Step3 Work

Before doing inventory, the implementing agent must complete this preflight.

### Preflight Goal 1: Confirm Baseline Files Exist

Required files:

- `docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md`
- `docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md`
- `docs/modification_0525_steps/phase2_completion_classification_step2_implementation_plan.md`
- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`
- `docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md`
- `tools/validate_phase2_completion_classification.py`
- `tests/test_phase2_completion_classification.py`

Run:

```powershell
Test-Path docs/phase2_completion_classification.json
Test-Path docs/phase2_completion_classification.md
Test-Path docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md
```

Expected: all return `True`.

### Preflight Goal 2: Validate Current Baseline

Run:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

Expected:

- classification JSON parses;
- classification validator passes;
- classification tests pass;
- audit reports `error_task_count: 0`;
- `project_ledger.json` is not modified.

### Preflight Goal 3: Create A Checkpoint

If the user authorizes commits, commit the current Step 1/2/2.5 state before Step 3:

```powershell
git add ToyApollo/Output/ex_14_4_3.lean ToyApollo/Output/prob_11_10.lean ToyApollo/Output/prob_11_6.lean ToyApollo/Output/prob_11_8.lean ToyApollo/Output/prob_11_9.lean ToyApollo/Output/thm_11_7.lean ToyApollo/Output/thm_13_14.lean
git add docs/phase2_ch10_14_clean_debt_surface_audit.json docs/phase2_ch10_14_clean_debt_surface_audit.md
git add phase2_prompt_packs/ex_14_4_3/proof_obligations.json phase2_prompt_packs/prob_11_10/proof_obligations.json phase2_prompt_packs/prob_11_6/proof_obligations.json phase2_prompt_packs/prob_11_8/proof_obligations.json phase2_prompt_packs/prob_11_9/proof_obligations.json phase2_prompt_packs/thm_11_7/proof_obligations.json phase2_prompt_packs/thm_13_14/proof_obligations.json
git add docs/modification_0525_steps/phase2_ch14_worker_d_classification.md docs/phase2_completion_classification.json docs/phase2_completion_classification.md docs/modification_0525_steps/phase2_completion_classification_step2_implementation_plan.md docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md
git add tests/test_phase2_completion_classification.py tools/validate_phase2_completion_classification.py
git commit -m "docs: checkpoint phase2 classification and tier a decisions"
```

If the user does not authorize a commit, write the current `git status --short --untracked-files=all` into the Step 3 final report and explicitly state that the inventory was produced on an uncommitted baseline.

Do not proceed silently on a dirty baseline without recording it.

## Step 3 Deliverables

Required:

- `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`

Optional, only if useful after the Markdown inventory exists:

- `tools/audit_interface_reuse.py`
- `tests/test_audit_interface_reuse.py`
- `docs/modification_0525_steps/phase2_interface_bridge_inventory.json`

The Markdown is required. The tool is optional and must not replace manual evidence.

## Step 3 Inventory Schema

Every concept section in `docs/modification_0525_steps/phase2_interface_bridge_inventory.md` must include:

- concept name;
- textbook definitions / ToyApollo declarations;
- Mathlib corresponding objects;
- bridge or equivalence theorems that actually exist;
- downstream post-Ch9 users;
- reuse classification for each downstream use:
  - `actual_theorem_reuse`;
  - `definition_reuse_only`;
  - `import_only`;
  - `mathlib_switch_with_bridge`;
  - `mathlib_switch_without_bridge`;
  - `reassumed_or_private_axiom`;
  - `adapter_completed`;
  - `needs_decision`;
- evidence lines with file paths and declarations;
- relation to Step 2/2.5 tasks;
- recommended next action:
  - `add_bridge_theorem`;
  - `rewrite_statement_to_reuse_existing_theorem`;
  - `prove_textbook_route`;
  - `accept_adapter_with_metadata`;
  - `keep_open_math_debt`;
  - `needs_user_decision`.

Use this table format inside each section:

```markdown
| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `prob_10_5` | `prob_10_5` | `reassumed_or_private_axiom` | `ToyApollo/Output/prob_10_5.lean:22` private axiom | Ch7 DCT does not bridge local convergence-in-probability interface to the required mean convergence theorem | Decide whether to strengthen statement or add theorem-level Vitali/DCT bridge |
```

## Required Concept Families

### Family A: DCT / Convergence

Main files:

- `ToyApollo/Output/thm_7_4.lean`
- `ToyApollo/Output/thm_7_5.lean`
- `ToyApollo/Output/thm_7_6.lean`
- `ToyApollo/Output/thm_7_7.lean`
- `ToyApollo/Output/def_10_2.lean`
- `ToyApollo/Output/def_10_3.lean`
- `ToyApollo/Output/thm_10_5.lean`
- `ToyApollo/Output/prob_10_5.lean`

Mandatory question:

- Why does `prob_10_5` not directly close from Chapter 7 DCT outputs?

Expected evidence to inspect:

```powershell
rg -n "theorem thm_7_4|tendsto_integral|dominated|ConvergesInProbability|prob_10_5|private axiom" ToyApollo/Output/thm_7_4.lean ToyApollo/Output/thm_7_5.lean ToyApollo/Output/thm_7_6.lean ToyApollo/Output/thm_7_7.lean ToyApollo/Output/def_10_2.lean ToyApollo/Output/def_10_3.lean ToyApollo/Output/thm_10_5.lean ToyApollo/Output/prob_10_5.lean
```

### Family B: Expectation / Integral / Moment Interface

Main files:

- `ToyApollo/Output/def_6_7.lean`
- `ToyApollo/Output/thm_6_7.lean`
- `ToyApollo/Output/thm_6_7__lemma_1.lean`
- `ToyApollo/Output/thm_11_3.lean`
- `ToyApollo/Output/prob_11_6.lean`
- `ToyApollo/Output/thm_11_7.lean`

Mandatory question:

- Does the project have theorem-level bridges from textbook expectation/moment notation to Mathlib integrability/moment APIs strong enough for `prob_11_6` and `thm_11_7`?

Expected evidence to inspect:

```powershell
rg -n "expectation|textbookIntegral|rthMoment|Integrable|MemLp|AEStronglyMeasurable|thm_6_7__lemma_1|thm_11_3_textbook_expectation_bridge|private axiom" ToyApollo/Output/def_6_7.lean ToyApollo/Output/thm_6_7.lean ToyApollo/Output/thm_6_7__lemma_1.lean ToyApollo/Output/thm_11_3.lean ToyApollo/Output/prob_11_6.lean ToyApollo/Output/thm_11_7.lean
```

### Family C: Distribution / Weak Convergence / Countable Sample Spaces

Main files:

- `ToyApollo/Output/prob_10_6.lean`
- `ToyApollo/Output/prob_10_10_distribution_bridge.lean`
- `ToyApollo/Output/thm_14_1.lean`
- `ToyApollo/Output/thm_14_2.lean`
- `ToyApollo/Output/prob_14_5.lean`

Mandatory question:

- Is there an actual theorem-level bridge from singleton masses on arbitrary countable spaces to bounded-test distribution convergence, or only specialized later work such as integer-valued TV convergence?

Expected evidence to inspect:

```powershell
rg -n "singleton|Countable|CountableSampleDistribution|distribution|Weak|tendsto|totalVariation|private axiom|prob_10_6_singleton_masses_to_distribution_internal" ToyApollo/Output/prob_10_6.lean ToyApollo/Output/prob_10_10_distribution_bridge.lean ToyApollo/Output/thm_14_1.lean ToyApollo/Output/thm_14_2.lean ToyApollo/Output/prob_14_5.lean ToyApollo/Output/tv_distance_core.lean
```

### Family D: Lebesgue-Stieltjes / RS Integral

Main files:

- `ToyApollo/Output/rs_stieltjes_bridge.lean`
- any output files importing or referencing `rsIntegral`, `textbookIntegral`, `StieltjesMeasureFunction`, or `StieltjesFunction.measure`.

Mandatory question:

- Are RS/Stieltjes bridges theorem-level equivalences, adapter files, or axiom-backed bridges?

Expected evidence to inspect:

```powershell
rg -n "rsIntegral|Stieltjes|textbookIntegral|axiom|theorem|bridge" ToyApollo/Output -g "*.lean"
```

### Family E: TV Distance

Main files:

- `ToyApollo/Output/tv_distance_core.lean`
- `ToyApollo/Output/prob_14_5.lean`
- `ToyApollo/Output/prob_10_6.lean`

Mandatory question:

- Can `tv_distance_core` support a reusable bridge for `prob_10_6`, or is it only used by later integer/discrete tasks?

Expected evidence to inspect:

```powershell
rg -n "totalVariationDistance|d_TV|singleton|tsum|integral|prob_14_5|prob_10_6" ToyApollo/Output/tv_distance_core.lean ToyApollo/Output/prob_14_5.lean ToyApollo/Output/prob_10_6.lean
```

### Family F: Tightness / CLT / Characteristic Functions

Main files:

- `ToyApollo/Output/def_14_3.lean`
- `ToyApollo/Output/thm_14_1.lean`
- `ToyApollo/Output/thm_14_2.lean`
- `ToyApollo/Output/thm_14_5.lean`
- `ToyApollo/Output/thm_14_6.lean`
- `ToyApollo/Output/thm_14_7.lean`
- `ToyApollo/Output/thm_14_8.lean`
- `ToyApollo/Output/ex_14_4_3.lean`

Mandatory question:

- Which Ch14 files are actual textbook-route proofs, which are Mathlib-backed adapters, and which still rely on private axioms or `thm_14_8_ProofBeyondBook`?

Expected evidence to inspect:

```powershell
rg -n "characteristic|isTightMeasureSet|def_14_3_of_mathlibTight|ProofBeyondBook|private axiom|Lindeberg|Lyapunov|SourceProofSpine" ToyApollo/Output/def_14_3.lean ToyApollo/Output/thm_14_1.lean ToyApollo/Output/thm_14_2.lean ToyApollo/Output/thm_14_5.lean ToyApollo/Output/thm_14_6.lean ToyApollo/Output/thm_14_7.lean ToyApollo/Output/thm_14_8.lean ToyApollo/Output/ex_14_4_3.lean
```

### Family G: Chapter 6 Probability Estimates / Occupancy

Main files:

- `ToyApollo/Output/prob_6_3.lean`
- `ToyApollo/Output/def_6_7.lean`
- `ToyApollo/Output/thm_6_7__lemma_1.lean`
- `ToyApollo/Output/ex_6_5_2.lean`
- `ToyApollo/Output/prob_11_9.lean`

Mandatory question:

- Does Chapter 6 contain theorem-level occupancy or balls-in-boxes results that `prob_11_9` can actually reuse, or are the statements adjacent but not connected?

Expected evidence to inspect:

```powershell
rg -n "occupancy|balls|boxes|bin|empty|exact|prob_6_3|ex_6_5_2|prob_11_9|private axiom" ToyApollo/Output/prob_6_3.lean ToyApollo/Output/def_6_7.lean ToyApollo/Output/thm_6_7__lemma_1.lean ToyApollo/Output/ex_6_5_2.lean ToyApollo/Output/prob_11_9.lean
```

## Skill And Subagent Guidance

Use skills in this order:

1. `arming-thought`: keep the investigation evidence-first.
2. `investigation-first`: required before writing conclusions.
3. `overall-planning`: use when deciding whether a gap is bridge, statement mismatch, or proof debt.
4. `superpowers:subagent-driven-development`: use only if the user explicitly authorizes subagents for the implementation run.
5. `superpowers:verification-before-completion`: use before claiming the inventory is complete.

If subagents are authorized, use read-only explorer agents with disjoint concept scopes:

- Explorer A: DCT / convergence and `prob_10_5`.
- Explorer B: distribution / weak convergence / TV and `prob_10_6`.
- Explorer C: expectation / integral / moments and `prob_11_6`, `thm_11_7`.
- Explorer D: Chapter 6 probability estimates / occupancy and `prob_11_9`.
- Explorer E: tightness / CLT / characteristic functions and Ch14 adapter/debt boundary.
- Explorer F: RS/Stieltjes bridge and early bridge/axiom patterns.

Instructions for every explorer:

- Do not edit files.
- Do not check GitHub or network.
- Return exact file paths, declaration names, and line numbers.
- Classify each downstream use as actual theorem reuse, definition reuse only, import only, Mathlib switch with bridge, Mathlib switch without bridge, reassumed/private axiom, adapter completed, or needs decision.
- Explicitly state "not found" when a bridge theorem was searched for but not found.
- Include the exact `rg` searches or file reads used.

The main agent writes the final Markdown. Subagents should not edit `docs/modification_0525_steps/phase2_interface_bridge_inventory.md` directly unless the main agent assigns a separate scratch file.

## Implementation Tasks

### Task 1: Preflight And Checkpoint

**Files:**

- Read: Step 1/2/2.5 docs listed above.
- Read: `project_ledger.json`.
- Optional commit if user authorizes.

- [ ] Run the preflight validation commands.
- [ ] Confirm `project_ledger.json` has no diff.
- [ ] Record whether the baseline is committed or dirty.
- [ ] If dirty and user has not authorized committing, proceed only after recording this in the final report.

### Task 2: Create Inventory Document Skeleton

**Files:**

- Create: `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`

Required top-level sections:

```markdown
# Phase2 Interface Bridge Inventory

Created: 2026-05-24
Status: local evidence inventory

## Purpose
## Baseline
## Reuse Classes
## Summary
## Tier A Case Studies
## Concept Families
## Cross-Cutting Findings
## Recommended Step 4 Inputs
## Validation
```

- [ ] Define the reuse classes.
- [ ] Include a clear statement that Step 3 does not modify Lean or ledger.
- [ ] Include Tier A as mandatory case studies.

### Task 3: Fill Tier A Case Studies

**Files:**

- Read: `docs/phase2_completion_classification.json`
- Read: `docs/phase2_completion_classification.md`
- Read: `phase2_prompt_packs/prob_10_5/proof_obligations.json`
- Read: `phase2_prompt_packs/prob_10_6/proof_obligations.json`
- Read: `phase2_prompt_packs/prob_11_6/proof_obligations.json`
- Read: `phase2_prompt_packs/prob_11_9/proof_obligations.json`

- [ ] Write one subsection each for `prob_10_5`, `prob_10_6`, `prob_11_6`, and `prob_11_9`.
- [ ] For each, answer:
  - what earlier concept should have been reusable;
  - what actual earlier theorem/definition exists;
  - whether the task actually uses it;
  - what is missing;
  - whether next action is bridge, statement rewrite, or proof route.

### Task 4: Fill Concept Families

**Files:**

- Read: all files listed under Required Concept Families.

- [ ] Fill Family A through Family G.
- [ ] Each family must include at least one table of downstream uses.
- [ ] Each family must cite concrete Lean declarations and line numbers.
- [ ] Each family must distinguish theorem reuse from definition reuse and imports.

### Task 5: Decide Whether Optional Tool Is Worth It

Only after the Markdown inventory exists:

- [ ] If repeated checks are mechanical, create `tools/audit_interface_reuse.py`.
- [ ] If the tool is created, add `tests/test_audit_interface_reuse.py`.
- [ ] The tool may find imports, private axioms, and declaration references, but must label its output as evidence hints, not proof-route truth.

Suggested tool output categories:

- `imports_only`;
- `private_axiom_near_concept`;
- `bridge_theorem_reference`;
- `definition_reference`;
- `mathlib_adapter_reference`;
- `needs_manual_review`.

### Task 6: Validate And Report

Run:

```powershell
rg -n "actual_theorem_reuse|definition_reuse_only|import_only|reassumed_or_private_axiom|needs_decision" docs/modification_0525_steps/phase2_interface_bridge_inventory.md
rg -n "prob_10_5|prob_10_6|prob_11_6|prob_11_9" docs/modification_0525_steps/phase2_interface_bridge_inventory.md
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

If optional tool is added:

```powershell
python tools/audit_interface_reuse.py
python -m unittest tests.test_audit_interface_reuse
```

Final report must include:

- whether preflight passed;
- whether baseline was committed or dirty;
- files created/modified;
- concept families completed;
- Tier A conclusions;
- top recommended Step 4 family order;
- whether optional tool was created;
- confirmation that no Lean files, prompt-pack JSON, or `project_ledger.json` were changed by Step 3.

## Completion Criteria

Step 3 is complete when:

- `docs/modification_0525_steps/phase2_interface_bridge_inventory.md` exists;
- all required concept families A-G are covered;
- Tier A case studies are explicitly addressed;
- every concept section cites concrete local files and declarations;
- downstream uses are classified by reuse class;
- recommended Step 4 inputs are listed by family;
- preflight validation status is recorded;
- no Lean files or `project_ledger.json` are changed.

Step 3 is **not** complete if:

- it only lists early definitions without checking post-Ch9 downstream usage;
- it says "bridge exists" only because a filename contains `bridge`;
- it omits Tier A;
- it treats `needs_decision` as proof completion;
- it starts Step 4 proof edits.

## Recommended Commit Boundary

If the baseline was already committed, commit Step 3 separately:

```powershell
git add docs/modification_0525_steps/phase2_interface_bridge_inventory.md
git commit -m "docs: inventory phase2 interface bridge reuse"
```

If optional tool is added:

```powershell
git add tools/audit_interface_reuse.py tests/test_audit_interface_reuse.py
git commit -m "test: add phase2 interface reuse audit hints"
```

Do not mix Step 3 inventory commits with Lean proof fixes.
