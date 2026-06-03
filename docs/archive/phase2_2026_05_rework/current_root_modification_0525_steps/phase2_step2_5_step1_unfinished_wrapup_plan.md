# Phase2 Step 2.5 Step 1 Unfinished Wrap-Up Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` if the user explicitly authorizes subagents for this run; otherwise use `superpowers:executing-plans` and execute task-by-task with checkpoints. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** After Step 2 creates the independent completion classification, use that classification to wrap up the unfinished mathematical work left by Step 1: replace selected `private axiom` / `open_math_debt` placeholders with theorem-level Lean proofs, without reintroducing public proof-package parameters or polluting `project_ledger.json`.

**Architecture:** Step 2.5 is a proof-completion queue, not a classification pass and not another audit cleanup. It consumes `docs/phase2_completion_classification.json` and targets entries with `primary_class = "open_math_debt"` plus flags such as `private_axiom_internalized`. Each completed task must remove or shrink the relevant private axiom, add theorem-level landings, update the classification artifact, then update prompt-pack metadata only after Lean builds.

**Tech Stack:** Lean 4/Lake, ToyApollo `ToyApollo/Output/*.lean`, Phase2 prompt-pack JSON metadata, completion-classification JSON/Markdown, existing audit tooling.

---

## Position In The Workflow

Step 1 did the public-interface cleanup:

- public `Support` / `Spine` / `Bridge` / proof-package parameters were removed from many task-facing theorems;
- several debts were internalized as `private axiom`;
- audit hard errors dropped to zero.

Step 2 creates an independent classification layer:

- `docs/phase2_completion_classification.json`;
- `docs/phase2_completion_classification.md`;
- no `project_ledger.json` edits;
- tasks are honestly classified as `textbook_proof_completed`, `mathlib_backed_adapter_completed`, `interface_bridge_completed`, `open_math_debt`, `beyond_book_exception`, or `needs_decision`.

Step 2.5 starts only after Step 2 exists.

Step 2.5 does **not** repeat Step 2. It uses Step 2's classification to choose which remaining Step 1 debts are worth proving next.

## Entry Condition

Do not start Step 2.5 until all of these are true:

- `docs/phase2_completion_classification.json` exists.
- `docs/phase2_completion_classification.md` exists.
- The classification explicitly lists all current `open_math_debt` tasks from Step 1.
- The classification marks private-axiom debts with `private_axiom_internalized`.
- `project_ledger.json` is not changed by Step 2.
- Baseline checks pass:

```powershell
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

If Step 2 has not been implemented yet, stop and implement Step 2 first.

## Non-Negotiable Rules

- Do not add public proof-package parameters back to final task-facing theorems.
- Do not mark an obligation `proved` if the landing is a private axiom, structure field, support structure, empty string, or adapter theorem that does not prove the source route.
- Do not use `sorry`, `admit`, or a new `axiom` to replace an old private axiom.
- Do not edit `project_ledger.json`.
- Do not remove useful internal `Support` / `Spine` structures just for naming hygiene.
- Do not try to solve every post-Chapter-9 debt in one batch. Each task should end with its own Lean validation.
- Do not treat Mathlib usage as bad. It is acceptable when recorded honestly as a bridge or adapter. Step 2.5 only upgrades tasks whose classification says the remaining blocker is genuine `open_math_debt`.

## Scope

Step 2.5 targets **only** Step 1 leftovers that are:

- already public-interface clean;
- still classified as `open_math_debt`;
- backed by an explicit private axiom or documented open theorem-level gap;
- small enough to attack as a bounded proof task.

Step 2.5 does **not** target:

- `mathlib_backed_adapter_completed` tasks unless the user explicitly asks for textbook-route upgrade;
- `beyond_book_exception` task `thm_14_8`;
- broad Chapter 14 setup-debt tasks whose proof requires a new large theory layer, unless smaller prerequisite lemmas are first isolated.

## Required First Reads

Read these before doing proof work:

- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`
- `docs/modification_0525_steps/phase2_completion_classification_step2_implementation_plan.md`
- `docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md`
- `docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.json`

For each task, read:

- `ToyApollo/Output/<task_id>.lean`
- `phase2_prompt_packs/<task_id>/proof_obligations.json`
- local dependencies found by `rg -n "<key declaration or concept>" ToyApollo/Output -g "*.lean"`

## Selection Rule

Pick the next task by this order:

1. Public interface is already clean.
2. Remaining debt is exactly one private axiom or one sharply described theorem-level gap.
3. Existing local lemmas likely cover most of the proof.
4. Removing the private axiom will not force stronger public assumptions.
5. The task is upstream of other tasks.

Avoid starting with tasks whose metadata already says the current statement is too weak or missing source hypotheses, unless the first action is to split out a prerequisite theorem.

## Step 2.5 Queue

### Tier A: Smallest Focused Wrap-Up Candidates

Start here. These are still nontrivial, but their debt is narrow enough to investigate one at a time.

| order | task | current blocker | target |
| ---: | --- | --- | --- |
| 1 | `prob_10_5` | `private axiom prob_10_5_dominated_probability_to_mean_internal` | Replace the dominated-convergence-in-probability-to-mean private axiom with theorem-level proof or a local bridge theorem using Chapter 7 DCT facts. |
| 2 | `prob_10_6` | `private axiom prob_10_6_singleton_masses_to_distribution_internal` | Prove the singleton-mass-to-countable-distribution direction or isolate the exact missing countability/distribution bridge. |
| 3 | `prob_11_6` | `private axiom prob_11_6_sixthMomentSupport_internal` | Prove sixth-moment support from independence, zero mean, and uniform boundedness, then keep the existing tail-summability theorem. |
| 4 | `prob_11_9` | `private axiom prob_11_9_occupancy_moment_calculation_internal` | Prove the occupancy second-moment calculation or add the missing finite balls-in-boxes model as theorem-level local setup. |

### Tier A Pass Outcome, 2026-05-24

The 2026-05-24 continuation processed all four default Tier A tasks. None was
silently patched with stronger hidden assumptions. Each task is now assigned a
Step 2.5 outcome in the completion-classification docs:

| task | Step 2.5 outcome | reason |
| --- | --- | --- |
| `prob_10_5` | `needs_decision` | Current statement lacks theorem-level measurability and uniform-integrability bridge hypotheses for the available Chapter 7 DCT/Vitali route. |
| `prob_10_6` | `needs_decision` | The reverse singleton-mass-to-bounded-test direction needs an arbitrary countable-space singleton-to-TV and TV-to-bounded-test bridge, or an equivalent finite-truncation/countable-integral route not currently landed locally. |
| `prob_11_6` | `needs_decision` | The sixth-moment replacement requires an independent-sum moment expansion layer plus explicit measurability, integrability, a.e. uniform-bound, and zero-mean mixed-term cancellation landings. |
| `prob_11_9` | `needs_decision` | The public statement does not encode the finite independent uniform balls-in-boxes model needed for the empty-box second-moment calculation. The nearby `ex_6_5_2` finite model covers a different one-box exact-occupancy expectation and does not connect to this abstract `X`. |

### Tier B: Medium Proof Debts

Start these only after at least one Tier A task is closed.

| order | task | current blocker | target |
| ---: | --- | --- | --- |
| 5 | `prob_11_8` | `private axiom prob_11_8_covarianceDecaySupport_internal` | Prove AR(1) MemLp, variance recursion/bound, and covariance decay as theorem-level landings. |
| 6 | `thm_11_7` | `private axiom thm_11_7_tail_summability_internal` | Prove the fourth-moment expansion and tail-summability route from the public fourth-moment source assumption. |

### Tier C: Large Analytic Debts

Do not start these until the user explicitly accepts a longer proof effort.

| order | task | current blocker | target |
| ---: | --- | --- | --- |
| 7 | `prob_11_10` | `private axiom prob_11_10_continuous_grid_uniformization_internal` | Prove finite-grid / Glivenko-Cantelli uniformization, including tail/tightness, monotonicity, countable event assembly, measurability, and sandwich estimate. |
| 8 | `thm_13_14` | `private axiom thm_13_14_conditional_expectation_internal` | Prove the density/Fubini and generator-extension route at theorem level. |
| 9 | `ex_14_4_3` | `private axiom ex_14_4_3_lyapunov_condition_internal` | Prove Lyapunov fourth-moment/Riemann-sum verification while preserving inherited `thm_14_8_ProofBeyondBook`. |

## Per-Task Workflow

For each task:

- [ ] Read the classification entry in `docs/phase2_completion_classification.json`.
- [ ] Read the Lean file and identify the exact private axiom or open theorem gap.
- [ ] Read the prompt-pack obligations and note the currently open obligation IDs.
- [ ] Search for local theorem reuse:

```powershell
rg -n "<private_axiom_name>|<support_name>|<concept_keyword>" ToyApollo/Output -g "*.lean"
```

- [ ] Decide whether the current public theorem statement is strong enough to prove the missing step.
- [ ] If the statement is too weak, stop and record `needs_decision`; do not patch around it with a stronger private axiom.
- [ ] Add theorem-level lemmas or bridge theorems.
- [ ] Replace the private axiom use with the theorem-level landing.
- [ ] Remove the private axiom only after the file builds.
- [ ] Run the Lean validation:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
```

- [ ] Run local surface check:

```powershell
rg -n "private axiom|axiom|sorry|admit|h_.*bridge|Support|Spine|ProofBeyondBook" ToyApollo/Output/<task_id>.lean
```

- [ ] The command may still show internal support constructors or the allowed `thm_14_8_ProofBeyondBook`; manually verify no new public proof package was introduced.
- [ ] Update `phase2_prompt_packs/<task_id>/proof_obligations.json` only after Lean builds.
- [ ] Update `docs/phase2_completion_classification.json`:
  - remove `private_axiom_internalized` if the private axiom is gone;
  - change `primary_class` only if the proof route now justifies it;
  - keep `open_math_debt` if any other private axiom remains.
- [ ] Update `docs/phase2_completion_classification.md` to match the JSON.
- [ ] Run classification validation if implemented:

```powershell
python tools/validate_phase2_completion_classification.py
```

- [ ] Run audit:

```powershell
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

- [ ] If the task outcome is `needs_decision`, record that outcome and continue
  to the next Tier A task. Do not stop the Step 2.5 pass merely because one task
  cannot be closed by theorem-level proof in the current statement.

## Completion Criteria For One Task

A Step 2.5 task is complete only when:

- the target private axiom is removed or no longer used;
- the Lean file builds;
- no public proof-package parameter was introduced;
- the relevant obligation has a theorem-level `lean_landing`;
- `proof_obligations.json` does not mark a private axiom, support structure, structure field, or empty landing as `proved`;
- `docs/phase2_completion_classification.json` and `.md` reflect the new state;
- audit still has `error_task_count = 0`;
- `project_ledger.json` remains untouched.

## Completion Criteria For Step 2.5

Step 2.5 is a Tier A wrap-up pass by default. It is **not** complete after one
Tier A task is reviewed. A worker must continue through every Tier A task unless
the user explicitly stops the run.

Step 2.5 is complete only when all Tier A tasks have been assigned one of these
final Step 2.5 outcomes:

- `closed`: the targeted private axiom is removed or no longer used, the Lean
  file builds, and the task is reclassified away from
  `private_axiom_internalized`;
- `needs_decision`: the current theorem statement is too weak, required source
  hypotheses are missing, or the replacement proof requires a larger theory
  layer; this must be recorded in both classification files and prompt-pack
  metadata;
- `deferred_by_user`: the user explicitly paused or redirected the Tier A pass.

The default Tier A set is:

- `prob_10_5`;
- `prob_10_6`;
- `prob_11_6`;
- `prob_11_9`.

After all Tier A tasks have one of the outcomes above, the worker must report a
Tier A summary and name the next available Tier B task. Only then may the worker
ask whether to continue into Tier B/C.

Do not define Step 2.5 as "all post-Chapter-9 math debt is gone." That would
recreate the same unbounded Step 1 problem. But also do not stop after the first
Tier A task that becomes `needs_decision`; that would fail to wrap up the Step 1
leftovers that Step 2.5 was created to handle.

## Task-Specific Notes

### `prob_10_5`

Current blocker:

- `ToyApollo/Output/prob_10_5.lean`: `private axiom prob_10_5_dominated_probability_to_mean_internal`.

Required investigation:

- Check whether Chapter 7 DCT files provide enough theorem-level adapter facts:
  - `ToyApollo/Output/thm_7_4.lean`
  - `ToyApollo/Output/thm_7_5.lean`
  - `ToyApollo/Output/thm_7_6.lean`
  - `ToyApollo/Output/thm_7_7.lean`
- If current statement lacks almost-everywhere convergence or integrable domination strong enough for DCT, do not silently add them as hidden assumptions.

### `prob_10_6`

Current blocker:

- `ToyApollo/Output/prob_10_6.lean`: `private axiom prob_10_6_singleton_masses_to_distribution_internal`.

Required investigation:

- Determine whether the missing direction is pure countable-set measure extensionality or a textbook distribution-interface bridge.
- Search existing distribution and total-variation files before proving from scratch.

### `prob_11_6`

Current blocker:

- `ToyApollo/Output/prob_11_6.lean`: `private axiom prob_11_6_sixthMomentSupport_internal`.

Existing local value:

- The tail-summability route after sixth-moment support is already theorem-level.

Target:

- Replace only the sixth-moment support axiom first.

### `prob_11_9`

Current blocker:

- `ToyApollo/Output/prob_11_9.lean`: `private axiom prob_11_9_occupancy_moment_calculation_internal`.

Known risk:

- Metadata says no local finite independent uniform balls-in-boxes probability model was found.

Target:

- Either prove the model/theorem locally or mark the task `needs_decision`; do not pretend the finite model exists.

### `prob_11_8`

Current blocker:

- `ToyApollo/Output/prob_11_8.lean`: `private axiom prob_11_8_covarianceDecaySupport_internal`.

Known prerequisite:

- Need theorem-level MemLp, variance-bound, and covariance-recursion facts for the AR(1) process.

### `thm_11_7`

Current blocker:

- `ToyApollo/Output/thm_11_7.lean`: `private axiom thm_11_7_tail_summability_internal`.

Known prerequisite:

- Fourth-moment expansion, zero mixed terms from independence, product bounds, Markov inequality, and summability.

### `prob_11_10`

Current blocker:

- `ToyApollo/Output/prob_11_10.lean`: `private axiom prob_11_10_continuous_grid_uniformization_internal`.

Known risk:

- Metadata says the older public implication was too weak without CDF tail/tightness and pathwise monotonicity hypotheses.

### `thm_13_14`

Current blocker:

- `ToyApollo/Output/thm_13_14.lean`: `private axiom thm_13_14_conditional_expectation_internal`.

Known risk:

- Metadata says the current public theorem needs density nonnegativity/measurability/integrability and generator-extension support to replace the private axiom.

### `ex_14_4_3`

Current blocker:

- `ToyApollo/Output/ex_14_4_3.lean`: `private axiom ex_14_4_3_lyapunov_condition_internal`.

Boundary:

- Keep `H : thm_14_8_ProofBeyondBook C.theoremSetup` as inherited beyond-book exception.
- Do not reintroduce public `hLyapunov`.

## Validation Batch

Before starting:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

For each touched task:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
```

After each completed task:

```powershell
python tools/audit_phase2_clean_debt_surface.py --write-report
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

If a classification validator exists:

```powershell
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
```

## Reporting Format

The worker's final report must include:

- Tier A status table with one row for each of `prob_10_5`, `prob_10_6`,
  `prob_11_6`, and `prob_11_9`;
- task attempted;
- private axiom or open debt targeted;
- whether the private axiom was removed, reduced, or left;
- Lean validation command and result;
- audit result;
- classification update made;
- prompt-pack metadata update made;
- whether `project_ledger.json` remained untouched;
- next unclosed Tier A task, if any.

If the worker reports after only one Tier A task and the user did not explicitly
stop the run, the report must say "partial Step 2.5 progress", not "goal
complete".

## Recommended Commit Boundary

Commit each completed proof-debt removal separately:

```powershell
git add ToyApollo/Output/<task_id>.lean phase2_prompt_packs/<task_id>/proof_obligations.json docs/phase2_completion_classification.json docs/phase2_completion_classification.md docs/phase2_ch10_14_clean_debt_surface_audit.md docs/phase2_ch10_14_clean_debt_surface_audit.json
git commit -m "proof: close <task_id> internalized phase2 debt"
```

If the task is reclassified to `needs_decision` rather than closed:

```powershell
git add docs/phase2_completion_classification.json docs/phase2_completion_classification.md phase2_prompt_packs/<task_id>/proof_obligations.json
git commit -m "docs: mark <task_id> phase2 debt as needs decision"
```

Do not mix Step 2.5 proof work with Step 2 classification creation in the same commit.
