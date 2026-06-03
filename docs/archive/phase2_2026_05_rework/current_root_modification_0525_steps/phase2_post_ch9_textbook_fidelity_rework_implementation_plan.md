# Post Chapter 9 Textbook Fidelity Rework Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` if the user explicitly authorizes subagents for this run; otherwise use `superpowers:executing-plans` and execute task-by-task with checkpoints. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring the current post-Chapter-9 corpus toward the corrected "Chapter 1-8 level": Lean files build, public task-facing interfaces do not expose hidden proof packages, and proof route status is classified honestly as textbook proof, Mathlib-backed adapter, interface bridge, or open math debt.

**Architecture:** Treat this as corpus cleanup, not mechanism expansion. First remove public hidden assumptions and open proof-debt parameters from task-facing theorem interfaces; then repair metadata only after the Lean theorem-level landing exists; finally classify Mathlib-backed adapters honestly instead of forcing them into "textbook proof completed."

**Tech Stack:** Lean 4/Lake, ToyApollo `ToyApollo/Output/*.lean`, Phase2 prompt-pack JSON metadata, Python audit helpers, local docs only.

---

## Non-Negotiable Constraints

- Do not check GitHub, remote commits, or network sources unless the user explicitly asks.
- Do not treat audit string matches as mathematical proof. Audit is only a triage signal.
- Do not change `project_ledger.json` or `proof_obligations.json` before the corresponding Lean theorem-level proof or honest classification is in place.
- Do not remove internal `Support` or `Spine` structures just because their names appear. Internal assembly scaffolds are allowed.
- Public task-facing theorems must not require non-exception `Support`, `Spine`, `Bridge`, or `ProofBeyondBook` arguments.
- The only allowed `ProofBeyondBook` exception is `thm_14_8_ProofBeyondBook`.
- If a theorem is closed mainly by a stronger Mathlib theorem, classify it as `mathlib_backed_adapter_completed`, not `textbook_proof_completed`.
- If the next worker sees unrelated local changes, preserve them. Do not use destructive git commands.

## Required First Reads

Read these files before editing:

- `docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.json`
- `docs/proof_debt_next_llm_playbook.md`
- `docs/phase2_prompt_pack_workflow.md`
- `docs/phase2_candidate_guidelines.md`
- `tools/audit_phase2_clean_debt_surface.py`
- `tests/test_phase2_clean_debt_surface_audit.py`

Read these Lean files for concrete patterns:

- `ToyApollo/Output/thm_9_5.lean`
- `ToyApollo/Output/thm_9_5_dirichlet.lean`
- `ToyApollo/Output/thm_10_8.lean`
- `ToyApollo/Output/thm_14_5.lean`
- `ToyApollo/Output/def_14_3.lean`
- `ToyApollo/Output/thm_14_8.lean`

Read these metadata files before changing related tasks:

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
- `phase2_prompt_packs/thm_14_7/proof_obligations.json`
- `phase2_prompt_packs/thm_14_8/proof_obligations.json`
- `phase2_prompt_packs/ex_14_4_3/proof_obligations.json`
- `phase2_prompt_packs/prob_14_1/proof_obligations.json`
- `phase2_prompt_packs/prob_14_8/proof_obligations.json`
- `phase2_prompt_packs/prob_14_10/proof_obligations.json`
- `phase2_prompt_packs/prob_14_11/proof_obligations.json`

## Acceptance Classes To Use

- `textbook_proof_completed`: statement is textbook-facing and proof follows the source route at theorem/lemma level.
- `mathlib_backed_adapter_completed`: statement is textbook-facing, but proof mainly specializes a stronger Mathlib theorem.
- `interface_bridge_completed`: theorem connects a ToyApollo textbook object to a Mathlib object.
- `open_math_debt`: theorem still depends on an axiom, public proof package, public bridge parameter, added mathematical assumption, or accepted beyond-book package.
- `public_interface_leak`: task-facing theorem exports `Support`, `Spine`, `Bridge`, or a proof-obligation argument that should be internal.
- `metadata_only_cleanliness_risk`: metadata says clean/proved, but the Lean proof route is adapter-only or the landing is not a theorem-level proof.
- `needs_decision`: user must decide whether adapter status is acceptable or whether a textbook proof route must be added.

## Skill And Subagent Policy

When implementing this plan:

- Start with `arming-thought` or an equivalent "facts first" discipline.
- Use `investigation-first` before changing a theorem whose dependencies are unclear.
- Use `superpowers:subagent-driven-development` only if the user explicitly asks for subagents in the implementation turn.
- If subagents are allowed, split by disjoint write scopes:
  - Worker A: `prob_10_5`, `prob_10_6`.
  - Worker B: `thm_13_14`.
  - Worker C: Chapter 11 group: `prob_11_6`, `prob_11_8`, `prob_11_9`, `prob_11_10`, `thm_11_7`.
  - Worker D: Chapter 14 classification and large setup debts: `thm_14_5`, `thm_14_6`, `thm_14_7`, `ex_14_4_3`, `prob_14_1`, `prob_14_8`, `prob_14_10`, `prob_14_11`.
- Tell each worker: they are not alone in the codebase; they must not revert edits made by others; they must list changed files and validation commands in their final response.
- Use `superpowers:verification-before-completion` before claiming any task is done.

## Baseline Commands

Run these before editing and save the outputs in the worker notes:

```powershell
git status --short
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report
```

For each Lean task touched, run:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
```

After each completed task, run:

```powershell
python tools/audit_phase2_clean_debt_surface.py --write-report
```

Run the strict audit only after the current batch is expected to be clean:

```powershell
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

## Phase 1: P0 Public Interface And Open Debt Blockers

### Task 1: Fix `prob_10_5`

**Current class:** `public_interface_leak`, likely `open_math_debt`.

**Evidence to verify locally:**

- `ToyApollo/Output/prob_10_5.lean:21` defines public theorem `prob_10_5`.
- `ToyApollo/Output/prob_10_5.lean:26` exposes `h_dominated_bridge`.
- `ToyApollo/Output/prob_10_5.lean:32` closes the theorem by applying that bridge.

**Files:**

- Modify: `ToyApollo/Output/prob_10_5.lean`
- Then, if Lean proof is real: `phase2_prompt_packs/prob_10_5/proof_obligations.json`

**Steps:**

- [ ] Inspect the exact theorem statement and local imports.
- [ ] Search for reusable DCT/in-probability tools in `ToyApollo/Output/thm_7_4.lean`, `ToyApollo/Output/thm_7_5.lean`, `ToyApollo/Output/thm_7_6.lean`, `ToyApollo/Output/thm_7_7.lean`, and nearby Chapter 10 files.
- [ ] Replace the public `h_dominated_bridge` parameter with an internal theorem-level lemma or a direct proof.
- [ ] Keep the statement faithful to the task; do not add a stronger user-facing assumption to hide the bridge.
- [ ] Run `lake env lean ToyApollo/Output/prob_10_5.lean`.
- [ ] Check there is no public artificial bridge parameter:

```powershell
rg -n "h_.*bridge|Bridge|Support|Spine|ProofBeyondBook" ToyApollo/Output/prob_10_5.lean
```

**Validation:** Lean file builds and public `prob_10_5` no longer accepts `h_dominated_bridge` or equivalent public proof package.

### Task 2: Fix `prob_10_6`

**Current class:** `public_interface_leak`, likely `open_math_debt`.

**Evidence to verify locally:**

- `ToyApollo/Output/prob_10_6.lean:28` defines public theorem `prob_10_6`.
- `ToyApollo/Output/prob_10_6.lean:31` exposes `h_countable_bridge`.
- `ToyApollo/Output/prob_10_6.lean:34` closes the theorem by applying that bridge.

**Files:**

- Modify: `ToyApollo/Output/prob_10_6.lean`
- Then, if Lean proof is real: `phase2_prompt_packs/prob_10_6/proof_obligations.json`

**Steps:**

- [ ] Inspect the theorem statement and determine whether the bridge is a missing countable-set probability proof or only notation translation.
- [ ] Search for reusable discrete distribution/countable mass lemmas in `ToyApollo/Output`, especially Chapter 6, Chapter 10, and `tv_distance_core.lean`.
- [ ] Internalize or prove the countable bridge at theorem level.
- [ ] Remove the public `h_countable_bridge` parameter from the task-facing theorem.
- [ ] Run `lake env lean ToyApollo/Output/prob_10_6.lean`.
- [ ] Check public surface:

```powershell
rg -n "h_.*bridge|Bridge|Support|Spine|ProofBeyondBook" ToyApollo/Output/prob_10_6.lean
```

**Validation:** Lean file builds and public `prob_10_6` no longer accepts `h_countable_bridge` or equivalent public proof package.

### Task 3: Fix `prob_11_10`

**Current class:** `open_math_debt`.

**Evidence to verify locally:**

- `ToyApollo/Output/prob_11_10.lean:65` defines public theorem `prob_11_10`.
- `ToyApollo/Output/prob_11_10.lean:69` exposes `hUniform`.
- `ToyApollo/Output/prob_11_10.lean:77` applies `hUniform`.
- `phase2_prompt_packs/prob_11_10/proof_obligations.json:78` records `continuous_grid_uniformization`.
- `phase2_prompt_packs/prob_11_10/proof_obligations.json:91` has empty landing.
- `phase2_prompt_packs/prob_11_10/proof_obligations.json:92` is open.

**Files:**

- Modify: `ToyApollo/Output/prob_11_10.lean`
- Then, if Lean proof is real: `phase2_prompt_packs/prob_11_10/proof_obligations.json`

**Steps:**

- [ ] Inspect the finite-grid/uniformization statement and assumptions.
- [ ] Search local Chapter 11 files for reusable variance, covariance, and grid estimates.
- [ ] Prove a theorem-level uniformization lemma or classify the exact missing mathematical proof as open.
- [ ] If proved, remove the public `hUniform` parameter and construct the required fact internally.
- [ ] Run `lake env lean ToyApollo/Output/prob_11_10.lean`.
- [ ] Check public surface:

```powershell
rg -n "hUniform|Support|Spine|Bridge|ProofBeyondBook" ToyApollo/Output/prob_11_10.lean
```

**Validation:** Lean file builds and the public theorem no longer asks the caller for the uniformization proof.

### Task 4: Fix `thm_13_14`

**Current class:** `open_math_debt`.

**Evidence to verify locally:**

- `ToyApollo/Output/thm_13_14.lean:329` defines final theorem `thm_13_14`.
- `ToyApollo/Output/thm_13_14.lean:336` exposes `hIntervals`.
- `ToyApollo/Output/thm_13_14.lean:340` exposes `hExtend`.
- `ToyApollo/Output/thm_13_14.lean:352` applies `hExtend hIntervals`.
- `phase2_prompt_packs/thm_13_14/proof_obligations.json:34` records open interval Fubini support.
- `phase2_prompt_packs/thm_13_14/proof_obligations.json:69` records open pi-lambda extension support.

**Files:**

- Modify: `ToyApollo/Output/thm_13_14.lean`
- Then, if Lean proof is real: `phase2_prompt_packs/thm_13_14/proof_obligations.json`

**Steps:**

- [ ] Inspect existing rectangle/cylinder helper theorems in `ToyApollo/Output/thm_13_14.lean`.
- [ ] Search `ToyApollo/Output/thm_13_12.lean`, `ToyApollo/Output/thm_13_13.lean`, and `ToyApollo/Output/ex_13_5_1.lean` for reusable Fubini and pi-lambda patterns.
- [ ] Prove theorem-level interval/Fubini and extension lemmas, or leave the task explicitly open if the proof is too large.
- [ ] If proved, remove public `hIntervals` and `hExtend`.
- [ ] Run `lake env lean ToyApollo/Output/thm_13_14.lean`.
- [ ] Check public surface:

```powershell
rg -n "hIntervals|hExtend|Support|Spine|Bridge|ProofBeyondBook" ToyApollo/Output/thm_13_14.lean
```

**Validation:** Lean file builds and the final theorem no longer exports interval/Fubini or extension proof packages.

## Phase 2: P1 Chapter 11 Estimate Group

These tasks are independent enough for separate workers if subagents are allowed, but they share local patterns. Start with the easiest proof and reuse the style.

| Task | Current class | Evidence | Action | Validation |
|---|---|---|---|---|
| `prob_11_6` | `open_math_debt` | `ToyApollo/Output/prob_11_6.lean:196` final theorem; `:202` public `_hSixth`; `phase2_prompt_packs/prob_11_6/proof_obligations.json:38` sixth moment support | Prove sixth-moment expansion at theorem level; remove public `_hSixth` if it is only proof debt | `lake env lean ToyApollo/Output/prob_11_6.lean`; no public `_hSixth` proof package |
| `prob_11_8` | `open_math_debt` | `ToyApollo/Output/prob_11_8.lean:46` final theorem; `:49` public `hCov`; metadata has open `covariance_decay_support` | Prove AR(1) covariance decay or classify as open; remove public `hCov` when proved | `lake env lean ToyApollo/Output/prob_11_8.lean`; no public `hCov` proof package |
| `prob_11_9` | `open_math_debt` | `ToyApollo/Output/prob_11_9.lean:145` final theorem; `:148` public `hMoment`; metadata open `occupancy_moment_calculation` | Prove occupancy moment calculation; remove public `hMoment` | `lake env lean ToyApollo/Output/prob_11_9.lean`; no public `hMoment` proof package |
| `thm_11_7` | `open_math_debt` | `ToyApollo/Output/thm_11_7.lean:245` final theorem; `:249` public `_hfourth`; `:250` public `h_tail_summability` | Prove fourth-moment/tail estimate chain; remove public proof packages | `lake env lean ToyApollo/Output/thm_11_7.lean`; no public `_hfourth` or `h_tail_summability` proof package |

For each task:

- [ ] Read the Lean file and its `proof_obligations.json`.
- [ ] Search for already proved estimates in `ToyApollo/Output/prob_11_5.lean`, `ToyApollo/Output/prob_11_7.lean`, and neighboring Chapter 11 outputs.
- [ ] Add theorem-level lemmas rather than structure-field landings.
- [ ] Run the task Lean file.
- [ ] Update metadata only after the theorem-level landing exists.

## Phase 3: P2 Honest Classification And Interface Hygiene

### Task 5: Classify or upgrade `thm_14_5`

**Current class:** `mathlib_backed_adapter_completed`, `metadata_only_cleanliness_risk`, `needs_decision`.

**Evidence:**

- `ToyApollo/Output/thm_14_5.lean:430` defines public theorem `thm_14_5`.
- `ToyApollo/Output/thm_14_5.lean:437` uses Mathlib `isTightMeasureSet_of_tendsto_charFun`.
- `ToyApollo/Output/thm_14_5.lean:442` uses `def_14_3_of_mathlibTight`.
- `phase2_prompt_packs/thm_14_5/proof_obligations.json` marks many source obligations as proved with landing `thm_14_5`.

**Allowed outcomes:**

- Adapter outcome: keep Lean proof as is, classify metadata/docs as `mathlib_backed_adapter_completed`, and stop claiming textbook proof completion.
- Textbook outcome: prove the source route feeding `thm_14_5_uniformTailBound` and route public `thm_14_5` through `thm_14_5_of_uniformTailBound`.

**Validation:** Either the metadata/docs honestly mark adapter status, or the public proof route no longer relies mainly on Mathlib tightness theorem.

### Task 6: Classify and clean `thm_14_6`

**Current class:** `mathlib_backed_adapter_completed`, with possible public helper interface issue.

**Evidence:**

- `ToyApollo/Output/thm_14_6.lean:459` defines the main theorem.
- `ToyApollo/Output/thm_14_6.lean:477` uses Mathlib compactness/subsequence route.
- `ToyApollo/Output/thm_14_6.lean:488` defines `thm_14_6_of_interval_tight`.
- `ToyApollo/Output/thm_14_6.lean:490` exposes `hbridge : def_14_3_IntervalMathlibTightBridge Pseq`.

**Action:**

- [ ] Keep Mathlib-backed adapter classification if this theorem intentionally relies on Prokhorov-style compactness.
- [ ] If `thm_14_6_of_interval_tight` is task-facing, internalize or rename/classify its bridge parameter so it is not mistaken for proof debt.
- [ ] Run `lake env lean ToyApollo/Output/thm_14_6.lean`.

**Validation:** Main theorem builds; docs/metadata do not claim strict textbook proof route unless that route is actually formalized.

## Phase 4: P3 Large Chapter 14 Setup Debts

These tasks are large. Do not start them before P0 is clean unless the user changes priority.

| Task | Current class | Evidence | Action | Validation |
|---|---|---|---|---|
| `prob_14_1` | `open_math_debt` | `ToyApollo/Output/prob_14_1.lean:212` setup structure; `:305` theorem takes setup; metadata open finite Polya/Stirling obligations | Prove Polya urn finite law and Stirling-to-Beta CDF or keep explicitly open | `lake env lean ToyApollo/Output/prob_14_1.lean`; no public setup if completed |
| `prob_14_8` | `open_math_debt` | `ToyApollo/Output/prob_14_8.lean:64` setup; `:77` field; `:84` theorem returns field | Prove MGF-to-characteristic convergence theorem-level route | `lake env lean ToyApollo/Output/prob_14_8.lean` |
| `prob_14_10` | `open_math_debt` | `ToyApollo/Output/prob_14_10.lean:86` setup; `:95` moments-to-MGF field; `:133` theorem | Prove moments-to-MGF setup route | `lake env lean ToyApollo/Output/prob_14_10.lean` |
| `prob_14_11` | `open_math_debt`, inherited exception | `ToyApollo/Output/prob_14_11.lean:35` setup; `:90` theorem also takes `thm_14_8_ProofBeyondBook` | Prove non-beyond-book setup fields; keep only inherited `thm_14_8` exception | `lake env lean ToyApollo/Output/prob_14_11.lean` |
| `thm_14_7` | `open_math_debt` | `ToyApollo/Output/thm_14_7.lean:205` setup; `:230`, `:250`, `:259` take setup | Prove centering, quadratic characteristic expansion, and independent sum characteristic route | `lake env lean ToyApollo/Output/thm_14_7.lean` |
| `ex_14_4_3` | `open_math_debt`, inherited exception | `ToyApollo/Output/ex_14_4_3.lean:348` Lyapunov setup; `:392` public `hLyapunov`; `:393` inherited `H` | Prove Lyapunov fourth-moment bound; keep only inherited beyond-book exception | `lake env lean ToyApollo/Output/ex_14_4_3.lean` |
| `thm_14_8` | allowed exception | `ToyApollo/Output/thm_14_8.lean:167` defines `thm_14_8_ProofBeyondBook` | Do not remove; keep as unique beyond-book exception | `lake env lean ToyApollo/Output/thm_14_8.lean`; audit accepts only this exception |

## Metadata Update Rules

Only update a `proof_obligations.json` item to `proved` when all of the following are true:

- The Lean file builds.
- `lean_landing` names an actual theorem or lemma.
- The landing is not a structure field projection.
- The landing is not the support predicate or structure itself.
- The landing is not empty.
- The proof route classification is honest.

Use these statuses consistently:

- `proved` with `review_status: accepted` for theorem-level proof landings.
- `accepted_as_proof_debt` only for `thm_14_8_ProofBeyondBook`.
- `open` for real unproved mathematical obligations.
- Adapter classification should be recorded in docs/metadata as adapter status, not disguised as source-proof completion.

## Final Acceptance Gate

The next worker should not claim the corpus is clean until all required local checks pass:

```powershell
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report
python tools/audit_phase2_clean_debt_surface.py --fail-on-errors
```

For each touched Lean file:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
```

Final report must include:

- Files changed.
- Lean validation commands run.
- Audit commands run.
- Tasks still classified as `open_math_debt`.
- Tasks accepted only as `mathlib_backed_adapter_completed`.
- Confirmation that `thm_14_8_ProofBeyondBook` is the only beyond-book exception.

## Recommended First Commit Boundary

Before implementation, commit the current evidence/planning docs if the user wants a stable baseline:

```powershell
git add docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md
git commit -m "docs: record post chapter9 textbook fidelity rework plan"
```

Then implement P0 only. Do not mix P0 theorem fixes with P2/P3 classification work in the same commit.
