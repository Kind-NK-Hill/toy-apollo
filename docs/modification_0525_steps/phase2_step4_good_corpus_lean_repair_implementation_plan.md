# Phase2 Step 4 Good Corpus Lean Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:subagent-driven-development` if the user explicitly authorizes subagents for this run; otherwise use `superpowers:executing-plans` and execute task-by-task with checkpoints. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Repair the post-Chapter-9 Lean corpus by mathematical family so it reaches a credible **Good Corpus** state: Lean builds, public task-facing theorem interfaces are clean, real proof gaps are explicit, Mathlib-backed adapters are honestly marked, and metadata no longer disguises scaffold fields or adapters as textbook proof completion.

**Architecture:** Step 4 consumes the Step 2 completion classification and Step 3 interface bridge inventory. It does not chase ledger status. It fixes or classifies tasks by mathematical family, updating Lean and prompt-pack metadata only where needed, while preserving the distinction between `textbook_proof_completed`, `mathlib_backed_adapter_completed`, `interface_bridge_completed`, `open_math_debt`, `beyond_book_exception`, and `needs_decision`.

**Tech Stack:** Lean 4/Lake, ToyApollo `ToyApollo/Output/*.lean`, Phase2 prompt-pack JSON, Step 2 classification docs, Step 3 interface bridge inventory, existing audit tools.

---

## Step 4 Definition

Step 4 is **Good Corpus Lean repair**.

It is not Textbook Complete Corpus work. A Step 4 result may still contain open mathematical debt, but that debt must be visible, classified, and not exposed as a public proof-package parameter.

Step 4 must not claim:

- every textbook proof route is formalized;
- every private axiom is removed;
- every Mathlib-backed adapter has been replaced by a textbook proof;
- ledger cleanliness means mathematical completion.

Step 4 may claim:

- public theorem interfaces are clean;
- Lean files touched by the batch build;
- audit hard errors are gone;
- metadata and classification honestly distinguish adapter, bridge, open debt, and textbook proof;
- remaining proof debt is explicit and assigned to a family.

## Required Pre-Step4 Work

Before editing Lean:

- [ ] Read `docs/phase2_completion_classification.md`.
- [ ] Read `docs/phase2_completion_classification.json`.
- [ ] Read `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`.
- [ ] Read `docs/modification_0525_steps/phase2_step4_good_corpus_family_work_queue.md`.
- [ ] Run the baseline validation:

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
- `project_ledger.json` has no diff.

If the working tree is dirty, do not silently mix Step 4 changes with Step 1-3 changes. Either:

- ask the user to authorize a checkpoint commit; or
- clearly record in the Step 4 final report that Step 4 was performed on an uncommitted baseline.

If the Step 4 family queue omits a task that appears in `docs/phase2_completion_classification.json` with `open_math_debt`, `needs_decision`, `mathlib_backed_adapter_completed`, or `beyond_book_exception`, update the queue before starting Lean edits. A completed queue that does not cover the classification file is not a completed Step 4.

The Step 4 family queue may also include non-classification review items:

- `concept_bridge_review`: a bridge/inventory file or reusable theorem seed that is not a normal task row in `docs/phase2_completion_classification.json`, but must be checked because later tasks may depend on its interface claim.
- `read_only_adapter_check`: a Lean file that is not currently a Step 2 classification row, but is part of the family validation surface and must be checked before claiming adapter/bridge status for the family.

These review items should update `docs/modification_0525_steps/phase2_interface_bridge_inventory.md` or family notes when relevant. Do not force them into `docs/phase2_completion_classification.json` unless they become task-level completion claims.

## Non-Negotiable Rules

1. Public task-facing theorems must not require callers to provide `Support`, `Spine`, `Bridge`, or non-exception `ProofBeyondBook` proof packages.
2. Internal `Support` / `Spine` structures may remain as assembly scaffolds.
3. Constructor lemmas returning `Support` may remain when they are theorem-level evidence.
4. If a support field can be proved, upgrade it to a theorem-level lemma.
5. If a support field cannot be proved, classify it as `open_math_debt` or `needs_decision`; do not expose it as a public proof parameter.
6. If a proof mainly closes a textbook-facing theorem by calling a stronger Mathlib theorem, classify it as `mathlib_backed_adapter_completed`, not `textbook_proof_completed`.
7. `proof_obligations.json` entries with `status = proved` must land on real theorem or lemma declarations, not structure field projections, support structures, private axioms, empty strings, or adapter theorems that do not prove the claimed source route.
8. `thm_14_8_ProofBeyondBook` is the only allowed beyond-book exception.
9. Direct downstream use of `thm_14_8_ProofBeyondBook` must be marked as `inherited_beyond_book_exception`, not ordinary proved debt.
10. Do not edit `project_ledger.json` unless the user explicitly asks for ledger application after Lean and metadata are stable.
11. Do not make a theorem build by adding stronger source-level assumptions unless the task is explicitly classified as `needs_decision` and the new assumption is called out in classification and the final report.
12. Every task with `support_constructor_return_only` must receive an explicit support-return review; do not assume that returning `Support` is clean merely because the audit reports only `review`.

## Public Signature And No-New-Assumption Review

For each touched task, compare the public task-facing theorem declarations before and after the family repair.

- [ ] The final theorem does not gain a new mathematical hypothesis that is absent from the textbook/source statement.
- [ ] If a new setup parameter remains public, it is source data, not a proof package.
- [ ] If a statement rewrite is necessary, classify the task as `good_corpus_needs_decision` until the user accepts the rewrite.
- [ ] Record any intentional statement change in `docs/phase2_completion_classification.md` and `docs/phase2_completion_classification.json`.
- [ ] Do not treat a clean audit as proof that the statement remained faithful.

Useful checks:

```powershell
git diff -- ToyApollo/Output/<task_id>.lean
rg -n "^theorem|^lemma|^def" ToyApollo/Output/<task_id>.lean
```

## Support-Return Constructor Review

Returning a `Support` or `Spine` object is allowed only when the constructor is theorem-level evidence, not a disguised open proof package.

For every `support_constructor_return_only` task:

- [ ] The constructor body builds without using a private axiom for the claimed proved fields.
- [ ] Each field that metadata marks `proved` lands on a real theorem or lemma, not `.field`, the structure declaration, or an empty landing.
- [ ] If the constructor uses a private axiom, the task remains `open_math_debt` or `needs_decision`.
- [ ] The final public theorem must construct or call the support internally; it must not ask the caller for support.
- [ ] If the support packages a Mathlib-backed adapter route, classify the task as `mathlib_backed_adapter_completed`, not `textbook_proof_completed`.

## Outcome Mapping

Step 4 outcomes are execution outcomes. They must map back to completion classification as follows:

| Step 4 outcome | completion `primary_class` |
| --- | --- |
| `good_corpus_closed` | `textbook_proof_completed` or `interface_bridge_completed`, depending on the proof route |
| `good_corpus_adapter_marked` | `mathlib_backed_adapter_completed` |
| `good_corpus_open_debt_exposed` | `open_math_debt` |
| `good_corpus_needs_decision` | `needs_decision` |
| `good_corpus_beyond_book_exception` | `beyond_book_exception` |
| `good_corpus_exception_inherited` | task-level class remains its real class, with `inherited_beyond_book_exception` flag |

Never promote a task to `textbook_proof_completed` from Step 4 alone unless the proof route was actually reviewed as textbook-level evidence.

For `concept_bridge_review` and `read_only_adapter_check` rows, record the review result in the queue/final report and update the bridge inventory if needed; no completion `primary_class` mapping is required unless the item is added to Step 2 classification.

## Outcome Labels

Each touched task must end Step 4 with one of these outcomes:

- `good_corpus_closed`: public interface clean, Lean builds, no private axiom/open debt remains for the scoped family obligation.
- `good_corpus_adapter_marked`: public interface clean, Lean builds, proof route is Mathlib-backed adapter and classification/metadata say so.
- `good_corpus_open_debt_exposed`: public interface clean, Lean builds, remaining proof gap is private/internal and explicitly classified as `open_math_debt`.
- `good_corpus_needs_decision`: public interface clean or intentionally scoped, Lean builds, but the current statement/interface is too weak or ambiguous; classification explains the required user decision.
- `good_corpus_beyond_book_exception`: public interface clean, Lean builds, and the task is the root allowed beyond-book exception `thm_14_8_ProofBeyondBook`.
- `good_corpus_exception_inherited`: public interface clean except for allowed inherited `thm_14_8_ProofBeyondBook`.

Do not use `completed` without one of these precise meanings.

## Skill And Subagent Guidance

Use skills in this order:

1. `arming-thought`: keep all claims evidence-based.
2. `investigation-first`: required before changing a family task.
3. `superpowers:systematic-debugging`: use for Lean build failures.
4. `superpowers:verification-before-completion`: required before reporting a family complete.
5. `superpowers:subagent-driven-development`: use only if the user explicitly authorizes subagents.

If subagents are authorized, split by disjoint family ownership:

- Worker A: Ch10 convergence / distribution family.
- Worker B: Ch11 estimate family.
- Worker C: Ch13 measure / Fubini family.
- Worker D: Ch14 CLT / tightness family.
- Optional Reviewer: read-only check of classification/metadata consistency after workers finish.

Tell every worker:

- You are not alone in the codebase.
- Do not revert edits made by others.
- Keep your write scope to your family.
- List changed files and validation commands in the final message.
- Do not edit `project_ledger.json`.

## Family Execution Order

### Family 4.2: Ch10 Convergence / Distribution

Primary files:

- `ToyApollo/Output/prob_10_5.lean`
- `ToyApollo/Output/prob_10_6.lean`
- `ToyApollo/Output/prob_10_10_distribution_bridge.lean`
- `ToyApollo/Output/prob_14_5.lean` (read-only bridge seed for the TV/countable route)
- `ToyApollo/Output/ex_10_3_2.lean`
- `ToyApollo/Output/thm_10_8.lean`

Metadata:

- `phase2_prompt_packs/prob_10_5/proof_obligations.json`
- `phase2_prompt_packs/prob_10_6/proof_obligations.json`
- `phase2_prompt_packs/ex_10_3_2/proof_obligations.json`
- `phase2_prompt_packs/thm_10_8/proof_obligations.json`

Goals:

- Remove or keep removed public DCT/countability/distribution bridge parameters such as `h_dominated_bridge` and `h_countable_bridge`.
- Check whether `prob_10_10_distribution_bridge` is a true interface bridge or hidden debt.
- Review `prob_14_5` as a read-only integer-valued TV/weak-equivalence seed for `prob_10_6`; do not treat it as directly closing the general countable-space gap unless a theorem-level generalization is added.
- Review `ex_10_3_2` setup structures as source data versus hidden proof obligations.
- Confirm `thm_10_8` has no public quantile support leak.
- Decide whether Ch10 DCT/convergence tasks reuse Chapter 7 theorem-level DCT, require a new bridge theorem, or should remain `needs_decision`.

Validation:

```powershell
lake env lean ToyApollo/Output/prob_10_5.lean
lake env lean ToyApollo/Output/prob_10_6.lean
lake env lean ToyApollo/Output/prob_10_10_distribution_bridge.lean
lake env lean ToyApollo/Output/prob_14_5.lean
lake env lean ToyApollo/Output/ex_10_3_2.lean
lake env lean ToyApollo/Output/thm_10_8.lean
rg -n "h_.*bridge|Support|Spine|ProofBeyondBook|Bridge|Setup|totalVariation|d_TV" ToyApollo/Output/prob_10_5.lean ToyApollo/Output/prob_10_6.lean ToyApollo/Output/prob_10_10_distribution_bridge.lean ToyApollo/Output/prob_14_5.lean ToyApollo/Output/ex_10_3_2.lean ToyApollo/Output/thm_10_8.lean
```

Expected Good Corpus outcome:

- public theorem interface clean;
- remaining private axiom or bridge gap is classified as `open_math_debt` or `needs_decision`;
- Mathlib-backed DCT usage is classified as adapter if applicable;
- no fake `proved` metadata.

### Family 4.3: Ch11 Estimate

Primary files:

- `ToyApollo/Output/prob_11_6.lean`
- `ToyApollo/Output/prob_11_5.lean`
- `ToyApollo/Output/prob_11_7.lean`
- `ToyApollo/Output/prob_11_8.lean`
- `ToyApollo/Output/prob_11_9.lean`
- `ToyApollo/Output/prob_11_10.lean`
- `ToyApollo/Output/thm_11_7.lean`

Metadata:

- `phase2_prompt_packs/prob_11_6/proof_obligations.json`
- `phase2_prompt_packs/prob_11_5/proof_obligations.json`
- `phase2_prompt_packs/prob_11_7/proof_obligations.json`
- `phase2_prompt_packs/prob_11_8/proof_obligations.json`
- `phase2_prompt_packs/prob_11_9/proof_obligations.json`
- `phase2_prompt_packs/prob_11_10/proof_obligations.json`
- `phase2_prompt_packs/thm_11_7/proof_obligations.json`

Goals:

- Keep tail, moment, covariance, occupancy, and uniformization proof fields out of public final theorem parameters.
- Convert provable fields into theorem-level lemmas.
- Review `prob_11_5` and `prob_11_7` support-return constructors instead of skipping them because the audit reports review-only status.
- Keep unprovable fields explicit as `open_math_debt` or `needs_decision`.
- Prevent `thm_11_7` from being reported as if all estimate details are proved.

Validation:

```powershell
lake env lean ToyApollo/Output/prob_11_5.lean
lake env lean ToyApollo/Output/prob_11_6.lean
lake env lean ToyApollo/Output/prob_11_7.lean
lake env lean ToyApollo/Output/prob_11_8.lean
lake env lean ToyApollo/Output/prob_11_9.lean
lake env lean ToyApollo/Output/prob_11_10.lean
lake env lean ToyApollo/Output/thm_11_7.lean
rg -n "private axiom|hCov|hMoment|hUniform|h_tail_summability|Support|Spine|Bridge|ProofBeyondBook" ToyApollo/Output/prob_11_5.lean ToyApollo/Output/prob_11_6.lean ToyApollo/Output/prob_11_7.lean ToyApollo/Output/prob_11_8.lean ToyApollo/Output/prob_11_9.lean ToyApollo/Output/prob_11_10.lean ToyApollo/Output/thm_11_7.lean
```

Expected Good Corpus outcome:

- final theorem public interfaces are clean;
- private axioms are visible and classified;
- support fields either have theorem-level landing or remain open;
- metadata does not mark private axioms as proved.

### Family 4.4: Ch13 Measure / Fubini

Primary files:

- `ToyApollo/Output/thm_13_14.lean`
- `ToyApollo/Output/thm_13_12.lean`
- `ToyApollo/Output/thm_13_13.lean`
- `ToyApollo/Output/ex_13_5_1.lean`

Metadata:

- `phase2_prompt_packs/thm_13_14/proof_obligations.json`
- `phase2_prompt_packs/thm_13_12/proof_obligations.json`
- `phase2_prompt_packs/thm_13_13/proof_obligations.json`
- `phase2_prompt_packs/ex_13_5_1/proof_obligations.json`

Goals:

- Distinguish actual Fubini / pi-lambda / atom-integral proof from Mathlib-backed adapters.
- Split source proof steps into theorem-level lemmas when feasible.
- Keep `thm_13_14` open if its density/Fubini/extension route still depends on private axiom or missing hypotheses.

Validation:

```powershell
lake env lean ToyApollo/Output/thm_13_14.lean
lake env lean ToyApollo/Output/thm_13_12.lean
lake env lean ToyApollo/Output/thm_13_13.lean
lake env lean ToyApollo/Output/ex_13_5_1.lean
rg -n "private axiom|hIntervals|hExtend|Support|Spine|Bridge|ProofBeyondBook" ToyApollo/Output/thm_13_14.lean ToyApollo/Output/thm_13_12.lean ToyApollo/Output/thm_13_13.lean ToyApollo/Output/ex_13_5_1.lean
```

Expected Good Corpus outcome:

- public theorem has no support/spine leak;
- Fubini/pi-lambda obligations do not land on structure fields;
- adapter proof routes are not classified as textbook completed.

### Family 4.5: Ch14 CLT / Tightness

Primary files:

- `ToyApollo/Output/thm_14_1.lean`
- `ToyApollo/Output/thm_14_2.lean`
- `ToyApollo/Output/thm_14_5.lean`
- `ToyApollo/Output/thm_14_6.lean`
- `ToyApollo/Output/prob_14_6.lean`
- `ToyApollo/Output/thm_14_7.lean`
- `ToyApollo/Output/thm_14_8.lean`
- `ToyApollo/Output/ex_14_4_1.lean`
- `ToyApollo/Output/ex_14_4_2.lean`
- `ToyApollo/Output/ex_14_4_3.lean`
- `ToyApollo/Output/prob_14_1.lean`
- `ToyApollo/Output/prob_14_2.lean`
- `ToyApollo/Output/prob_14_8.lean`
- `ToyApollo/Output/prob_14_10.lean`
- `ToyApollo/Output/prob_14_11.lean`
- `ToyApollo/Output/prob_14_12.lean`

Metadata:

- `phase2_prompt_packs/thm_14_5/proof_obligations.json`
- `phase2_prompt_packs/thm_14_6/proof_obligations.json`
- `phase2_prompt_packs/prob_14_6/proof_obligations.json`
- `phase2_prompt_packs/thm_14_7/proof_obligations.json`
- `phase2_prompt_packs/thm_14_8/proof_obligations.json`
- `phase2_prompt_packs/ex_14_4_1/proof_obligations.json`
- `phase2_prompt_packs/ex_14_4_2/proof_obligations.json`
- `phase2_prompt_packs/ex_14_4_3/proof_obligations.json`
- `phase2_prompt_packs/prob_14_1/proof_obligations.json`
- `phase2_prompt_packs/prob_14_2/proof_obligations.json`
- `phase2_prompt_packs/prob_14_8/proof_obligations.json`
- `phase2_prompt_packs/prob_14_10/proof_obligations.json`
- `phase2_prompt_packs/prob_14_11/proof_obligations.json`
- `phase2_prompt_packs/prob_14_12/proof_obligations.json`

Goals:

- Honestly classify `thm_14_1`, `thm_14_2`, `thm_14_5`, and `thm_14_6` when they are Mathlib-backed adapters.
- Keep `def_14_3_of_mathlibTight` and related bridge declarations as interface bridges, not proof debt.
- Ensure `thm_14_6_of_interval_tight` does not expose `hbridge` as a public proof package.
- Review `prob_14_6_PositiveScalingSupport` as an internal support surface and record the read-only result even if no Lean repair is needed.
- Remove or internalize Ch14 setup proof fields from public theorem parameters where feasible.
- Include `prob_14_2`, `ex_14_4_1`, and `ex_14_4_2` in the Lindeberg-Levy setup debt review; do not leave them outside Step 4 just because their public surfaces are already clean.
- Keep `prob_14_12` adapter status explicit and separate from strict textbook proof completion.
- Preserve `thm_14_8_ProofBeyondBook` as the only beyond-book exception.
- Mark downstream uses of `thm_14_8_ProofBeyondBook` as inherited exceptions.

Validation:

```powershell
lake env lean ToyApollo/Output/thm_14_1.lean
lake env lean ToyApollo/Output/thm_14_2.lean
lake env lean ToyApollo/Output/thm_14_5.lean
lake env lean ToyApollo/Output/thm_14_6.lean
lake env lean ToyApollo/Output/prob_14_6.lean
lake env lean ToyApollo/Output/thm_14_7.lean
lake env lean ToyApollo/Output/thm_14_8.lean
lake env lean ToyApollo/Output/ex_14_4_1.lean
lake env lean ToyApollo/Output/ex_14_4_2.lean
lake env lean ToyApollo/Output/ex_14_4_3.lean
lake env lean ToyApollo/Output/prob_14_1.lean
lake env lean ToyApollo/Output/prob_14_2.lean
lake env lean ToyApollo/Output/prob_14_8.lean
lake env lean ToyApollo/Output/prob_14_10.lean
lake env lean ToyApollo/Output/prob_14_11.lean
lake env lean ToyApollo/Output/prob_14_12.lean
rg -n "hbridge|private axiom|Support|Spine|ProofBeyondBook|SourceProofSpine|Lindeberg|Lyapunov" ToyApollo/Output/thm_14_1.lean ToyApollo/Output/thm_14_2.lean ToyApollo/Output/thm_14_5.lean ToyApollo/Output/thm_14_6.lean ToyApollo/Output/prob_14_6.lean ToyApollo/Output/thm_14_7.lean ToyApollo/Output/thm_14_8.lean ToyApollo/Output/ex_14_4_1.lean ToyApollo/Output/ex_14_4_2.lean ToyApollo/Output/ex_14_4_3.lean ToyApollo/Output/prob_14_1.lean ToyApollo/Output/prob_14_2.lean ToyApollo/Output/prob_14_8.lean ToyApollo/Output/prob_14_10.lean ToyApollo/Output/prob_14_11.lean ToyApollo/Output/prob_14_12.lean
```

Expected Good Corpus outcome:

- public theorem interfaces are clean except the allowed/inherited beyond-book exception;
- CLT/tightness/Lyapunov/Lindeberg setup status is explicit;
- adapter, bridge, open debt, and textbook proof are not mixed.

## Metadata Update Rules

After each Lean change:

- [ ] Update the corresponding `phase2_prompt_packs/<task_id>/proof_obligations.json` only when the Lean file builds.
- [ ] Update `docs/phase2_completion_classification.json`.
- [ ] Update `docs/phase2_completion_classification.md`.
- [ ] If the change affects a reuse or bridge conclusion, update `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`.
- [ ] Regenerate clean-debt audit reports when relevant:

```powershell
python tools/audit_phase2_clean_debt_surface.py --write-report
```

Metadata must never mark these as `proved`:

- private axiom;
- structure field projection;
- support structure itself;
- empty landing;
- Mathlib-backed adapter when the obligation claims textbook source-route proof.

## Step 4 Batch Validation

For every family batch:

```powershell
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Run the touched Lean files individually with `lake env lean`.

Before reporting a family done:

- [ ] Search for public proof package parameters.
- [ ] Compare public theorem signatures against the pre-repair version and record any new source-level assumption.
- [ ] Complete support-return constructor review for every `support_constructor_return_only` task in the family.
- [ ] Check no new private axiom was added unless explicitly classified as new open debt and accepted by the user.
- [ ] Check no metadata landing points to a structure field.
- [ ] Check adapter status is explicit where applicable.
- [ ] Check `project_ledger.json` still has no diff unless explicitly requested.

## Step 4 Completion Criteria

Step 4 is complete when every task in the Step 4 family work queue has one of the precise Step 4 outcomes:

- `good_corpus_closed`;
- `good_corpus_adapter_marked`;
- `good_corpus_open_debt_exposed`;
- `good_corpus_needs_decision`;
- `good_corpus_beyond_book_exception`;
- `good_corpus_exception_inherited`.

Step 4 is also required to satisfy:

- all touched Lean files build;
- audit hard errors remain zero or only the explicitly accepted beyond-book exception is allowed;
- public task-facing interfaces are clean;
- metadata does not lie about proof route;
- completion classification and interface inventory are updated to match the Lean state;
- `project_ledger.json` is untouched unless the user explicitly asks for ledger application.

Step 4 is **not** complete if:

- a public theorem still asks for a non-exception proof package;
- a private axiom is marked as proved;
- a Mathlib-backed adapter is marked as textbook proof completed;
- `thm_14_8_ProofBeyondBook` is copied into other tasks as ordinary proof debt;
- a family is skipped because the ledger looked clean.

## Step 4 Final Report

The final report must include:

- baseline status: committed or dirty;
- families attempted;
- files changed;
- Lean validation commands and results;
- audit/classification validation commands and results;
- tasks classified as `good_corpus_closed`;
- tasks classified as `good_corpus_adapter_marked`;
- tasks classified as `good_corpus_open_debt_exposed`;
- tasks classified as `good_corpus_needs_decision`;
- tasks classified as `good_corpus_beyond_book_exception`;
- tasks classified as `good_corpus_exception_inherited`;
- explicit statement that the corpus is **Good Corpus**, not **Textbook Complete Corpus**.

## Recommended Commit Boundaries

Commit by family, not by ledger status:

```powershell
git add ToyApollo/Output/<family-files> phase2_prompt_packs/<family-packs> docs/phase2_completion_classification.json docs/phase2_completion_classification.md docs/modification_0525_steps/phase2_interface_bridge_inventory.md docs/phase2_ch10_14_clean_debt_surface_audit.md docs/phase2_ch10_14_clean_debt_surface_audit.json
git commit -m "repair: good corpus <family-name> phase2 status"
```

If a family only changes docs/metadata:

```powershell
git add phase2_prompt_packs/<family-packs> docs/phase2_completion_classification.json docs/phase2_completion_classification.md docs/modification_0525_steps/phase2_interface_bridge_inventory.md
git commit -m "docs: mark <family-name> phase2 good corpus status"
```

Do not mix Step 4 family work with Step 5 mechanism changes.
