# Proof Debt Next-LLM Playbook

This is a practical memory note for proof-debt work.
It exists to prevent the next LLM from repeating slow or invalid repair loops.

## Current Handoff Snapshot

As of 2026-05-21, the older "Batches 1 through 6 are clean" conclusion is no
longer a valid completion claim under the stricter public-interface standard.
The previous pass closed parent `accepted_as_proof_debt` entries, but a fresh
Chapter 10-14 audit found many `proof_debt_support` entries marked `proved`
whose Lean landing is only a `Support`/`Spine` structure field or has no
theorem-level landing.

Run the strict audit before claiming any Chapter 10-14 debt is clear:

```powershell
python .\tools\audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

The generated report is:

- `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.json`
- `docs/phase2_ch10_14_clean_debt_goals.md` groups the current findings into
  execution goals.

Update on 2026-05-21: the audit distinguishes proof-package parameters from
proof-package constructors. A declaration that proves and returns a
`Support`/`Spine` package is review surface, not an error. A public declaration
that takes such a package as a parameter is still an error unless it is the
explicit `thm_14_8_ProofBeyondBook` exception. `prob_11_5` is the current small
model: the theorem proving tail summability remains public, the helper that
consumes the support is private, and the final task theorem constructs the
support internally.

This audit checks all official task output files in scope, not only theorem
tasks. Examples, problems, and definitions are included when they have official
Lean output.

Current important facts:

- No parent task currently has
  `proof_obligation_summary.status_counts.accepted_as_proof_debt > 0`, but this
  is not sufficient evidence of cleanliness.
- The only intentionally allowed proof-debt exception is
  `thm_14_8_ProofBeyondBook`, because the source text explicitly puts that
  proof beyond the book. Do not generalize this exception to ordinary
  `Support` or `Spine` packages.
- A `proof_debt_support` item marked `proved` is suspect unless its landing is
  an actual theorem/lemma proving the source step. A structure field such as
  `SomeSourceSpine.some_field` is not a proof landing.
- The lone `COMPLETED_WITH_PROOF_DEBT` task observed after Batch 4/5/6 should
  be rechecked against the strict audit rather than normalized away blindly.
- Two open `thm_14_4` child tasks can remain visible even though parent
  `thm_14_4` is `COMPLETED` and its obsolete obligations are already recorded
  at the parent level. Treat them as ledger hygiene, not active math debt.
- Historical batch/handoff notes were moved to
  `docs/archive/outdated_agent_handoffs/`. They are audit trail only, not
  current operating guidance.

## Core Rule

Proof debt is not cleared by making Lean accept a wrapper. It is cleared only
when the previously accepted assumption is replaced by local theorem-level
evidence and then passes the normal Phase2 build and semantic-review loop.

Acceptable replacement forms:

- a real local theorem proving the missing textbook step;
- a source-faithful interface translation between an existing ToyApollo theorem
  and the statement needed by the current file;
- a shared foundation theorem imported by multiple downstream tasks;
- a decomposition into smaller obligation tasks, each tracked in the ledger.

Unacceptable replacement forms:

- `axiom`;
- `constant`;
- a `structure` field that is just the old assumption under a new name;
- a theorem whose hard hypothesis is the same missing statement;
- a semantic review pass on a stale candidate or stale review basis.

The public theorem or task-facing declaration must also be clean. It is not
enough to prove `hSupport -> conclusion`; the non-exception support object must
be constructed internally from theorem-level evidence, following the `thm_9_5`
pattern.

Do not turn every normal task into a proof-debt task. The older Phase2 path
remains the default: buildable Lean plus semantic review of source claims, proof
spine, interface contract, and downstream adequacy. Use structured
`proof_obligations.json` tracking only when the task is genuinely complex:
multiple independently reviewable proof steps, repeated partial progress, or a
temporary assembly scaffold that would otherwise leak into the public theorem
interface.

## Recommended Format For Each Debt

Use this local analysis format before editing Lean:

```text
Task:
Statement:
Textbook proof spine:
Existing ToyApollo declarations:
Existing Mathlib declarations:
Lean landing declaration:
Current support/assumption being removed:
New theorem-level replacement:
Build result:
Semantic review result:
Remaining blocker:
```

This is close to the intended "analysis notebook" style: statement first,
dependencies second, proof spine third, implementation last.

## Workflow

1. Inspect the official output file and the pack candidate. Compare them if the
   file was recently edited.
2. Search existing `ToyApollo/Output` files before creating a new theorem.
3. Search bridge/foundation files; old names may still include "bridge", newer
   docs may call the same role `interface_translation` or
   `proof_debt_support`.
4. Search Mathlib for atomic API support, not as a black-box replacement for the
   textbook proof.
5. Edit the official output file or pack `draft.lean` according to the current
   Phase2 state.
6. Run `lake env lean ToyApollo/Output/<file>.lean` for fast local feedback.
7. Run the Phase2 `build-check`.
8. Run a fresh `review-now --review-subject candidate`.
9. Write the reviewer JSON from the fresh template.
10. Apply only a fresh pass result.

For sibling child tasks under the same parent, do not generate every review
result first and apply later. Promotion of one child changes the parent's
review basis and invalidates sibling review results. Use this cycle instead:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <child> --review-subject candidate
# write semantic_review_result_vM.json from that fresh request/template
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <child> --review-result <fresh-result>
```

Repeat the fresh review/apply cycle for the next sibling.

## Fast Sanity Commands

Run these before claiming any debt was cleared:

```powershell
rg -n "axiom|constant|sorry|admit" ToyApollo/Output/<target>.lean ToyApollo/Output/*bridge*.lean
rg -n "Support|support|proof_debt|accepted_as_proof_debt" ToyApollo/Output/<target>.lean phase2_prompt_packs/<task_id>
lake env lean ToyApollo/Output/<target>.lean
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
```

If the pack candidate differs from the official file, regenerate or build from
the correct candidate before semantic review.

## Review JSON Discipline

Several Batch 4/5/6 retries failed because the review JSON was structurally
close but not exact. Keep these details tight:

- `obligation_review.items[*].obligation_id` must be the parent obligation id
  from the request text, for example `obligation_4`, not
  `obl_prob_14_3_obligation_4`.
- If `semantic_review_input_vM.json` lists `direct_downstream_consumers`, add a
  `downstream_adequacy.consumers_checked` entry for every listed consumer.
- Use `covered` or `not_applicable` item statuses for a pass verdict; do not use
  custom values in schema-constrained fields.
- If `review-apply` says the basis changed, discard the result, run fresh
  `review-now`, write a new result, and apply immediately.
- If `pack` reports that a hard dependency still carries proof debt, clear the
  dependency first. Do not edit a stale pack to bypass the dependency gate.

## Lessons From The Interrupted Session

### 1. Green Lean Is Not Enough

Several official files compiled while still containing debt. The most obvious
case is `prob_10_10_distribution_bridge.lean`, which compiles because it uses
two axioms. Semantic clearance must reject that.

### 2. Stale Pack Candidates Are Dangerous

`ToyApollo/Output/ex_13_6_5.lean` was updated to use
`ex_13_6_5_GamblingTeamProcess`, but old pack candidates still carried
`hOptional`, `hThirdCase`, and `hInitialGainZero`. Build/review artifacts from
those candidates do not describe the current official output.

### 3. Existing Output Is Often The Main Source

The user's criticism was correct: many apparent gaps are already in the
textbook or in existing output files. Before inventing new foundations, inspect:

- older task outputs in `ToyApollo/Output`;
- task-local bridge/foundation files;
- Chapter 9 examples, especially `thm_9_5` style foundations;
- downstream files that already consume the same concept.

### 4. Do Not Overuse Mathlib As A Source-Proof Substitute

Mathlib can supply APIs and atomic facts. The proof spine should still follow
the textbook and existing ToyApollo declarations. A review should fail if a
candidate replaces a textbook argument with an unrelated black-box theorem and
does not prove the interface equivalence.

### 5. Shared Foundations Beat Repeated Local Debt

If several obligations need the same statement, create one source-faithful local
foundation theorem and import it. Do not create separate theorem-local support
fields. The same rule applies to Batch 2 and Batch 3: local ToyApollo imports
keep the project aligned, while Mathlib APIs should be used in Tao style when a
standard bridge already exists.

For already completed Batch 1, shared foundations included:

- CDF convergence to `TendstoInDistribution`;
- probability convergence from constant-limit distribution convergence;
- quantile measurability and quantile law facts;
- Chapter 14 weak/distribution interface;
- optional-stopping gambling-team process evidence.

## Batch 2 Suggested Order

Batch 1 is complete. The next batch should be Chapter 11 estimates and small
interfaces:

1. `prob_11_4.density_mean_interface`
2. `prob_11_5.tail_summability_support`
3. `prob_11_6.sixth_moment_support`
4. `prob_11_6.tail_summability_support`
5. `prob_11_7.variance_decay_support`
6. `prob_11_8.covariance_decay_support`
7. `prob_11_9.occupancy_moment_calculation`
8. `prob_11_10.continuous_grid_uniformization`
9. `thm_11_7.fourth_moment_expansion_tail_bound`
10. `prob_14_6.obligation_2`

Reasoning:

- The Chapter 11 debts are mostly reusable estimates, tail bounds, and concrete
  moment calculations.
- Clearing them gives useful infrastructure for later UI, tightness, and CLT
  batches.
- `prob_14_6.obligation_2` is a small local interface debt and can be handled
  after the Chapter 11 estimates without opening the full Levy/CLT batch.

## Batch 3 Suggested Order

After Batch 2, run the measure-theoretic extension and Fubini batch:

1. `ex_13_5_1.rectangle_area`
2. `ex_13_5_1.pi_lambda_extension`
3. `thm_13_14.interval_fubini_calculation`
4. `thm_13_14.pi_lambda_extension`

Reasoning:

- These obligations share rectangle/cylinder, Fubini, and pi-lambda extension
  machinery.
- They should be solved by local theorem-level evidence or shared local
  foundation lemmas, not by theorem-local support fields.
- They are separate from the later characteristic-function, Levy, tightness, and
  CLT foundations, so finishing them keeps the work bounded.

## Deprecated Batch 4/5/6 Notes

This section is historical context only. It records what the old batch process
attempted, but those batches are not considered clean under the current
Chapter 10-14 public-surface audit.

Batch 4 targeted the `thm_14_5` tightness kernel spine:

- characteristic at zero;
- Fubini identity;
- inner integral identity;
- averaged kernel identity;
- kernel/tail lower bound;
- small-window continuity estimate;
- DCT estimate;
- finite-prefix tail handling;
- final uniform tail bound.

Batch 5 targeted the Levy, characteristic-function, MGF, Slutsky, and
downstream Chapter 14 bridge tasks:

- `thm_14_6`;
- `prob_14_3`, `prob_14_4`;
- `prob_14_6` through `prob_14_10`.

Batch 6 targeted the explicit model, CLT, triangular-array, and uniform
integrability tasks:

- `prob_14_1`, `prob_14_2`, `prob_14_5`;
- `thm_14_7`, `thm_14_8`;
- `ex_14_4_3`;
- `prob_14_11`, `prob_14_12`.

Do not use the old "cleared" wording from these batches as evidence. The
current proof-debt state is determined by
`tools/audit_phase2_clean_debt_surface.py` and the fresh Phase2 review loop.

## How To Handle A Large Debt

Do not pause just because a proof is large. Convert it to smaller ledger-visible
obligations when needed:

1. Identify the exact source proof steps.
2. Check whether each step exists in output or Mathlib.
3. For each missing step, either prove it locally or promote a smaller
   obligation child.
4. Keep the parent theorem from depending on equivalent support assumptions.
5. Continue the normal counters: 15 build attempts or 15 review attempts before
   a hard failure is legitimate.

Closed child obligations should remain in the ledger as history. Do not delete
them merely because the parent proof strategy later changes; if a decomposition
is superseded, mark the old child as superseded/closed through the ledger
mechanism rather than erasing it.

## Final Reminder

The next LLM should not report a batch done until every obligation in that batch
has fresh build and semantic-review evidence, the review result corresponds to
the current candidate/review input, and the parent proof-obligation entries are
no longer `accepted_as_proof_debt`.
