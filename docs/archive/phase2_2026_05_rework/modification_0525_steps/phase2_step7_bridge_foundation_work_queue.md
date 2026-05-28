# Phase2 Step 7 Bridge And Foundation Work Queue

Created: 2026-05-25
Status: current queue for Step 7 proof-production

## Queue Rule

Step 7 queue items come only from Step 6 frozen route/signature handoffs. A row
is not ready for Step 7 if it only says "prove the theorem" or "needs
foundation". It must name at least one concrete lemma signature or a concrete
statement patch to try.

## Priority Queue

| priority | task_id | Step 6 handoff | first productive unit | allowed result |
| ---: | --- | --- | --- | --- |
| 1 | `thm_11_7` | tail-summability from fourth-moment route | Land a small tail/moment foundation lemma before attempting full tail summability. | `foundation_lemma_landed` or `hard_blocked_with_failed_lean_attempt` |
| 2 | `thm_13_14` | interval-Fubini and generator-extension route | Land one density/Fubini or generator-extension foundation lemma. | `foundation_lemma_landed`, `statement_patch_landed`, or `hard_blocked_with_failed_lean_attempt` |
| 3 | `ex_14_4_3` | not yet selected in current Step 6 | Requires a fresh Step 6 route/signature freeze for local Lyapunov debt. | not ready |

## `thm_11_7` Foundation Queue

Current blocker:

- public `h_tail_summability` premise in `ToyApollo/Output/thm_11_7.lean`;
- obligation `obl_thm_11_7_fourth_moment_expansion_tail_bound`.

Step 7 should try the smallest useful lemma first. Candidate order:

1. `thm_11_7_pseries_tail_bound`
   - Goal: prove the summability/finite-ENNReal tail fact needed after a
     `C / n^2` bound.
   - Why first: it is likely independent of the hardest moment expansion.
2. `thm_11_7_markov_fourth_tail_bound`
   - Goal: convert a fourth-moment bound on a partial sum into a probability
     bound for the deviation event.
   - Requires: current event/interface compatibility.
3. `thm_11_7_centered_independence`
   - Goal: transport independence to centered variables.
   - Requires: measurability and integrability interface check.
4. `thm_11_7_fourth_moment_sum_bound`
   - Goal: prove the finite-sum fourth-moment estimate.
   - This is likely the hardest Step 7 unit and should not be attempted before
     the smaller tail/Markov pieces are checked.
5. `thm_11_7_tail_summability_from_fourth_moment`
   - Goal: assemble the full support theorem only after enough foundation
     lemmas have landed.

Hard blocker evidence must include:

- exact attempted theorem statement;
- Lean error shape;
- missing local or Mathlib declaration;
- whether the issue is proof search, statement insufficiency, or incompatible
  definitions.

## `thm_13_14` Foundation Queue

Current blockers:

- public `hIntervals` premise in `ToyApollo/Output/thm_13_14.lean`;
- public `hExtend` premise in `ToyApollo/Output/thm_13_14.lean`;
- obligations `obl_thm_13_14_interval_fubini_calculation` and
  `obl_thm_13_14_pi_lambda_extension`.

Candidate order:

1. `thm_13_14_joint_density_measurable_nonneg`
   - Goal: expose the measurability/nonnegativity facts currently implicit in
     `thm_13_14_jointDensityLaw`.
   - If the current definition cannot provide these, land a statement patch or
     return to Step 5.
2. `thm_13_14_closed_interval_cylinder_measurable`
   - Goal: make the interval-cylinder sets usable by later Fubini/generator
     steps.
3. `thm_13_14_interval_fubini_from_joint_density`
   - Goal: prove the interval identity support from density and integrability
     facts.
4. `thm_13_14_interval_generator_extension`
   - Goal: prove the generator/pi-lambda extension in the local interface.
5. `thm_13_14_pi_lambda_extension_from_intervals`
   - Goal: assemble the extension support only after the generator lemma is
     available.

This target is likely to need a statement patch if the current joint-density
law does not carry enough Mathlib-facing regularity. Such a patch is a valid
Step 7 result only if it is actually landed and build-verified.

## Non-Ready Items

| task_id | reason |
| --- | --- |
| `prob_10_5` | Step 5 kept it open until a Vitali/DCT bridge or statement rewrite is accepted. |
| `prob_11_6` | Step 5 kept it open until moment-interface prerequisites are accepted. |
| `prob_11_9` | Step 5 kept it open until concrete occupancy-model route is accepted. |
| `thm_14_5` | Accepted adapter; no Step 7 source-spine upgrade unless Step 5 is reopened. |
| `thm_14_7` | Deferred; needs its own Step 6 route/signature freeze before Step 7. |

## Required Report

Each Step 7 run must create or update a report under
`docs/modification_0525_steps/` with:

```text
task_id
selected_queue_item
attempted_signature
files_touched
result: foundation_lemma_landed | statement_patch_landed | hard_blocked_with_failed_lean_attempt
Lean commands run
validator commands run
obligation/classification changes
Step 8 readiness update
```
