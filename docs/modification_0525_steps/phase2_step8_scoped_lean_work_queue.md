# Phase2 Step 8 Scoped Lean Work Queue

Created: 2026-05-25
Status: current queue for target-theorem implementation

## Queue Rule

Step 8 queue items are target theorem implementation items. A target enters this
queue only after Step 6 freezes its route/signatures and Step 7 either lands the
necessary bridge/foundation lemmas or proves that no separate foundation step is
needed.

## Current Queue

| priority | task_id | status | Step 8 action |
| ---: | --- | --- | --- |
| 1 | `prob_10_6` | already complete | No action unless regression appears. |
| 2 | `thm_11_7` | waiting on Step 7 | After Step 7 lands tail-summability foundation evidence, remove public `h_tail_summability` and route final theorem through internal evidence. |
| 3 | `thm_13_14` | waiting on Step 7 | After Step 7 lands interval-Fubini and extension evidence, remove public `hIntervals` / `hExtend` and route final theorem through internal evidence. |
| 4 | `ex_14_4_3` | not selected | Needs fresh Step 6 route freeze and Step 7 Lyapunov foundation work. |
| 5 | `thm_14_5` | accepted adapter | No Step 8 upgrade unless Step 5 explicitly reopens source-spine route. |

## `thm_11_7` Step 8 Target

Current final theorem issue:

- public theorem still takes `h_tail_summability`;
- classification remains `open_math_debt`;
- Step 8 cannot start until Step 7 supplies enough theorem-level evidence to
  construct `thm_11_7_tailSummabilitySupport P X mu`.

Required Step 8 reduction:

```text
remove public h_tail_summability
construct thm_11_7_tailSummabilitySupport internally from Step 7 lemmas
call thm_11_7_from_tailSummability
update obligation contract for obl_thm_11_7_fourth_moment_expansion_tail_bound
```

Allowed result:

- `target_textbook_completed` if the whole tail route is internalized;
- `target_debt_reduced` if one public premise/private obligation is removed but
  another part remains open;
- `hard_blocked_with_failed_lean_attempt` if final assembly fails despite
  landed Step 7 lemmas.

## `thm_13_14` Step 8 Target

Current final theorem issue:

- public theorem still takes `hIntervals`;
- public theorem still takes `hExtend`;
- classification remains `open_math_debt`;
- Step 8 cannot start until Step 7 supplies interval-Fubini and extension
  evidence, or an accepted statement patch changes the target.

Required Step 8 reduction:

```text
remove public hIntervals and hExtend
construct thm_13_14_intervalFubiniSupport internally from Step 7 lemmas
construct thm_13_14_piLambdaExtensionSupport internally from Step 7 lemmas
call thm_13_14_from_intervalFubini_piLambda
update obligations for interval_fubini_calculation and pi_lambda_extension
```

Allowed result:

- `target_textbook_completed` if both supports are internalized;
- `target_debt_reduced` if one support is internalized and the other remains
  explicitly open;
- `statement_patch_landed` if a prior Step 7 statement patch changes the target
  interface and all touched files build;
- `hard_blocked_with_failed_lean_attempt` if final assembly fails against
  landed Step 7 lemmas.

## Report Format

Each Step 8 run must create or update a report under
`docs/modification_0525_steps/`:

```text
task_id
Step 6 handoff used
Step 7 lemmas consumed
files_touched
public theorem before
public theorem after
result: target_textbook_completed | target_debt_reduced | statement_patch_landed | hard_blocked_with_failed_lean_attempt
Lean commands run
validator commands run
obligation/classification changes
remaining open debt
```

## Hard Stop

If a Step 8 worker cannot identify the Step 7 lemma that should remove a public
premise or private axiom, stop and return to Step 7. Do not invent a new public
premise in the final theorem.
