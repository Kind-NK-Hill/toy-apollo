# P5-P9 Health Reconciliation

This note records the post-scan handling for the P5-P9 output-health queue.
It is a maintenance boundary note, not a ledger update and not a completion
claim by itself.

## P5: `prob_7_3`

Action taken: split the large partition support along an existing proof
boundary.

- `ToyApollo/Output/prob_7_3_partition_atom_support.lean` owns the
  atom-free endpoint and compact-positive-subset lemmas.
- `ToyApollo/Output/prob_7_3_partition_protected_support.lean` owns compact
  distance, protected endpoint sets, sorted adjacency, and final endpoint
  finset refinement.
- `ToyApollo/Output/prob_7_3_partition_support.lean` remains as a compatibility
  import wrapper.

The split does not rename exported declarations and does not broaden the
Riemann-Stieltjes bridge surface.

## P6: Chapter 1 Riemann-Stieltjes Core

Action taken: no Lean migration in this pass.

The controlling boundary remains `docs/phase2/rs_stieltjes_boundary.md`. That
note already records the `thm_1_2` interval-concatenation blocker: the raw
source statement is unsafe under the current closed-interval Darboux interface
without additional endpoint-continuity or no-common-jump hypotheses.

For this health pass, the correct action is to preserve that boundary rather
than start a broad migration across `def_1_2`, `rs_stieltjes_*`, and
`thm_1_1_*`. Future work should split or migrate those files only when it is
repairing a specific source-facing task route.

## P7: `prob_14_11`

Action taken: no ordinary health split in this pass.

`prob_14_11_support.lean` intentionally imports `ToyApollo.Output.thm_14_8`.
That inherited exception boundary should remain visible because the task route
depends on the existing `thm_14_8` support surface. Treating this file as an
ordinary large support split would risk hiding the boundary that downstream
review needs to see.

## P8: `prob_14_8`

Action taken: evidence reconciliation only.

The current family is already split across subsequence, Montel, MGF, and thin
proof-support files. The older health classification is stale relative to the
current proof-shaped files and review evidence. No Lean move is needed unless a
future proof change reopens the family.

## P9: `thm_11_7`

Action taken: split parent-owned support out of the source-facing parent.

- `ToyApollo/Output/thm_11_7_support.lean` owns the fourth-moment expansion,
  centered moment bounds, tail estimates, and summability support.
- `ToyApollo/Output/thm_11_7.lean` keeps the task text, final assembly helper,
  and exported theorem statement.

The exported theorem name and statement remain unchanged.
