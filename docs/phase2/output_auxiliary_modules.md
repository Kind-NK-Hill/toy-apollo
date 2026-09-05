# Output Auxiliary Module Classification

This file classifies `ProbabilityTheory/**/*.lean` modules whose basename is not a
live `project_ledger.json` task id. These modules are not Phase2 task roots and
must not be counted as fresh existing-output review tasks.

There is no formal `helper` class. A non-task output module must be classified
as one of:

- `support`: reusable or parent-owned proof/API support imported by one or more
  task modules or support modules.
- `bridge`: reusable equivalence or API bridge between textbook-facing
  statements and local/Mathlib infrastructure.
- `family_member`: a split implementation module owned by a specific textbook
  task family. The parent ledger task remains the review root.
- `retired_build_probe`: stale build-probe output that is not an official task,
  support module, bridge, or family member. These files should not remain under
  `ProbabilityTheory`.

`PackBuildCheck_*` modules are retired build probes. They are not tasks, are not
valid completion evidence, and should not be imported by Lean output modules.
Historical prompt-pack logs may still mention old `PackBuildCheck_*` module
names because they record prior build attempts; those mentions are historical
text only and do not make a current `ProbabilityTheory` module authoritative.

## Current Non-Task Core Modules

These files were previously grouped by preflight as `other_unknown`. They are
now explicitly classified below.

| Module | Classification | Owner / Use |
|---|---|---|
| `ch8_bernoulli_bool_core` | support | Shared Bernoulli Bool support for Chapter 8 examples. |
| `ch8_discrete_pmf_core` | support | Discrete PMF support for Chapter 8 Bernoulli/PMF examples. |
| `etemadi_pairwise_iid_slln` | support | Reusable Etemadi/pairwise-iid SLLN support surface. |
| `ex_1_2_2_dirichlet_gamma_beta` | family_member | Split implementation for `ex_1_2_2`. |
| `ex_1_2_2_dirichlet_gamma_chart` | family_member | Split implementation for `ex_1_2_2`. |
| `ex_1_2_2_dirichlet_gamma_core` | family_member | Split implementation for `ex_1_2_2`. |
| `ex_6_3_1_harmonic` | family_member | Split implementation for `ex_6_3_1`. |
| `rs_partition_core` | support | Reusable finite partition/Riemann-Stieltjes core support. |
| `thm_1_1_bad_cells` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_basic` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_common_limit` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_common_refinement_monotonicity` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_common_refinement_points` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_darboux_gap` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_darboux_refinement` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_finite_discontinuity` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_oscillation` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_oscillation_basic` | family_member | Split implementation for `thm_1_1`. |
| `thm_1_1_refinement` | family_member | Split implementation for `thm_1_1`. |
| `thm_10_8_inverse_comparison` | family_member | Split implementation for `thm_10_8`. |
| `thm_10_8_quantile_convergence` | family_member | Split implementation for `thm_10_8`. |
| `thm_10_8_quantile_defs` | family_member | Split implementation for `thm_10_8`. |
| `thm_10_8_quantile_law` | family_member | Split implementation for `thm_10_8`. |
| `thm_10_8_quantile_space` | family_member | Split implementation for `thm_10_8`. |
| `thm_14_4_dominating_measure` | family_member | Split implementation/support for `thm_14_4`. |
| `thm_9_5_dirichlet` | family_member | Split implementation for `thm_9_5`. |
| `thm_9_5_fubini` | family_member | Split implementation for `thm_9_5`. |
| `thm_9_5_kernel` | family_member | Split implementation for `thm_9_5`. |
| `tv_distance_core` | support | Shared total-variation distance support. |

## Review Scope Rule

Fresh existing-output review sweeps use live ledger task ids as review roots.
Support, bridge, and family-member modules may be inspected as context or
dependency evidence, but they do not receive independent task-level
`phase2_status` unless explicitly promoted into the ledger as tasks.
