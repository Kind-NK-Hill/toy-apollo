# Output Auxiliary Module Classification

This file defines how to treat modules under MAT
`ProbabilityTheory/chapter_XX/` whose basename is not a live Phase 1 plan task
id. These modules are not Phase2 task roots and must not be counted as fresh
existing-output review tasks. The checked-in MAT manifest is the current
per-file classification authority; this document records the runtime rule.

There is no formal `helper` class. A non-task output module must be classified
as one of:

- `support`: reusable or parent-owned proof/API support imported by one or more
  task modules or support modules.
- `bridge`: reusable equivalence or API bridge between textbook-facing
  statements and local/Mathlib infrastructure.
- `family_member`: a split implementation module owned by a specific textbook
  task family. The parent ledger task remains the review root.
- `retired_build_probe`: stale build-probe output that is not an official task,
  support module, bridge, or family member. These files must not remain under
  MAT `ProbabilityTheory`.

`PackBuildCheck_*` modules are retired build probes. They are not tasks, are not
valid completion evidence, and should not be imported by Lean output modules.
Historical prompt-pack logs may still mention old `PackBuildCheck_*` or
`ToyApollo.Output.*` module names because they record prior build attempts;
those mentions are historical text only and do not make a second output tree
authoritative. Current scratch modules live under `ProbabilityTheory/Scratch`
and are deleted after validation.

## Review Scope Rule

Fresh existing-output review sweeps use live Phase 1 plan task ids as review
roots. Filename matching is case-insensitive so Kenneth-preserved names such as
`Ex_1_3_1.lean` still resolve to the canonical task id.
Support, bridge, and family-member modules may be inspected as context or
dependency evidence, but they do not receive independent task-level
`phase2_status` unless explicitly promoted into the ledger as tasks.
