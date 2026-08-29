# Documentation

Start with the stable public model, then enter operator detail only when the
task requires it.

## Public project model

- [`architecture.md`](architecture.md): Module ownership, runtime flow, trust
  model, and source/evidence planes.
- [`repository_scope.md`](repository_scope.md): what is public, what remains
  private, and how case studies are curated.
- [`development.md`](development.md): fresh-checkout setup and focused checks.
- [`../examples/case-studies/`](../examples/case-studies/): two inspectable
  review-and-repair histories.

## Current operator contracts

Use these when operating or modifying Phase 2:

- [`phase2/README.md`](phase2/README.md)
- [`phase2/workflow.md`](phase2/workflow.md)
- [`phase2/status_contract.md`](phase2/status_contract.md)
- [`phase2/review_criteria.md`](phase2/review_criteria.md)
- [`phase2/artifacts.md`](phase2/artifacts.md)
- [`phase2/tools.md`](phase2/tools.md)
- [`workspace_state.md`](workspace_state.md)
- [`evidence_bridge.md`](evidence_bridge.md)

`phase2/textbook_complete_targets.json` is a data artifact, not a policy
entry.

## Policy notes

Use these when changing dependency modeling or source-plan Interfaces:

- [`chapter1_2_cross_chapter_dependency.md`](chapter1_2_cross_chapter_dependency.md)
- [`dependency_decision_trail.md`](dependency_decision_trail.md)
- [`interface_dependency_policy.md`](interface_dependency_policy.md)

## Generated reports

Classification, alignment, completion, and unfinished-task reports are cache or
diagnostic artifacts. They may provide review context, but they do not decide
Phase 2 completion. The operational state is queried from the private workspace
database and is not published as a current snapshot.

## Historical material

Historical migration notes, one-off handoffs, old provider plans, rescue logs,
and superseded Phase 2 policies remain preserved in the private evidence plane
and Git history. They are intentionally absent from the default public
documentation surface.

Archive material is never runtime truth merely because it exists. Current CLI
behavior and the current contracts above take precedence.

## Search behavior

Normal `rg` searches exclude generated packs, artifact paths, and private
archives through `.rgignore`. Use `rg --no-ignore` only for a deliberate
evidence audit.
