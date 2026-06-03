# Phase2 Artifacts

## Authority

Build authority:

- `phase2_prompt_packs/<task_id>/candidate_vN.lean`
- `phase2_prompt_packs/<task_id>/build_result_vN.json`

These decide technical build readiness only.

Review authority:

- latest valid `semantic_review_input_vN.json`
- latest valid `semantic_review_result_vN.json`
- matching `semantic_review_request_vN.json`
- matching review subject hash and review-basis hash

These decide semantic review verdict and `proof_class`.

Apply authority:

- `review-apply`
- ledger metadata written by `review-apply`, especially `phase2_status`

Only `review-apply` can land clean completion, and only when
`phase2_status=pass`.

## Evidence And Context

These must be read when relevant, but they do not complete tasks:

- source TeX and source plans;
- `proof_obligations.json`;
- dependency decision context;
- downstream/import scans;
- classification history;
- audit evidence;
- ledger runtime status;
- hash/freshness evidence.

## Cache, Reports, And History

These are not authorities:

- `project_ledger.json` by itself;
- `metadata.json`;
- `context.md`;
- `operator_prompt.md`;
- `verify_result_vN.json`;
- `verification_report.md`;
- `attempt_history.json`;
- `failure_summary.md`;
- batch state JSON/Markdown;
- classification JSON/Markdown;
- validation and audit reports;
- old prompt-pack artifacts.

Use them for review context, diagnostics, repair planning, and reproducibility.
Do not hand-edit them to declare completion.

`phase2_prompt_packs/*/proof_obligations.json` is task content/context. Keep
mechanism refactors separate from proof-obligation content repairs unless a
mechanism regression test explicitly needs a fixture update.
