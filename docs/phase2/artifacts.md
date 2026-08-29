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
- matching complete review-input hash, rendered prompt/context, review subject
  hash, and review-basis hash

These decide semantic review verdict and `proof_class`.
Existing-output review subjects are bound only to
`ToyApollo/Output/<task_id>.lean`; legacy `output_lean_files` copies are shadow
evidence, not alternate review subjects. The review basis separately hashes the
resolved `inputs/<source_plan>.tex` file and the task content, so changing the
source TeX invalidates an older request even when ledger/plan text is unchanged.
The inline task/candidate/context shown to the reviewer must also match those
bound artifacts; reviewer-visible context changes produce a different cache
key.

Math Review Gate evidence:

- `phase2_prompt_packs/<task_id>/math_proof_skeleton_vN.md`
- `phase2_prompt_packs/<task_id>/math_review_result_vN.json`
- metadata/status fields:
  `math_review_gate_required`, `math_review_gate_status`,
  `latest_math_proof_skeleton_file`, `latest_math_proof_skeleton_hash`,
  `latest_math_review_result_file`, `latest_math_review_result_hash`, and
  `latest_math_review_verdict`

These decide only whether a triggered task may enter Lean author/build. They do
not decide completion, do not replace semantic review, and do not write clean
status.

Apply authority:

- `review-apply`
- ledger metadata written by `review-apply`, especially `phase2_status`

Only `review-apply` can land clean completion, and only when
`phase2_status=pass`.

Successful candidate apply also records the subject hash, original review-
basis hash, and full post-apply basis hash as an idempotence receipt. That
receipt authorizes a no-op replay only while all bound evidence remains
unchanged; it is not a substitute for a fresh review after any drift.

## Evidence And Context

These must be read when relevant, but they do not complete tasks:

- source TeX and source plans;
- Math Review Gate skeleton/review artifacts;
- dependency decision context;
- downstream/import scans;
- classification history;
- audit evidence;
- ledger runtime status;
- hash/freshness evidence.

## Cache, Reports, And History

These are not authorities:

- the frozen legacy `project_ledger.json` by itself;
- `metadata.json`;
- `context.md`;
- `operator_prompt.md`;
- `verify_result_vN.json`;
- `verification_report.md`;
- `attempt_history.json`;
- `failure_summary.md`;
- `semantic_fail_triage_vN.json`;
- `prepared_diagnoser_prompt_vN.txt`;
- `math_proof_skeleton_vN.md`;
- `math_review_result_vN.json`;
- batch state JSON/Markdown;
- classification JSON/Markdown;
- validation and audit reports;
- old prompt-pack artifacts.
- retired full-review sidecar `state*.json` / `reviews*.json` files.

Use them for review context, diagnostics, repair planning, and reproducibility.
Do not hand-edit them to declare completion.

Historical `phase2_prompt_packs/*/proof_obligations.json` files are inert
audit fixtures. Active runtime paths must not generate, bind, review, apply,
gate, or plan from them; deleting those historical files is a separate archival
decision.

Legacy `obl_*` and nested `obl_obl_*` packs are historical audit evidence, not
default author/review queue items. Current ledgers should not retain those child
task rows; old fixtures or imported legacy state may still be readable for
audit. They must not regain completion authority, create new nested
obligations, or bypass the parent/support `build-check -> review-now ->
review-apply` chain.
