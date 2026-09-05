# Prospective paired review pilot

**Status: executable protocol, synthetic QA and one two-task live feasibility run
complete; independent human adjudication remains pending.** No quality improvement is claimed.
This helper is separate from Phase 2 acceptance and never reads or writes the
operational ledger, canonical Lean corpus, or historical review authority.

## Decision and scope

Test one question: with the same model and total token/time allowance, does a
source-blind Lean-to-natural-language translation help a subsequent reviewer
avoid accepting a source mismatch, and what does it cost?

Before collecting responses, freeze one copied manifest containing at most eight
new tasks, source/Lean byte hashes, the exact model identifier, and per-arm input
token, output token, and elapsed-time limits. Pin provider settings and tool
access in the manifest's `model_config` object and copy it into every response;
the scorer checks exact equality. Use
one attempt per task and arm, separate fresh sessions, and a preregistered
counterbalanced order (ordinary first on odd cases, assisted first on even cases).
Do not alter tasks, prompts, budgets or adjudication policy after seeing results.
These bounds support a feasibility decision, not a population accuracy estimate.

The two [public demonstration inputs](../examples/review-comparison-pilot/README.md)
are newly authored examples with pending adjudication. They are deliberately
small and public; use separately selected prospective tasks for an empirical
claim. This protocol does not revive discarded historical experiments or use
previous PASS/FAIL records as truth.

## Information flow

1. `prepare` checks the manifest and every input hash. It writes one ordinary
   request with the source and Lean, and a separate translation request containing
   only the Lean and a neutral task label. It never exports adjudications.
2. Give the translation payload to an isolated model session with no filesystem,
   source, ordinary-arm result, or reference-verdict access. The translator must
   list assumptions, quantifiers, domains and conclusions literally. A fresh
   session for the ordinary arm receives only its ordinary payload.
3. `seal-translation` validates the returned request hash, exact model, session
   identifier, model configuration and measured usage. It creates a sealed response and only then
   generates the assisted review payload containing source, Lean and translation.
   Neither file can be overwritten through the helper. Give this payload to a
   third fresh session, with the same reviewer instruction as the ordinary arm.
4. The assisted reviewer receives the **remaining** token/time allowance after
   translation. Its total charge includes translation plus review. The ordinary
   arm gets the same total cap. Do not grant extra retries to either arm.
5. Independently adjudicate the pinned source/Lean pair without revealing either
   arm's verdict or translation. Keep adjudications outside all reviewer inputs.
   Collect final response records, then run `score`.

Session identities, usage reports and human-independence attestations are recorded
claims. The helper checks consistency and separation of identifiers; it cannot
prove that a provider honored isolation, that a human was independent, or that
usage was measured honestly. Enforce isolation in the execution harness and
retain provider receipts. Filesystem permissions are an operator responsibility;
the tool does not sandbox sessions. Hashes detect changes relative to submitted
bindings; they are not signatures or tamper-proof storage.

## Commands and records

Install the package or run the helper directly from the repository root:

```powershell
python tools/review_comparison_pilot.py prepare --manifest <manifest.json> --output <new-run-directory>
python tools/review_comparison_pilot.py seal-translation --manifest <manifest.json> --prepared <run-directory> --task case01 --response <translation-response.json>
python tools/review_comparison_pilot.py score --manifest <manifest.json> --prepared <run-directory> --results <results.json> --adjudications <adjudications.json> --output <new-report.json>
```

Request hashes use SHA-256 of UTF-8 canonical JSON with sorted keys, no whitespace,
and unescaped Unicode (`digest()` in the implementation). Input-file hashes use
exact bytes; the example directory pins LF line endings. `subject_sha256` binds
the source and Lean hashes; the review request also binds the entire manifest.
Result files and adjudication arrays are hashed into the score report.

A translation response is one JSON object:

```json
{
  "request_sha256": "<digest of translate.request.json>",
  "model": "<exact manifest model>",
  "model_config": {},
  "session_id": "case01-translation-session",
  "text": "<literal translation>",
  "usage": {
    "input_tokens": 1000,
    "output_tokens": 300,
    "elapsed_seconds": 12.5,
    "cost_usd": 0.01
  }
}
```

Each final review record belongs in a JSON array. The allowed arms are `ordinary`
and `reverse_translation`; allowed verdicts are `pass`, `fail`, and `abstain`:

```json
{
  "task_id": "case01",
  "arm": "ordinary",
  "request_sha256": "<digest of this arm's request>",
  "subject_sha256": "<copied from this arm's request>",
  "model": "<exact manifest model>",
  "model_config": {},
  "session_id": "case01-ordinary-session",
  "verdict": "abstain",
  "rationale": "<specific reason and supporting declarations>",
  "usage": {
    "input_tokens": 1000,
    "output_tokens": 300,
    "elapsed_seconds": 12.5,
    "cost_usd": 0.01
  }
}
```

Measure all provider input/output tokens, including translation overhead in the
assisted arm. Use the same elapsed-time measurement convention for both arms;
sum translation and review durations. Report actual provider charges with a
retained pricing/receipt record, not the illustrative values above. If the local
CLI reports tokens but no dollar charge, use `"cost_usd": null` for unknown cost;
totals and differences involving unknown cost stay null, never zero. Missing token/time usage,
nonfinite or negative numbers, noninteger token counts, model differences and
exceeded budgets invalidate a record. Budget exhaustion should produce an
`abstain` record within the cap when possible; a missing or over-budget response
is reported separately, not silently converted to a fidelity verdict.

Adjudications are a separate JSON array. Allowed provenance is limited to
`synthetic_test_only` and `independent_human`. Pending records need only task,
subject hash, provenance and `"verdict": "pending"`. A completed human record is:

```json
{
  "task_id": "case01",
  "subject_sha256": "<pinned subject hash>",
  "provenance": "independent_human",
  "verdict": "fail",
  "adjudicator_id": "<independent human identity>",
  "independent_of_review_arms": true,
  "blinded_to_arm_results": true,
  "rationale": "<independent assessment of exact source and declaration>",
  "evidence_ref": "<retained adjudication note>"
}
```

Reference `pass` means faithful to the source under the fixed review scope;
`fail` means a source mismatch under that scope. If humans cannot resolve the
case, keep `pending`; do not use the model's vote to resolve it. A synthetic label
exists solely to test branches of the scorer, even when its assigned value seems
obvious. It is never promoted to human truth.

## Scoring and stopping

The score report explicitly lists missing, duplicate and invalid records,
unpaired tasks and unresolved adjudications. Every copy of a duplicate task/arm
is excluded; the scorer never chooses the favorable or latest copy. Duplicate
adjudications are also excluded. Altered input files reject the run; altered
prepared requests or translations invalidate the affected arm. Both arms must
be valid to enter a paired comparison. Review sessions and translators must have
globally distinct identifiers across all tasks; reuse excludes every associated
pair. A human adjudicator identifier cannot overlap any of those sessions.
`valid_review_records` counts only records finally admitted to valid pairs,
including pairs still awaiting truth.

Process totals include paired valid responses even while adjudication is pending.
Quality counts are reported separately by provenance, with the number of
reference-pass and reference-fail cases, paired verdict transitions, false accepts
(review PASS on reference FAIL), false rejects (review FAIL on reference PASS),
abstentions, and correct decisive reviews. Translation usage is included in the
assisted arm. Differences are descriptive counts/costs, without significance
claims, extrapolation, or pooling synthetic labels with human adjudications.
No accuracy is computed for unadjudicated tasks.

QA exits nonzero when issues are present, while preserving a report of exclusions.
Pending adjudication alone is not a malformed record. Stop this pilot after the
preregistered task set; publish missingness and unresolved cases alongside usable
pairs. Decide whether a larger experiment is justified only after independent
adjudication and inspection of the paired errors and cost. Do not interpret the
synthetic demo or a count of later recorded PASS verdicts as evidence of gain.

## Optional local CLI feasibility run

`tools/run_codex_review_pilot.py` can execute exactly two tasks through an already
authenticated local Codex CLI. Select the model and reasoning effort explicitly
from the operator's existing settings; the runner does not inspect credentials,
change models automatically, or install an API dependency.

```powershell
python tools/run_codex_review_pilot.py --manifest examples/review-comparison-pilot/manifest.json --output <new-private-run-directory> --model <configured-model> --reasoning-effort <configured-effort>
```

The runner copies and freezes input hashes, fixes a 100,000 input-token / 8,000
output-token / 300-second budget per arm, and preregisters counterbalanced order.
It uses at most six fresh CLI calls in two parallel task chains. Every call has
an empty temporary working directory, ephemeral session, ignored user config,
disabled project instructions/host skill discovery, disabled tool features and
web search, and a schema-bound final response. Only its current request payload
is supplied on stdin. A failed stage is retained without retry; its dependent
assisted stage may be skipped. There is no automatic human adjudication.

Raw JSONL events, stderr, exact invocations and provider usage are retained in
the private run directory. The real `thread.started` identity and
`turn.completed` token receipt supply each response record; dollar charges stay
unknown when the CLI does not report them. Any observed tool/non-message item
excludes its entire pair. Two explicitly recognized pre-turn CLI startup
diagnostics (disabled code-mode host and experimental host-skill-discovery
setting) are retained as diagnostics rather than counted as tool calls. Unknown
items or the same error messages after turn start remain ineligible. The audit
cannot attest stronger isolation than the configured CLI and observed events.
Token limits are checked against returned provider usage; wall-time limits
terminate the local process. Unknown cost does not invalidate a token/time
measurement.

Paired agreement, abstention and resource use can be reported while human truth
is pending. Agreement does not establish correctness or incremental benefit.
The two deliberately small public examples support a workflow feasibility
check only. The CLI's structured events and isolated-config options follow the
[official non-interactive-mode documentation](https://learn.chatgpt.com/docs/non-interactive-mode).

### Observed feasibility run: 2026-09-05

The [public process report](../examples/review-comparison-pilot/live-feasibility-20260905.json)
records six actual `gpt-6-astra` calls with `ultra` reasoning, using the operator's
existing model settings. Each stage used a distinct provider session. No tool
calls were observed. Both tasks produced valid paired responses; the reported
verdicts were `pass → pass` and `fail → fail`. Human labels remain pending.

| Two-task totals | Ordinary review | Translation plus assisted review |
|---|---:|---:|
| Provider input tokens | 25,074 | 50,188 |
| Provider output tokens | 590 | 1,957 |
| Sum of stage wall time | 40.69 s | 118.48 s |
| Reported dollar charge | Unknown | Unknown |

The assisted workflow consumed more measured resources and did not change either
verdict in this run. The inputs are deliberately small public examples, so this
observation cannot establish a general quality or cost-effectiveness result.

The first parser incorrectly treated two expected CLI startup warnings as tool
events. Its regression was fixed and the four already-produced provider receipts
were reprocessed without repeating those model calls. Only the two previously
unrun assisted stages were then executed, preserving the six-call limit. The
second task consequently ran ordinary review before assisted review, deviating
from the counterbalanced order. Original and corrected audits are retained;
the public report discloses the deviation. This supports workflow feasibility,
not a controlled comparison of incremental benefit.
