# Paired review protocol example

These two small source/Lean pairs are **new protocol demonstration inputs**.
They are not samples of the historical review corpus, and their pending human
adjudications are not filled from earlier reviews or from the synthetic fixture.
Both declarations are intended to compile; compilation does not supply the
source-fidelity reference verdict.

The exact model remains a fixture placeholder. Copy this directory outside the
repository, choose a pinned model and budgets, and preregister the task set before
starting any prospective model runs. Do not report these deliberately small,
public demonstration inputs as a representative benchmark.

Run the deterministic scoring demonstration from the repository root:

```powershell
python examples/review-comparison-pilot/run_synthetic_fixture.py
python -m unittest tests.test_review_comparison_pilot -v
```

The demonstration fabricates translation text, model usage, reviews, and reference
labels **only to exercise the scorer**. It uses a temporary directory, makes no
model calls, reports the `synthetic_test_only` group, and leaves empirical status
pending. Never copy those fabricated labels into `adjudications.pending.json`.

Prepare isolated request payloads without invoking a model:

```powershell
python tools/review_comparison_pilot.py prepare --manifest examples/review-comparison-pilot/manifest.json --output ../ProbabilityTheoryFormalization-artifacts/review-comparison-demo-v1
```

The output directory must not already exist. An empty response array can be
scored against pending adjudications; it explicitly reports missing reviews and
returns a nonzero QA exit code. It does not infer that a model failed the task:

```powershell
python tools/review_comparison_pilot.py score --manifest examples/review-comparison-pilot/manifest.json --prepared ../ProbabilityTheoryFormalization-artifacts/review-comparison-demo-v1 --results examples/review-comparison-pilot/results.pending.json --adjudications examples/review-comparison-pilot/adjudications.pending.json
```

See the [protocol and response schemas](../../docs/review_comparison_pilot.md)
before collecting actual model responses or independent human adjudications.

A [two-task live process report](live-feasibility-20260905.json) records six actual
model calls on 2026-09-05. Both arms agreed on both tasks; the assisted arm used
more tokens and time. Dollar charges and independent human truth remain unknown.
The report includes the runner-recovery and order deviation, so it is a
feasibility observation rather than a controlled quality comparison. See the
[run interpretation](../../docs/review_comparison_pilot.md#observed-feasibility-run-2026-09-05).
