# Reproduce the complete workflow

The [teaching fixture](../examples/workflow-demo/) runs the **production** Python
pack, Lean build, review request, review-result validation, freshness check, and
apply functions against a new, isolated runtime and SQLite database. Compilation
is real. The default semantic opinions are recorded teaching reviews.

The fixture is newly authored, outside the 452-task textbook catalog. It uses
Lean's standard library to avoid downloading Mathlib for a tiny example. It
defines a rounded per-thousand frequency on valid counts. This is an interface
example, not a new probability theorem or an accuracy benchmark.

## Run

From a checkout with the pinned Lean toolchain available:

```console
python -m pip install -e .
lake update
python tools/run_workflow_demo.py
```

`lake update` prepares the repository's configured dependencies and may need
network access. If dependencies are already present, omit it. The demo itself
copies the small REPL package into its new temporary runtime, builds that copy,
and uses no external model or network service in replay mode. `--repl-source`
can select an already downloaded compatible REPL package.

The printed evidence directory is preserved. To choose its location, use
`--output <new-directory>`; existing paths are refused. No automatic cleanup,
shared live state, production source plans, or corpus writes are involved.

## What actually runs

1. `write_prompt_pack` prepares source and task context in isolated artifacts.
2. `build_check_prompt_pack_candidate` accepts the initial Lean definition and
   its caller, even though the definition omits its specified domain conditions.
3. `run_codex_review_now` prepares the bound review request. A recorded failing
   opinion is replayed; `apply_codex_review_result_once` records the failure and
   leaves the isolated canonical output absent.
4. The source mismatch triggers the existing mathematical route gate. The
   independently reviewed source-and-repair skeleton, with three explicit
   review rounds, is replayed before authoring can continue. This is a recorded
   teaching `go`, not a new review or catalog approval.
5. The interface-only repair adds the conditions. The **real Lean build fails**
   because the old caller supplies too few arguments.
6. The complete repair supplies the caller's conditions. It builds and receives
   a passing teaching opinion.
7. A newly built candidate intentionally reintroduces the old interface. The
   previously passing review is rejected by the production freshness gate.
   Existing candidate and review receipts are preserved.
8. The complete repair is rebuilt and gets a newly bound review request. Only
   its corresponding result reaches the production apply gate, which builds
   and writes the isolated canonical file.

The caller is a declaration in the same Lean file. This deliberately small
example demonstrates call-interface migration, not an atomic transaction across
multiple catalog tasks. The original public historical cases remain separate.

Inspect `summary.json`, `events.json`, `evidence-sha256.json`, and the versioned
files under `artifacts/phase2_prompt_packs/def_demo_frequency/`. The SQLite status
belongs to this isolated teaching run; it says nothing about catalog completion.
The evidence manifest hashes the inputs, review/build receipts, and landed code.
Absolute paths, timestamps, platform line endings, and run-specific hashes vary.
The final Lean text (normalized to LF) and sequence of outcomes are reproducible.
The script also checks that the landed bytes equal the exact candidate snapshot
reviewed within that run, and reports both raw-byte and normalized-text hashes.

## Replay provenance

`teaching-review.json` preserves the separately performed review of the fixed
source and code, including the original reviewer identity and exact file hashes.
The replay refuses code or source that differs from those fixed inputs.
`math-review.json` separately records the three-round review of
`math-proof-skeleton.md`, including exact source/skeleton hashes. Those three
rounds do not represent three independent reviewers or statistical samples.

The demo mechanically fills a **simulated protocol envelope** with each new
temporary request's hashes and evidence fields. Every replay result states that
no reviewer inspected that new runtime. The independence-shaped schema fields
inside that envelope demonstrate the gate protocol; they are not a fresh
independence attestation. Rebinding cannot convert a recorded opinion into new
mathematical authority, and these results must never be imported into the live
catalog. No runtime acceptance rule is weakened for this example.

## Run a fresh external review

Use an existing independent reviewer runner. This script starts no new service
and assumes no provider. Its command is supplied as an argument array, without a
shell. For example, adapt the paths and arguments to your actual runner:

```console
python tools/run_workflow_demo.py --reviewer-id your-real-reviewer --model your-actual-model --reviewer-argv-json '["python", "/absolute/path/reviewer.py", "--input", "{input}", "--prompt", "{prompt}", "--result", "{result}"]'
```

Quote the JSON string according to your shell. Supported substitutions are
`{request}`, `{input}`, `{prompt}`, `{result}`, and `{run_metadata}`. The runner
is invoked for three semantic reviews and one mathematical route review.
The latter request contains `review_kind: math_route`, source and skeleton
paths/hashes, and its separate result template; it requires three explicit
rounds and a `go` before repair. The reviewer should read
the source, exact candidate, caller, and bound evidence, then fill the generated
result template according to the current prompt. It must truthfully provide its
independence attestation. The demo does not fill or overwrite the live verdict,
review identity, source assessment, or hash binding.

The runner may write only the expected result and optional `run_metadata` JSON.
It can report cost and token usage in that metadata; unreported values remain
unavailable. The demo records request/result hashes, a run identifier, supplied
reviewer identity/model, elapsed time, exit status, and raw runner metadata.
It hashes other run files before and after invocation and refuses apply after
a persisted input change. This detects changes; it is **not an operating-system
sandbox**. Configure the actual reviewer tool with read-only access.

If a reviewer disagrees with the expected teaching verdict, returns an invalid
result, times out, or changes inputs, the demo stops and preserves its evidence.
It never falls back from a failed real review to a passing replay.
