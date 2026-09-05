# Development

A public checkout supports Python development, Lean corpus builds, case
inspection, and a complete isolated workflow demonstration. The owner's source
corpus, task plans, catalog policy and operational SQLite database are not needed
for those checks and are not distributed in the release.

## Set up

Use Python 3.11 or newer (`pyproject.toml`); CI runs Python 3.12 on Ubuntu.
Install Git, [Elan](https://github.com/leanprover/elan) for the version in
`lean-toolchain`, and [ripgrep](https://github.com/BurntSushi/ripgrep) for repository
surface tests. Windows PowerShell commands are shown below:

```powershell
git clone https://github.com/Kind-NK-Hill/ProbabilityTheoryFormalization.git
Set-Location .\ProbabilityTheoryFormalization
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
python -m pip install --editable .
lake exe cache get
formalize -h
formalize --status
```

On Linux/macOS, activate the environment with `source .venv/bin/activate`.
Use the committed `lake-manifest.json` and `lean-toolchain`; `lake update` is for
intentional dependency updates or initialization when dependencies have not yet
been resolved. Python dependencies are not fully locked, and the declared minimum
version is not a claim of a complete platform/version test matrix.

Optional semantic indexing/retrieval needs the additional components in
`requirements.txt`; install them with `python -m pip install -e ".[retrieval]"`
(or `python -m pip install -r requirements.txt`). Core prompt packs and the
workflow demonstration do not require those retrieval dependencies.

## Run the complete demonstration

```powershell
python tools/run_workflow_demo.py
```

This runs production pack/build/review/apply code, real Lean builds, a rejected
stale review, and an isolated SQLite database. It preserves its generated evidence
directory. Default reviews are recorded teaching opinions, explicitly distinct
from newly executed model reviews. See [workflow_demo.md](workflow_demo.md) for
the external-reviewer adapter, provenance, and expected outputs.

## Verify the public release

From an unmodified public release checkout:

```powershell
python tools/check_public_release.py
python tools/check_formal_corpus.py --publication-map data/publication/corpus_map.json
python tools/prepare_public_snapshot.py
python tools/check_case_studies.py
python tools/check_repo_hygiene.py
$env:LEAN_NUM_THREADS = "1"
lake build ProbabilityTheory
python tools/check_chapter_imports.py
python -m unittest discover -s tests -p "test_*.py" -v
```

The thread limit matches CI and bounds peak memory during the corpus build. On
Linux/macOS, use `export LEAN_NUM_THREADS=1` before the build. Increase it only
when the machine has sufficient memory for concurrent Lean processes.

The release check compares the published file inventory and normalized UTF-8/LF
fingerprints. It is expected to detect local edits; it does not grant semantic
review authority. Publication mappings are generated from committed source by
the maintainer, not edited to hide a mismatch.

The library build covers all corpus modules and their dependencies. Chapter
joint-import checks are separate: chapters 1 and 7 retain the Kenneth/Mathlib
`Partition` boundary. The Python suite includes the Lean definition-interface
contract; use its normal discovery runner so the contract is actually executed.
Tests requiring omitted private evidence explicitly skip in the public checkout.

For a focused change:

```powershell
python -m unittest tests.test_settings
lake build ProbabilityTheory.chapter_08.def_8_5
```

Compile the preserved historical slices independently:

```powershell
Get-ChildItem .\examples\case-studies -Recurse -Filter *.lean | ForEach-Object {
    lake env lean $_.FullName
    if ($LASTEXITCODE -ne 0) { throw "case snapshot failed: $($_.FullName)" }
}
```

Both rejected and accepted historical slices can compile; the accompanying
timeline explains the semantic distinction.

## Operate a complete private workspace

Corpus completion and normal textbook generation require the operator's source
units, plans, catalog policy, source/evidence roots and compatible state. The
public build manifest deliberately contains only `basename`, `file_path`,
`module_name`, `chapter` and `sha256`; it cannot replace that catalog.

If those materials are available, configure the roots explicitly:

```powershell
$env:FORMALIZATION_ENGINE_RUNTIME_ROOT = "C:\work\ProbabilityTheoryFormalization"
$env:FORMALIZATION_ENGINE_ARTIFACT_ROOT = "C:\work\ProbabilityTheoryFormalization-artifacts"
formalize --status
formalize state validate --json
```

`--status` reports the current process's roots without writing state. The catalog
validation command belongs to this complete workspace, not the public-clone
quick start. `status <task>` and `worklist` refresh repository/GitHub observations
by default; they do not commit, push, open or merge PRs. See
[workspace_state.md](workspace_state.md) and [the Chinese operator guide](getting_started.zh-CN.md).

## Before a pull request

Describe the changed behavior and evidence boundary, run checks proportional to
the change, and preserve unrelated work. A changed canonical mathematical task
still needs the project's independent review/apply process; compiling it does
not establish source fidelity.

Keep complete inputs/plans, catalog policy, upstream snapshots, operational
databases, live packs, logs and receipts outside public commits. New examples
need appropriate publication rights, bounded source descriptions, and honest
AI-assistance attribution. Do not run the source sanitizer with `--apply` against
the private canonical corpus; the release exporter transforms only its output.

See [CONTRIBUTING.md](../CONTRIBUTING.md) and
[repository_scope.md](repository_scope.md) for the release/export boundary.
