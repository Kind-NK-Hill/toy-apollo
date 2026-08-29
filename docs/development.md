# Development

This guide takes a fresh source checkout to a focused, verified development
state. The complete private source corpus and runtime evidence are optional and
are not required for CLI help, hygiene checks, Lean output builds, or public
case-study inspection.

## Prerequisites

- Python 3.12 is the currently verified environment. The repository has not
  yet declared a minimum supported Python version.
- [Elan](https://github.com/leanprover/elan) for the Lean version pinned by
  `lean-toolchain`.
- Git.

Windows PowerShell is the currently documented shell. The Python and Lean code
are not intentionally Windows-only, but a complete cross-platform CI matrix is
not yet present.

## Set up

```powershell
git clone https://github.com/Kind-NK-Hill/toy-apollo.git
Set-Location .\toy-apollo

python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
pip install -r requirements.txt

lake update
lake exe cache get
python .\run_chapter.py -h
```

`requirements.txt` is currently unpinned. Reproducible dependency locking is a
known follow-up, not an existing guarantee.

## Focused verification

Run the smallest check that covers the changed Interface:

```powershell
# CLI import and command surface
python .\run_chapter.py -h

# Tracked-artifact policy
python .\tools\check_repo_hygiene.py

# Fail-closed Task Parent source-excerpt policy
python .\tools\prepare_public_snapshot.py

# Public case catalog, timeline, and diversity policy
python .\tools\check_case_studies.py

# One Python test Module
python -m unittest tests.test_settings

# One Lean Task Parent
lake build ToyApollo.Output.def_8_5

# All public case snapshots
Get-ChildItem .\examples\case-studies -Directory | ForEach-Object {
    lake env lean (Join-Path $_.FullName 'initial.lean')
    if ($LASTEXITCODE -ne 0) { throw "initial snapshot failed: $($_.Name)" }
    lake env lean (Join-Path $_.FullName 'final.lean')
    if ($LASTEXITCODE -ne 0) { throw "final snapshot failed: $($_.Name)" }
}
```

For a broader Python run:

```powershell
python -m unittest discover -s tests -p "test_*.py"
```

In a public checkout, tests whose authority is the omitted private evidence
plane report explicit skips instead of silently fabricating fixtures. The
source-only runtime, state, review, publication-boundary, and hygiene tests
still run normally; each skip names the missing private evidence class.

The repository does not yet have a single command combining formatter, lint,
type, Python test, Lean build, and documentation checks. Do not describe that
gate as present until it is implemented.

## Local evidence plane

To operate against a private runtime/evidence checkout, point ToyApollo at the
two roots without changing the CLI:

```powershell
$env:TOY_APOLLO_RUNTIME_ROOT="D:\path\to\toy-apollo"
$env:TOY_APOLLO_ARTIFACT_ROOT="D:\path\to\toy-apollo-artifacts"
python .\run_chapter.py --status
```

`--status` is read-only and describes roots resolved for that process. The
artifact root owns the operational SQLite database.

Do not commit:

- source-derived `inputs/` or `plans/` corpora;
- prompt packs;
- SQLite databases or ledger snapshots;
- logs, batch queues, receipts, or generated reports;
- `.env` files, tokens, or credentials.

When a runtime history is worth showing publicly, export a sanitized immutable
case under `examples/case-studies/` and retain the full original privately.

## Formatting

`.editorconfig` and `.gitattributes` establish UTF-8/LF source conventions.
Do not run a repository-wide normalization over unrelated work. Format only
the files in scope until a dedicated formatter/linter gate is adopted.

## Phase 2 changes

Before changing Phase 2 review, apply, status, or batch behavior, read:

- [`phase2/README.md`](phase2/README.md)
- [`phase2/workflow.md`](phase2/workflow.md)
- [`phase2/status_contract.md`](phase2/status_contract.md)
- [`phase2/review_criteria.md`](phase2/review_criteria.md)
- [`phase2/artifacts.md`](phase2/artifacts.md)

Build success, review success, and applied completion must remain separate
claims.

## Pull requests

Before opening a pull request:

1. explain the changed Interface and its authority implications;
2. run focused Python and Lean checks;
3. show that no generated corpus or local path entered the diff;
4. run `python tools/prepare_public_snapshot.py` after changing Lean outputs;
5. document any AI-assisted code or review artifact accurately;
6. include source-rights information for new examples.

See [`../CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution policy.
