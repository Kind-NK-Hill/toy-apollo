# Contributing to ToyApollo

ToyApollo welcomes focused improvements to its Lean formalization Modules,
local agent workflow, evidence handling, tests, and documentation.

## Before starting

Open an issue before changing a stable CLI flag, status name, plan schema,
review schema, repository layout, or source/evidence classification. These are
Interfaces used by runtime state and historical evidence; seemingly local
changes may invalidate existing receipts.

Small fixes, tests, and documentation corrections can go directly to a pull
request.

## Set up and verify

Follow [`docs/development.md`](docs/development.md). Start with the narrowest
check that exercises the changed Interface, then add broader checks when the
risk justifies them.

At minimum, source-facing changes should normally run:

```powershell
python .\run_chapter.py -h
python .\tools\check_repo_hygiene.py
python .\tools\prepare_public_snapshot.py
python -m unittest <relevant-test-module>
```

Lean-facing changes should additionally build each touched Task Parent:

```powershell
lake build ToyApollo.Output.<task_id>
```

A Lean build is not evidence of source fidelity. Changes to an official task
still require the Phase 2 review/apply contract used by the project owner.

## Keep the public source plane small

Do not commit complete source corpora, plans, prompt packs, operational
databases, logs, batch state, receipts, or generated reports. Preserve those in
the private evidence plane.

A new public case study must satisfy
[`docs/repository_scope.md`](docs/repository_scope.md): minimal scope,
path-relative files, source-rights review, evidence hashes, and an explicit
statement that a selected case is not benchmark evidence.

## Code and documentation

- Put new Python Implementation under `src/toy_apollo/`.
- Treat root-level `src/*.py` as active legacy compatibility code until its
  callers have migrated.
- Keep CLI, tests, and callers on the same Seam.
- Prefer a deep Module with a narrow Interface over pass-through Modules.
- Use the domain terms in [`CONTEXT.md`](CONTEXT.md).
- Match documentation to current runtime behavior, not intended future work.
- Preserve unrelated working-tree changes.

## Provenance and authorship

- Do not submit source material unless you have the right to publish it.
- Do not describe AI-generated Lean, prose, or review evidence as handwritten.
- In the pull request, state material model-assisted generation or review and
  explain what a human verified.
- Never fabricate benchmark results, task counts, costs, review outcomes, or
  completion status.

## Security and privacy

Never commit API keys, tokens, `.env` files, local absolute paths, personal
information, or private source text. Follow [`SECURITY.md`](SECURITY.md) for
responsible vulnerability reporting.
