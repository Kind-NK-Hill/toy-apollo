# Workspace Structure

## Active Repository (Reorg)

- Path: `D:\Grad_Study\Practimum\toy_apollo_archive\_migration_20260330_211429\toy-apollo`
- Branch: `reorg`
- Remote: `Kind-NK-Hill/toy-apollo`
- Purpose: clean source-first structure and future development.

## Legacy Repository (Frozen Parallel)

- Path: `D:\Grad_Study\Practimum\toy_apollo_archive`
- Active branch: `master` (dirty historical workspace)
- Frozen pointer branch: `legacy_parallel_20260330`
- Purpose: preserve previous local state for rollback/reference.

## Working Rule

- New changes go to the active reorg repository.
- Legacy repository stays untouched except explicit migration or recovery tasks.
