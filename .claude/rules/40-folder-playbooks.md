# Folder Playbooks

Read the nearest folder-level `AGENTS.md` before changing files there.

Current folder playbooks:

- `src/AGENTS.md`
- `src/toy_apollo/AGENTS.md`
- `docs/AGENTS.md`
- `plans/AGENTS.md`
- `tests/AGENTS.md`
- `tools/AGENTS.md`

## Intended Use

- Root `AGENTS.md`: global contract only
- `.claude/rules/*`: cross-cutting details
- Folder `AGENTS.md`: local editing guidance

Folder-level `AGENTS.md` files cannot override the root/rules no-delete boundary. If local guidance conflicts with protected-state policy, follow the root contract and `.claude/rules/*`.

Before touching ledger files, prompt packs, `.claude/worktrees/`, or `dependency_decisions/`, read:

- `.claude/rules/00-repo-boundary.md`
- `.claude/rules/20-artifacts-and-ledger.md`

Keep each folder playbook short and local to that subtree.
