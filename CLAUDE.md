# CLAUDE.md

Read in this order:

1. Use [AGENTS.md](AGENTS.md) as the canonical root contract.
2. For any phase behavior or routing question, read [.claude/rules/10-phase-runtime.md](.claude/rules/10-phase-runtime.md).
3. Before editing inside a subtree, read the nearest folder-level `AGENTS.md`.

Do:

- Keep `run_chapter.py` and current CLI mode names stable.
- Treat active code and `.claude/rules/*` as truth over archive notes.
- Use phase2 modes for prompt-pack formalization, build gating, and operator review.
- Use `--phase 2 --phase2-mode soft-pack/soft-apply` for Problem soft-import selection.
- Treat legacy provider/offload/harvest notes as history, not active workflow.
- Keep runtime artifacts and secrets out of source-control changes unless the task explicitly requires them.

Do not:

- Route phase work from memory without checking `10-phase-runtime.md`.
- Describe `soft-apply` as external provider execution, execution-batch generation, or Lean verification.
- Use `--phase 3 --phase3-mode ...` or removed Phase 3 mode names such as `plan-batches`, `offload-batch`, `repair-pack`, or `repair-verify`.
- Treat phase4 as an active automated path while the CLI branch is disabled.
- Skip folder-level `AGENTS.md` when working inside `src/`, `docs/`, `plans/`, `tests/`, or `tools/`.
