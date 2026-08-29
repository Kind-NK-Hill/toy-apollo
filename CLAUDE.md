# CLAUDE.md

Read in this order:

1. Before ToyApollo coding, Phase 2, review, proof-status, or packaging-claim work, explicitly read [AGENTS.md](AGENTS.md) first unless it is already loaded in this session. Do not `@import` it here because it contains nested rule imports and should be used with progressive disclosure.
2. For any phase behavior or routing question, read [.claude/rules/10-phase-runtime.md](.claude/rules/10-phase-runtime.md).
3. For proof-status, evidence hierarchy, review verdicts, ledger meaning, and completion claims, follow [AGENTS.md](AGENTS.md) plus the relevant `docs/phase2/*` contract. Do not restate those rules here.
4. Before editing inside a subtree, read the nearest folder-level `AGENTS.md`.

Do:

- Keep `run_chapter.py` and current CLI mode names stable.
- Treat active code and `.claude/rules/*` as truth over archive notes.
- Use phase2 modes for prompt-pack formalization, build gating, and operator review.
- Use `--phase 2 --phase2-mode soft-pack/soft-apply` for Problem soft-import selection.
- Treat legacy provider/offload/harvest notes as history, not active workflow.
- Keep runtime artifacts and secrets out of source-control changes unless the task explicitly requires them.
- Treat archived AI packaging/evidence material under `reports/_archive_*` (including the packaging bridge, evidence-mining, and case-card archives) as historical scratch, not active project evidence or packaging guidance. Do not use it as a positive source unless the user explicitly asks to audit that archive or a current non-archive artifact independently revalidates the claim.
- For current CS329/CS329T notes, prompt handoffs, or claim-mapping documents outside the archive, treat requests to review, critique, or improve the document as read-only artifact critique by default, not as Phase 2 Lean proof work.
- In artifact critique, lead with findings and minimal fixes. Do not generate evidence cards, portfolio text, resume bullets, or new Lean proofs unless the user explicitly asks for those outputs.
- If a `strict-critic` subagent is available, use it for concrete packaging artifacts; if it is unavailable, continue in the main agent with the same findings-first rules.

Do not:

- Route phase work from memory without checking `10-phase-runtime.md`.
- Describe `soft-apply` as external provider execution, execution-batch generation, or Lean verification.
- Use `--phase 3 --phase3-mode ...` or removed Phase 3 mode names such as `plan-batches`, `offload-batch`, `repair-pack`, or `repair-verify`.
- Treat phase4 as an active automated path while the CLI branch is disabled.
- Skip folder-level `AGENTS.md` when working inside `src/`, `docs/`, `plans/`, `tests/`, or `tools/`.
