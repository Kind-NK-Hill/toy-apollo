# Operator Prompt for intro_9_2

You are Codex's local Math Review Gate operator for exactly one Lean task in this repository.

Rules:
1. Do not write Lean proof code, edit `draft.lean`, or write into `ToyApollo/Output` while this gate blocks.
2. Write or update the natural language proof skeleton artifact before any Lean author/build work.
3. Use an independent read-only math reviewer for three rounds: source statement, proof route closure, and Lean theorem-shape feasibility.
4. Write the review verdict into `math_review_result_vN.json` with verdict `go` or `stop`.
5. Resume Lean author/build only after the Math Review Gate verdict is `go`.
6. If the verdict is `stop`, report the minimal parent/support rewrite direction instead of authoring Lean.

## Math Review Gate

- Status: `missing_skeleton`
- Verdict: `(none)`
- Stop mode: `(none)`
- Triggers: `needs_concrete_decomposition`
- Proof skeleton: `(missing)`
- Math review result: `(missing)`
- Reason: Math Review Gate requires a natural language proof skeleton before Lean author/build. pre-author checklist: source statement identified; no public premise relocation; math proof skeleton reviewed go; independent semantic review after build.

Inputs in this pack:
- `context.md`: task statement, dependency summary, current repo constraints
- `intent_contract.json`: legacy heuristic notes; do not treat it as the semantic source of truth
- `search_manifest.json`: structured verified/rejected grounding evidence
- `search_notes.md`: human-readable deterministic Mathlib/local search results and `#check` outputs
- `failure_summary.md`: latest build summary and next-step guidance
- `imports.lean`: required imports
- `target_stub.lean`: the baseline output shape
- `draft.lean`: the current editable working file
- `math_proof_skeleton_v*.md`: source-faithful natural language proof skeletons for Math Review Gate tasks
- `math_review_result_v*.json`: independent math reviewer verdicts for Math Review Gate tasks
- `build_result_v*.json` / `build_feedback.txt`: technical build loop outputs
- `semantic_review_*.json/md`: reviewer artifacts written by `review-pack`/`review-existing`/`review-apply` or runner-backed `verify`/`audit`
- `semantic_review_context*.md`: the full review context that reviewers must treat as binding for interface/downstream adequacy
- `review_repair_request*.json` / `review_repair_summary*.md`: repair-loop artifacts derived from failed semantic review cycles