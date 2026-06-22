# Operator Prompt for intro_9

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
- Triggers: `semantic_fail_triage:statement_or_source_mismatch, needs_concrete_decomposition, source_mismatch`
- Proof skeleton: `(missing)`
- Math review result: `(missing)`
- Reason: Math Review Gate requires a natural language proof skeleton before Lean author/build. pre-author checklist: source statement identified; no public premise relocation; math proof skeleton reviewed go; independent semantic review after build.

## Active Semantic Repair

You are in semantic repair mode. The current goal is to remove the semantic defect identified by the failed review, not merely to make the file compile.
Treat `review_repair_request.json` and the canonical failed review artifacts as the primary repair inputs.
`failure_summary.md` and current build diagnostics remain useful, but they are secondary to the semantic defect contract.
Do not answer the failed review with a syntax-only patch if the semantic mismatch would remain.

Current repair targets:
- Must fix: The official output is a valid non-proof textual carrier shape, with no public premises, axioms, or proof debt, but it is not source-faithful enough: it only records the transform-tool/domain contrast and omits several central source claims about moments, the future MGF existence theorem, inversion/uniqueness, distribution recovery, and convergence motivation.
- Must fix: The carrier string is a strict summary of only the transform/domain contrast and omits central source claims C2, C4, C6, and C7, with C5 only partially covered.
- Must fix: No public-premise relocation, private axiom, adapter shortcut, or proof debt was found in `ToyApollo/Output/intro_9.lean`.
- Must fix: The generated `source_proof_spine` placeholder is stale for this non-proof Remark and should not be treated as source math debt.
- Must preserve: Preserve the original task statement: \section*{Moment Generating Functions and Characteristic Functions}

The moment generating function and characteristic function are both examples of transform functions used to analyze probability distributions. The moment generating function of a random variable contains all the information about its moments. However, a drawback of the moment generating function is that it may not exist in certain cases. In this chapter we will prove that the moment generating function of a random variable exists if and only if the moments of all orders are finite.

In contrast, the characteristic function of a random variable is well-defined for all types of random variables, even if the moments are not finite. The inversion formula and the uniqueness theorem state that we can recover not only the moments, but the entire probability distribution of a random variable from its characteristic function. Although the inversion formula is not frequently used to compute probability explicitly, it provides a theoretical basis for checking convergence in distribution through characteristic functions.
- Must preserve: Preserve allowed abstraction: Shared interfaces follow the textbook-first, bridge-then-Mathlib policy: define the textbook object first, prove or import a reviewed equivalence bridge, then use Mathlib through that bridge when it does not skip the source proof spine.
- Must preserve: Preserve allowed abstraction: 可以在证明内部调用 Mathlib 或已有测度论/积分论引理，但导出的 theorem/definition statement 必须忠实对应教材对象。
- Must preserve: Preserve allowed abstraction: 允许 reviewed reusable bridge / equivalence theorem + Mathlib support；禁止 adapter-only shortcut 或 task-shaped bridge 冒充教材证明。
- Forbidden shortcut: 禁止把教材中的公共接口偷换成纯存在性壳、占位定义或只记录 witness 的结构。
- Forbidden shortcut: 禁止把应当供下游复用的 theorem 改写成只够当前文件自证的 theorem-specific wrapper。

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