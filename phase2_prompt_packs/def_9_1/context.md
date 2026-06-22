# Context for def_9_1

- Type: `Definition`
- Source plan: `chapter9-moments-mgf`
- Chapter: `9`
- Current ledger status: `COMPLETED`
- Pack candidate state: `draft`

## Task

### Title
Moments and Central Moments

### Content

\begin{defbox}{9.1}
For an integer $r \geq 1$, the $r$-th moment of $X$ is defined as the expectation $\mathbb{E}[X^r]$. The $r$-th central moment is defined by $\mathbb{E}[(X-\mathbb{E}[X])^r]$. In particular, the second central moment is commonly called the variance of $X$; the square root of variance is called the standard deviation.

The third central moment measures the asymmetry of the probability distribution. The skewness of a random variable is defined as the third central moment normalized by the cube of the standard deviation $\sigma$,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^3]}{\sigma^3}.
\]
The analogous quantity of order $4$ is called the kurtosis,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^4]}{\sigma^4}.
\]
It measures the tailedness of the probability distribution.
\end{defbox}

## Legacy Heuristic Notes

These notes are advisory only. Hard checks and reviewer artifacts are the promotion gates.

- Task role: `definition`
- Coverage mode: `strict_source_alignment`
- Required cues: `(none)`
- Forbidden relaxations: `(none)`
- Must not assume: `(none)`

Rules for this task:
- Examples must preserve the source construction, counterexample logic, density/distribution assumptions, and conclusion; do not reduce them to a theorem wrapper.
- Theorems must not strengthen hypotheses to erase the main textbook argument.

## Hard Dependencies

- None
## Soft Imports

- None

## Final Import Union

- None

## Latest Operation Summary

- Latest operation kind: `review-apply`
- Latest operation file: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\verify_result_v6.json`

## Build State

- Build attempts recorded: `2`
- Latest build candidate: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\candidate_v2.lean`
- Latest build-ready candidate: `(none)`
- Latest build result: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\build_result_v2.json`
- last build-ready candidate is stale
- Latest build status: `success`
- Latest primary failure kind: ``
- Latest build disposition: `build_check_passed`

## Math Review Gate

- Required: `false`
- Status: `not_required`
- Verdict: `(none)`
- Stop mode: `(none)`
- Triggers: `(none)`
- Proof skeleton: `(none)`
- Proof skeleton hash: `(none)`
- Math review result: `(none)`
- Math review result hash: `(none)`
- Gate reason: Math Review Gate is not required for this task.

## Review State

- Current review status: `review materials prepared via review-existing-queue`
- Current review origin: `review-existing-queue`
- Current review subject kind: `official_output`
- Current review input: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_input_v3.json`
- Current review prompt: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_prompt_v3.md`
- Current review context: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_context_v3.md`
- Current review template: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_result_template_v3.json`
- Current review request: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_request_v3.json`
- Current review request backend: `codex-handoff`
- Current expected review result file: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_result_v3.json`
- The completed review result below is from the previous review cycle, not the current pending pack.

- Last completed semantic review result: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\semantic_review_result.json`
- Last completed semantic verdict: `pass`
- Last completed semantic summary: `Definition 9.1 is faithfully represented: the raw moment, central moment, variance, standard deviation, skewness, and kurtosis all have direct Lean landings using Mathlib's moment and centralMoment definitions or direct algebraic combinations of them. The task has no proof-bearing source spine or task-local proof obligations, and the exported interface is adequate for the listed downstream consumers.`

## Auto-Loop State

- Current auto-loop status: `(inactive)`

## Active Repair State

- Active repair status: `(none)`

## Compatibility State

- Latest verify summary: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\verify_result_v6.json`
## Failure Summary

# Failure Summary for def_9_1

- Total runtime attempts: `6`
- Total build attempts: `2`
- Total semantic review outcomes: `4`
- Latest candidate: `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\official_snapshot_v2.lean`
- Latest semantic review verdict: `pass`
- Latest proof class: ``
- Latest task status: ``
- Latest disposition: `official_output_review_pass`
- Latest semantic summary: `Definition 9.1 is faithfully represented: the raw moment, central moment, variance, standard deviation, skewness, and kurtosis all have direct Lean landings using Mathlib's moment and centralMoment definitions or direct algebraic combinations of them. The task has no proof-bearing source spine or task-local proof obligations, and the exported interface is adequate for the listed downstream consumers.`

## Recent Attempts

- Attempt `2`: `success` / `` / `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\candidate_v2.lean`
- Attempt `2`: `semantic_review` / verdict `inconclusive` / task `` / class `` / `codex_review_invalid_no_promotion` / `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\candidate_v2.lean`
- Attempt `3`: `semantic_review` / verdict `inconclusive` / task `` / class `` / `codex_review_invalid_no_promotion` / `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\candidate_v2.lean`
- Attempt `4`: `semantic_review` / verdict `pass` / task `` / class `` / `codex_review_pass_promoted` / `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\candidate_v2.lean`
- Attempt `6`: `semantic_review` / verdict `pass` / task `` / class `` / `official_output_review_pass` / `D:\Grad_Study\Practimum\Formalization\toy-apollo\phase2_prompt_packs\def_9_1\official_snapshot_v2.lean`

## Recommended Next Action

- The latest semantic review/apply path succeeded. Use Latest task status, not verdict alone, before calling this textbook complete. If `draft.lean` changes again, rerun `build-check` before any new review.
