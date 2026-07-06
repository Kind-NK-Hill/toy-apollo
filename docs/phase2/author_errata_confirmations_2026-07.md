# Author Errata Confirmations — 2026-07

Record of textbook-author responses to the two Chapter-1 source-statement
exceptions our Phase 2 semantic review flagged. This is a **record-only** update:
the two tasks are **not** re-run and their `phase2_status` stays
`allowed_exception`. The Lean files remain the exception snapshots. What changed
is only the *reason* attached to each exception — the author has now
addressed the underlying source issue.

Author: Kenneth Shum (textbook author). Channel: direct correspondence, 2026-07.

## `ex_1_3_2` — Example 1.3.2 — source typo, CORRECTED by author

- **Our exception:** `source_typo_statement_exception` (recorded 2026-06-22).
  Review could not produce a source-faithful completion because the displayed
  α₂ / mixed-type continuous part did not decompose the CDF as printed —
  flagged as an "α₂ convention / prefactor" mismatch.
- **Author action:** issued a **written erratum** stating that α₂(x) for x in
  [−1.5, 1.5] equals ∫_{−1.5}^x e^{−t²/2}/√(2π) dt, i.e. the standard normal CDF
  (with the 1/√(2π) prefactor).
- **Assessment:** direct match. The pipeline's source-fidelity review
  independently flagged the exact function the author's erratum corrects. This is
  the strongest form of resolution — a published correction.
- **Status:** exception preserved as the finding; source issue **corrected** by
  author. Not re-run.

## `thm_1_2` — Theorem 1.2(4) — missing hypothesis, ACKNOWLEDGED by author

- **Our exception:** `source_statement_exception`. The interval-additivity
  clause `f ∈ R(α; [a,c]) and f ∈ R(α; [c,b]) ⟹ f ∈ R(α; [a,b])` is unsafe under
  the book's mesh-limit definition when α and f share a jump at the split point
  c. See [`rs_stieltjes_boundary.md`](rs_stieltjes_boundary.md) §"Theorem 1.2(4)
  Impact Boundary".
- **Evidence sent to author:** a counterexample note (α, f both stepping at
  c = 1 on [0,2]: both halves RS-integrable, whole not) plus two repair options.
- **Author action:** **acknowledged** in correspondence that the counterexample
  is valid and that part (4) is missing an assumption. No written erratum yet.
- **Resolution direction:** **Option A** — retain the mesh-limit definition and
  add a split-point compatibility hypothesis (α continuous at c, *or* f
  continuous at c; more generally the crossing-cell oscillation condition). This
  is inferred from the author's "missing assumption" wording; an explicit
  Option A vs Option B (redefine integrability à la Darboux/Rudin) confirmation
  and a formal erratum are still pending.
- **Status:** exception preserved as the finding; source issue
  **acknowledged**, formal correction pending. Not re-run.

## Net exception surface after this record

Four recorded exceptions, now in two honest tiers:

- **Author-addressed (Chapter-1 source-statement issues our review flagged):**
  `ex_1_3_2` (corrected), `thm_1_2` (acknowledged, erratum pending).
- **Structural scope boundaries (not source errors, not author-fixable):**
  `thm_11_8` (proof cites a result external to the book),
  `thm_14_8` (statement beyond the book's scope).

Nothing here is claimed as a `pass`. Converting either Chapter-1 exception into a
pass would require editing the source `.tex` to the corrected statement and
**re-running** Phase 2 (fresh build + fresh semantic review against the new
text) — deliberately not done, to preserve the record that the review caught a
real source issue the author later confirmed.
