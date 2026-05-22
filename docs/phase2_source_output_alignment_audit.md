# Phase 2 Source-Output Alignment Audit

Snapshot date: 2026-05-19.

Purpose: convert every accepted proof-debt gap into one of four concrete actions: import an existing theorem, write a narrow interface translation, formalize the source proof step locally, or keep only a verified external/foundation gap.

## Classification Rules

- `A_existing_theorem_candidate`: all recorded landing names resolve to theorem/lemma declarations. These are the first candidates for import/rewrite and debt retirement, but their hypotheses still need review.
- `B_partial_theorem_plus_support_interface`: at least one theorem/lemma exists, but the landing also contains definitions or structures. Use the theorem part, then formalize the remaining source step.
- `B_partial_theorem_plus_missing_or_support`: at least one theorem/lemma exists, but another recorded landing name is missing, usually a support assumption or structure field. This is not clean until the missing part is replaced.
- `C_support_predicate_or_structure_only`: the recorded landing is only a support predicate, structure, definition, or field. This is not a cleared proof; replace it by theorem-level evidence.
- `D_no_landing_search_required` / `D_landing_names_missing`: no usable local landing is recorded or found. Re-open source/output search before accepting it as real debt.

## Counts

- Total accepted debt items: 1
- B_partial_theorem_plus_support_interface: 1

## Family Counts

- clt/triangular: 1

## Manual Follow-up Notes

- `ex_13_6_5.optional_stopping_zero_gain` and `ex_13_6_5.expected_waiting_times` have theorem landings, but signature inspection shows they still carry model-specific hypotheses such as `hThirdCase`, `hInitialGainZero`, and terminal payoff integral identities. Treat them as interface/source-formalization work, not clean debt retirement.
- `prob_10_10.constant_distribution_to_probability` can import `prob_10_3`, but `prob_10_3` itself still requires `h_constant_bridge`; this is a partial source-output alignment, not a completed proof.
- `thm_10_8.quantile_law_preservation` already has the CDF-to-law bridge in `thm_10_8_quantile_law.lean`; the remaining work is the source event calculation and measurability needed to feed that bridge.

## Audit Table

| task.obligation | family | classification | existing local declarations | missing landing names | next action |
| --- | --- | --- | --- | --- | --- |
| `thm_14_8.beyond_book_proof_obligations` | clt/triangular | `B_partial_theorem_plus_support_interface` | `thm_14_8_ProofBeyondBook` (structure, `ToyApollo/Output/thm_14_8.lean:167`)<br>`thm_14_8_of_lindeberg` (theorem, `ToyApollo/Output/thm_14_8.lean:175`)<br>`thm_14_8_of_lyapunov` (theorem, `ToyApollo/Output/thm_14_8.lean:184`)<br>`thm_14_8` (theorem, `ToyApollo/Output/thm_14_8.lean:195`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |

## Immediate Queue

Start with `A_existing_theorem_candidate` and both `B_partial_*` classes, but do not mark any item proved merely because a symbol exists. The declaration must actually discharge the source obligation without carrying an equivalent support assumption.

This audit is also attached back to each accepted debt item as `source_output_alignment`, so debt-fix prompts can act on every existing gap rather than rediscovering this classification manually.
