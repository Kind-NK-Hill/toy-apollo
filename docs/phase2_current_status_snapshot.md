# Phase2 Current Status Snapshot

- generated_at: `2026-06-19T02:58:47.181254Z`
- ledger: `project_ledger.json`
- ledger_sha256: `4ca96aeb49ffa5717ba4b9ff37e4dde953d0efecc20b2deafdd396c4b14dfad5`
- ledger_size_bytes: `3270898`
- tasks: `396`
- symbols: `3647`
- legacy_obligation_tasks: `0`
- legacy_obligation_symbol_owners: `0`

This report is audit context only. It does not replace `review-apply` or declare completion.

## Status Counts

- `COMPLETED`: 344
- `COMPLETED_WITH_PROOF_DEBT`: 1
- `DISCOVERED`: 47
- `PACKED`: 4

## Phase2 Status Counts

- `allowed_exception`: 2
- `blocked`: 1
- `fail`: 1
- `missing`: 51
- `pass`: 341

## Exceptions

### fail

- `ex_1_3_2` `Example_Proof` ledger `PACKED` reason `proof_class open_math_debt_source_mismatch contains local open debt/adapter/weakening evidence`

### blocked

- `thm_1_2` `Theorem_Statement` ledger `PACKED` reason `proof_class dependency_blocked_pending_statement_decision is dependency-gate blocked without local open debt`

### allowed_exception

- `thm_11_8` `Theorem_Statement` ledger `COMPLETED` reason `cited_external_proof_exception is the explicit allowed Phase2 exception for thm_11_8`
- `thm_14_8` `Theorem_Statement` ledger `COMPLETED_WITH_PROOF_DEBT` reason `beyond_book_exception is the explicit allowed Phase2 exception for thm_14_8`

## Missing Phase2 Status Sample

- `intro_10` `Remark` ledger `DISCOVERED`
- `intro_10_1` `Remark` ledger `DISCOVERED`
- `intro_10_2` `Remark` ledger `DISCOVERED`
- `intro_10_3` `Remark` ledger `DISCOVERED`
- `intro_10_4` `Remark` ledger `DISCOVERED`
- `intro_10_5` `Remark` ledger `DISCOVERED`
- `intro_11` `Remark` ledger `DISCOVERED`
- `intro_11_1` `Remark` ledger `DISCOVERED`
- `intro_11_2` `Remark` ledger `DISCOVERED`
- `intro_11_3` `Remark` ledger `DISCOVERED`
- `intro_11_4` `Remark` ledger `DISCOVERED`
- `intro_11_5` `Remark` ledger `DISCOVERED`
- `intro_12` `Remark` ledger `DISCOVERED`
- `intro_12_1` `Remark` ledger `DISCOVERED`
- `intro_12_2` `Remark` ledger `DISCOVERED`
- `intro_12_3` `Remark` ledger `DISCOVERED`
- `intro_12_4` `Remark` ledger `DISCOVERED`
- `intro_13` `Remark` ledger `DISCOVERED`
- `intro_13_1` `Remark` ledger `DISCOVERED`
- `intro_13_2` `Remark` ledger `DISCOVERED`
- `intro_13_3` `Remark` ledger `DISCOVERED`
- `intro_13_4` `Remark` ledger `DISCOVERED`
- `intro_13_5` `Remark` ledger `DISCOVERED`
- `intro_13_6` `Remark` ledger `DISCOVERED`
- `intro_14` `Remark` ledger `DISCOVERED`
