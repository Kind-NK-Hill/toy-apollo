# Phase2 Current Status Snapshot

- generated_at: `2026-06-22T06:31:10.828986Z`
- ledger: `project_ledger.json`
- ledger_sha256: `cddfbfd82290a085939a6a49b54b46c729e2e1f1809df986a3b45029ca5e0bf0`
- ledger_size_bytes: `3551227`
- tasks: `396`
- symbols: `3084`
- legacy_obligation_tasks: `0`
- legacy_obligation_symbol_owners: `0`

This report is audit context only. It does not replace `review-apply` or declare completion.

## Status Counts

- `COMPLETED`: 345
- `COMPLETED_WITH_PROOF_DEBT`: 1
- `DISCOVERED`: 47
- `PACKED`: 3

## Phase2 Status Counts

- `allowed_exception`: 4
- `fail`: 1
- `missing`: 48
- `pass`: 343

## Exceptions

### fail

- `intro_9` `Remark` ledger `PACKED` reason `proof_class statement_weakened contains local open debt/adapter/weakening evidence`

### blocked

- none

### allowed_exception

- `ex_1_3_2` `Example_Proof` ledger `PACKED` reason `source_typo_statement_exception is the explicit allowed Phase2 exception for ex_1_3_2`
- `thm_11_8` `Theorem_Statement` ledger `COMPLETED` reason `cited_external_proof_exception is the explicit allowed Phase2 exception for thm_11_8`
- `thm_14_8` `Theorem_Statement` ledger `COMPLETED_WITH_PROOF_DEBT` reason `beyond_book_exception is the explicit allowed Phase2 exception for thm_14_8`
- `thm_1_2` `Theorem_Statement` ledger `PACKED` reason `source_statement_exception is the explicit allowed Phase2 exception for thm_1_2`

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
