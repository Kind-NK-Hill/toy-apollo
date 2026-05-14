# Unsolved Closure Runbook (Windows)

> Historical/legacy guidance. This is not the current active closure path while
> Phase 4 automation is disabled/no-op. Active Phase 3 is now limited to
> problem soft dependency selection with `soft-pack` / `soft-apply`.

## 1. Preconditions

Historical provider-only secret setup, not required for current active workflows:

```powershell
$env:ARISTOTLE_API_KEY="..."
```

## 2. Legacy State Reconcile (Status-First + Conservative)

Legacy source is read-only (`D:\Grad_Study\Practimum\toy_apollo`).

Dry-run (default):

```powershell
python .\tools\reconcile_legacy_state.py
```

Historical/manual-only mutating action: apply reconciled preview to current `project_ledger.json` (auto backup before write):

```powershell
python .\tools\reconcile_legacy_state.py --apply
```

Historical/manual-only mutating action: restore ledger from backup:

```powershell
python .\tools\reconcile_legacy_state.py --restore .\project_ledger.backup.<timestamp>.json
```

Reconcile outputs:

- `docs/reorg/reconcile_report.md`
- `docs/reorg/reconcile_conflicts.json`
- `docs/reorg/reconcile_preview_ledger.json`

## 3. Closure Execution

Historical/manual-only chained offload + align. Current Phase 4 automation is disabled/no-op; do not treat this as the active default path:

```powershell
.\tools\run_phase3_phase4.ps1
```

Legacy regression checks:

```powershell
.\tools\regression_unsolved_closure.ps1
```

## 4. Failure Matrix

- `missing_candidate_context`
  - Meaning: `FAILED_LOCAL` task missing in plan/legacy/snapshot recovery chain.
  - Action: regenerate Phase 1 plan or restore `candidate_snapshot` in ledger, then rerun Phase 3.

- `staging_dir_not_found:<task_id>`
  - Meaning: package not generated after retired provider step.
  - Historical/manual-only action: inspect archived logs and protected local artifacts such as `aristotle_outbox/`; do not route this through active Phase 3.

- `aristotle_result_cli_failed:*`
  - Meaning: retired provider CLI result harvest failed.
  - Historical/manual-only action: confirm the old CLI environment only when auditing legacy runs; do not route this through active Phase 3.

- `phase4_local_file_not_found:<task_id>`
  - Meaning: harvested file not found for align stage.
  - Historical/manual-only action: check `output_lean_files/general/` and `ToyApollo/Output/` before any manual Phase 4-style recovery.

- `phase4_lake_build_failed`
  - Meaning: align output still fails module build.
  - Historical/manual-only action: inspect `last_align_error`; do not rerun Phase 4 as an automated path while it is disabled/no-op.

## 5. Rollback

Historical/manual-only mutating Git action: before release, create rollback anchor tag:

```powershell
git tag reorg_pre_unsolved_closure
git push origin reorg_pre_unsolved_closure
```

Historical/manual-only mutating Git action: rollback to anchor:

```powershell
git checkout reorg_pre_unsolved_closure
```

Historical/manual-only mutating Git action: return to working branch:

```powershell
git checkout reorg
```

Historical/manual-only mutating action: if ledger was changed by reconcile `--apply`, rollback with the generated backup:

```powershell
python .\tools\reconcile_legacy_state.py --restore .\project_ledger.backup.<timestamp>.json
```
