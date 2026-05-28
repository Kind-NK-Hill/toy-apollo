# Phase2 Tools

This file lists current validation tools and what they do.

## Lean Build

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
```

Checks the touched Lean file. Build success is mandatory but not sufficient for
proof completion.

## Completion Classification Validator

```powershell
python tools/validate_phase2_completion_classification.py
python tools/validate_phase2_completion_classification.py --require-proof-contract
```

Checks classification artifacts for consistency and required proof-contract
evidence.

## Obligation Contract Validator

```powershell
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_obligation_contracts.py --write-report
```

Checks `proof_obligations.json` contract fields. It rejects metadata claiming
proved obligations without verified theorem-level support. It is not a Lean
proof oracle.

Reports are written under `docs/phase2/reports/`.

Textbook-complete target selection is read from:

```text
docs/phase2/textbook_complete_targets.json
```

The legacy target-selection path is a fallback for old worktrees only; do not
use it as the active policy source.

## Clean Debt Surface Audit

```powershell
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Checks public proof-package surface and the unique beyond-book exception. It is
a string/static audit, not mathematical proof.

## Runner-Backed Review Modes

Phase2 `verify` and `audit` require a configured reviewer runner. If reviewer
configuration is missing, treat that as a mechanism blocker, not a mathematical
proof failure.

## Useful Searches

```powershell
rg -n "Support|Spine|Bridge|ProofBeyondBook|private axiom|axiom|sorry|admit" ToyApollo/Output
rg -n "MemLp|Integrable|Tendsto|Support|Spine|Bridge" ToyApollo/Output/<task_id>.lean
rg -n "proof_contract_status|expected_theorem_signature|public_premise_check" phase2_prompt_packs/<task_id>/proof_obligations.json
```

Use these as leads. Final judgment still follows `proof_fidelity_contract.md`.

## Obligation Promotion

```powershell
python .\run_chapter.py --phase 2 --phase2-mode promote-obligations --tasks <task_id>
```

Use only for complex tasks whose blocking obligations need first-class ledger
children. It is not proof production and does not replace Lean build or
semantic review.
