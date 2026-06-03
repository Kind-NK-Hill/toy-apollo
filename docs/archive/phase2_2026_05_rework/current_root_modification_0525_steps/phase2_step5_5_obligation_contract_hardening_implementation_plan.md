# Phase2 Step 5.5 Obligation Contract Hardening Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Phase2 unable to mark a proof obligation as `proved` unless the
landing is a real theorem/lemma that satisfies an explicit proof-fidelity
contract.

**Architecture:** Add a contract layer between semantic review and obligation
status mutation. The layer records the expected theorem signature, classifies the
actual landing, and prevents reviewer `covered` from becoming `proved` when the
landing is only a field, support package, private axiom, adapter, public
premise, or wrapper that re-assumes the source obligation.

**Tech Stack:** Python standard library, `unittest`, existing Phase2 JSON
artifacts, simple Lean declaration scanning by regex. Do not introduce external
dependencies.

---

## Status And Scope

Created: 2026-05-25

Implemented: 2026-05-25

Implementation status: complete; Step 5.6 reconciliation subsequently moved the
state beyond the initial `contract_active_with_errors` handoff by cleaning the
Step 6 priority tasks, passing the strict classification gate, and recording the
remaining queue in
`docs/modification_0525_steps/phase2_step5_6_contract_reconciliation_report.md`.

This is Step 5.5, inserted after Step 5 and the first Step 6 attempt.

It exists because Step 6 showed a real failure mode:

- `thm_11_7` and `thm_13_14` removed private axioms;
- the missing source mathematics moved to explicit statement-boundary premises;
- build and public-surface cleanup improved, but the textbook proof route was
  still open.

Step 5.5 is a mechanism-hardening step. It must not prove Lean theorems. It must
not edit `ToyApollo/Output/*.lean` except temporary test fixtures. It must not
update `project_ledger.json` by hand.

## Inputs

Read these before implementation:

- `docs/phase2_proof_fidelity_contract.md`
- `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.md`
- `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`
- `docs/modification_0525_steps/phase2_step6_challenger_postmortem_for_step_redesign.md`
- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`
- `src/toy_apollo/phase2_proof_obligations.py`
- `src/toy_apollo/phase2_semantic_review.py`
- `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`
- `tools/validate_phase2_completion_classification.py`
- `tests/test_phase2_proof_obligations.py`
- `tests/test_phase2_review_apply.py`
- `tests/test_phase2_completion_classification.py`

## Non-Goals

- Do not write the missing proofs for `thm_11_7`, `thm_13_14`, `thm_14_7`, or
  any other task.
- Do not promote any task to `textbook_proof_completed`.
- Do not treat `tools/audit_phase2_clean_debt_surface.py` as a proof-fidelity
  oracle. It remains a public-surface hygiene tool.
- Do not require every normal Level 0 task to have `proof_obligations.json`.
- Do not make schema migration destructive. Existing obligations must remain
  readable.

## Contract Vocabulary

Add these fields to obligation items when the item is proof-bearing or could be
marked `proved`:

```json
{
  "expected_theorem_signature": "theorem/lemma statement expected for this source step",
  "landing_kind": "theorem | lemma | private_axiom | structure_field | support_predicate | support_constructor | adapter | public_premise | empty | unknown",
  "proof_contract_status": "unverified | verified | failed | not_applicable | accepted_adapter | open_math_debt | beyond_book_exception",
  "proof_contract_notes": "short reason",
  "body_reassumption_check": "unverified | passed | failed | not_applicable",
  "signature_match": "unverified | passed | failed | not_applicable",
  "public_premise_check": "unverified | passed | failed | not_applicable"
}
```

Allowed transitional behavior:

- Existing files may lack these fields.
- Missing fields are warnings for open, partial, blocked, obsolete, or
  `accepted_as_proof_debt` obligations.
- Missing `expected_theorem_signature` is an error for any blocking obligation
  whose `status` is `proved`.
- `proof_contract_status = verified` is required before semantic review apply
  may convert reviewer `covered` into obligation `proved`.

## Files To Create Or Modify

Create:

- `tools/validate_phase2_obligation_contracts.py`
- `tests/test_phase2_obligation_contracts.py`
- `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.md`
- `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.json`

Modify:

- `src/toy_apollo/phase2_proof_obligations.py`
- `src/toy_apollo/phase2_semantic_review.py`
- `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`
- `src/toy_apollo/phase2_prompt_pack.py`
- `src/toy_apollo/phase2_review_request.py`
- `src/toy_apollo/phase2_review_apply.py`
- `tools/validate_phase2_completion_classification.py`
- `tests/test_phase2_proof_obligations.py`
- `tests/test_phase2_review_apply.py`
- `tests/test_phase2_pack_generation.py`
- `tests/test_phase2_completion_classification.py`

If one of the listed runtime files does not actually need code changes after
inspection, record that in the final Step 5.5 implementation report.

## Task 1: Add Contract Normalization Fields

**Files:**

- Modify: `src/toy_apollo/phase2_proof_obligations.py`
- Modify: `tests/test_phase2_proof_obligations.py`

- [ ] **Step 1: Add constants**

Add allowed values near the existing obligation constants:

```python
LANDING_KINDS = {
    "theorem",
    "lemma",
    "private_axiom",
    "structure_field",
    "support_predicate",
    "support_constructor",
    "adapter",
    "public_premise",
    "empty",
    "unknown",
}

PROOF_CONTRACT_STATUSES = {
    "unverified",
    "verified",
    "failed",
    "not_applicable",
    "accepted_adapter",
    "open_math_debt",
    "beyond_book_exception",
}

CONTRACT_CHECK_STATUSES = {
    "unverified",
    "passed",
    "failed",
    "not_applicable",
}
```

- [ ] **Step 2: Normalize fields**

In `_normalize_obligation`, preserve these fields with defaults:

```python
"expected_theorem_signature": str(item.get("expected_theorem_signature", "") or ""),
"landing_kind": _normalize_enum(item.get("landing_kind"), LANDING_KINDS, "unknown"),
"proof_contract_status": _normalize_enum(item.get("proof_contract_status"), PROOF_CONTRACT_STATUSES, "unverified"),
"proof_contract_notes": str(item.get("proof_contract_notes", "") or ""),
"body_reassumption_check": _normalize_enum(item.get("body_reassumption_check"), CONTRACT_CHECK_STATUSES, "unverified"),
"signature_match": _normalize_enum(item.get("signature_match"), CONTRACT_CHECK_STATUSES, "unverified"),
"public_premise_check": _normalize_enum(item.get("public_premise_check"), CONTRACT_CHECK_STATUSES, "unverified"),
```

Add helper:

```python
def _normalize_enum(value: Any, allowed: set[str], default: str) -> str:
    normalized = str(value or "").strip()
    return normalized if normalized in allowed else default
```

- [ ] **Step 3: Render fields in Markdown**

In `render_proof_obligations_markdown`, show the expected signature and contract
status for each obligation:

```text
  - Expected theorem signature: `...`
  - Landing kind: `...`
  - Proof contract status: `...`
  - Contract checks: signature `...`, body `...`, public premise `...`
```

- [ ] **Step 4: Add unit test**

Add a test to `tests/test_phase2_proof_obligations.py`:

```python
def test_normalize_obligation_preserves_contract_fields(self):
    payload = normalize_proof_obligations(
        {
            "task_id": "thm_test",
            "obligations": [
                {
                    "id": "source_step",
                    "kind": "source_step",
                    "status": "proved",
                    "lean_landing": "source_step_proof",
                    "expected_theorem_signature": "theorem source_step_proof : P",
                    "landing_kind": "theorem",
                    "proof_contract_status": "verified",
                    "signature_match": "passed",
                    "body_reassumption_check": "passed",
                    "public_premise_check": "passed",
                }
            ],
        },
        {"block_id": "thm_test"},
    )
    item = payload["obligations"][0]
    self.assertEqual(item["expected_theorem_signature"], "theorem source_step_proof : P")
    self.assertEqual(item["landing_kind"], "theorem")
    self.assertEqual(item["proof_contract_status"], "verified")
    self.assertEqual(item["signature_match"], "passed")
    self.assertEqual(item["body_reassumption_check"], "passed")
    self.assertEqual(item["public_premise_check"], "passed")
```

- [ ] **Step 5: Run targeted test**

Run:

```powershell
python -m unittest tests.test_phase2_proof_obligations
```

Expected: pass.

## Task 2: Add Obligation Contract Validator

**Files:**

- Create: `tools/validate_phase2_obligation_contracts.py`
- Create: `tests/test_phase2_obligation_contracts.py`

- [ ] **Step 1: Implement validator API**

Create a tool with these public functions:

```python
def validate_obligation_contracts(root: Path) -> list[dict[str, str]]:
    ...

def validate_obligations_file(root: Path, path: Path) -> list[dict[str, str]]:
    ...
```

Each finding object must include:

```python
{
    "severity": "error | warning | info",
    "task_id": "...",
    "file": "...",
    "obligation_id": "...",
    "category": "...",
    "detail": "...",
    "action": "...",
}
```

- [ ] **Step 2: Implement CLI**

The tool must support:

```powershell
python tools/validate_phase2_obligation_contracts.py
python tools/validate_phase2_obligation_contracts.py --write-report
python tools/validate_phase2_obligation_contracts.py --fail-on-errors
python tools/validate_phase2_obligation_contracts.py --task thm_11_7 --write-report
```

Default report paths:

- `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.md`
- `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.json`

Default exit behavior:

- without `--fail-on-errors`: print summary and exit `0`;
- with `--fail-on-errors`: exit `1` if any error exists.

- [ ] **Step 3: Add required error categories**

The validator must emit `error` for:

- `proved_missing_expected_signature`: blocking obligation has
  `status = proved` but empty `expected_theorem_signature`;
- `proved_missing_landing`: blocking obligation has `status = proved` but empty
  `lean_landing`;
- `proved_field_projection_landing`: `lean_landing` contains a dot suffix that
  looks like a structure field, for example `SomeSourceSpine.some_field`;
- `proved_forbidden_landing_kind`: `status = proved` and `landing_kind` is one
  of `private_axiom`, `structure_field`, `support_predicate`,
  `support_constructor`, `adapter`, `public_premise`, `empty`, or `unknown`;
- `proved_contract_not_verified`: `status = proved` but
  `proof_contract_status != verified`;
- `proved_signature_not_passed`: `status = proved` but
  `signature_match != passed`;
- `proved_body_reassumption_not_passed`: `status = proved` but
  `body_reassumption_check != passed`;
- `proved_public_premise_not_passed`: `status = proved` but
  `public_premise_check != passed`;
- `non_exception_beyond_book`: any landing or contract status attempts a
  beyond-book exception outside `thm_14_8_ProofBeyondBook`;
- `textbook_target_adapter_landing`: a task selected as Textbook Complete in
  `phase2_step5_textbook_complete_target_selection.json` has a proved obligation
  with `landing_kind = adapter`.

- [ ] **Step 4: Add warning categories**

The validator must emit `warning` for:

- `open_missing_expected_signature`: open/partial/blocked blocking obligation has
  no `expected_theorem_signature`;
- `accepted_debt_missing_contract_note`: `status = accepted_as_proof_debt` has no
  `proof_contract_notes`;
- `obsolete_verified_contract`: `status = obsolete` but
  `proof_contract_status = verified`;
- `constructor_return_needs_review`: `landing_kind = support_constructor`;
- `adapter_completion_needs_classification`: `landing_kind = adapter` and task
  classification is not clearly `mathlib_backed_adapter_completed`.

- [ ] **Step 5: Add Lean declaration scan**

Use a simple regex scanner over `ToyApollo/Output/<task_id>.lean` to classify
the landing when possible:

```python
DECL_RE = re.compile(
    r"^\\s*(private\\s+)?(theorem|lemma|axiom|def|structure)\\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
```

Rules:

- `private theorem` or `private lemma` is not automatically an error, but cannot
  satisfy Textbook Complete without explicit `proof_contract_status = verified`;
- `axiom` is a forbidden proved landing;
- `structure` is not a proof landing;
- if a named landing is not found, emit warning `landing_not_found_in_output`
  unless another tool has explicitly marked it as external Mathlib evidence.

- [ ] **Step 6: Write adversarial tests**

Create `tests/test_phase2_obligation_contracts.py` with temporary repository
fixtures. Include tests named exactly:

```python
test_proved_obligation_requires_expected_signature
test_proved_obligation_rejects_field_projection_landing
test_proved_obligation_rejects_private_axiom_landing
test_proved_obligation_rejects_support_constructor_landing
test_proved_obligation_rejects_adapter_for_textbook_target
test_verified_theorem_landing_passes
test_write_report_creates_markdown_and_json
```

Each test should create:

- `ToyApollo/Output/<task_id>.lean`
- `phase2_prompt_packs/<task_id>/proof_obligations.json`
- when needed, a minimal
  `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`

- [ ] **Step 7: Run validator tests**

Run:

```powershell
python -m unittest tests.test_phase2_obligation_contracts
```

Expected: pass.

## Task 3: Harden Review Output Shape

**Files:**

- Modify: `src/toy_apollo/phase2_proof_obligations.py`
- Modify: `src/toy_apollo/phase2_semantic_review.py`
- Modify: `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`
- Modify: `tests/test_phase2_proof_obligations.py`
- Modify: `tests/test_phase2_pack_generation.py`

- [ ] **Step 1: Extend review item schema**

`validate_obligation_review_shape` must allow and validate these optional fields
inside `obligation_review.items[*]`:

```json
{
  "expected_theorem_signature": "...",
  "landing_kind": "...",
  "proof_contract_status": "...",
  "signature_match": "passed | failed | unverified | not_applicable",
  "body_reassumption_check": "passed | failed | unverified | not_applicable",
  "public_premise_check": "passed | failed | unverified | not_applicable"
}
```

If an item has `status = covered`, these fields are required unless the
obligation itself is `not_applicable` or explicitly `accepted_as_proof_debt`.

- [ ] **Step 2: Update pass validation**

`validate_obligation_review_for_pass` must reject a pass verdict when a blocking
obligation is covered but its contract fields are missing or not passed.

Expected error text must include:

```text
pass verdict requires verified proof contract for covered obligations
```

- [ ] **Step 3: Update semantic review prompt**

In `render_semantic_review_prompt`, add instructions that a pass must compare:

- expected theorem signature against landing statement;
- whether the landing theorem assumes the same source step;
- whether the proof moved the obligation to a public premise;
- whether the landing is source-route proof, adapter, bridge, open debt, or
  beyond-book exception.

- [ ] **Step 4: Update result template/schema hints**

Where semantic review templates are generated, add schema hints for the new
contract fields. The existing `obligation_review.items` template should show the
new keys.

- [ ] **Step 5: Run tests**

Run:

```powershell
python -m unittest tests.test_phase2_proof_obligations tests.test_phase2_pack_generation
```

Expected: pass after updating expected templates.

## Task 4: Harden Review Apply

**Files:**

- Modify: `src/toy_apollo/phase2_proof_obligations.py`
- Modify: `src/toy_apollo/phase2_review_apply.py`
- Modify: `tests/test_phase2_review_apply.py`

- [ ] **Step 1: Stop direct covered-to-proved promotion**

In `apply_obligation_review_to_file`, reviewer item `status = covered` must not
automatically set `target["status"] = "proved"`.

New rule:

- if `proof_contract_status = verified` and all three checks are `passed`, set
  `status = proved`;
- otherwise keep or set `status = partial`, set `review_status = needs_review`,
  set `proof_contract_status = failed` or `unverified`, and record the evidence.

- [ ] **Step 2: Preserve review evidence**

Copy contract fields from `obligation_review.items[*]` onto the target
obligation when present.

- [ ] **Step 3: Update old tests**

Existing tests that assert covered obligations become proved must be split:

- one test with verified contract still becomes proved;
- one test without verified contract stays partial/needs_review.

The existing test name
`test_codex_review_apply_fail_marks_covered_obligations_as_proved` should either
be renamed or updated so its title no longer encodes the old unsafe behavior.

- [ ] **Step 4: Run apply tests**

Run:

```powershell
python -m unittest tests.test_phase2_review_apply tests.test_phase2_obligation_tasks
```

Expected: pass.

## Task 5: Connect Classification Validator

**Files:**

- Modify: `tools/validate_phase2_completion_classification.py`
- Modify: `tests/test_phase2_completion_classification.py`

- [ ] **Step 1: Add optional proof-contract evidence check**

For any task with `primary_class = textbook_proof_completed`, require at least
one of:

- evidence item with `kind = proof_contract`;
- validation command containing `validate_phase2_obligation_contracts.py`;
- explicit classification reason saying no task-local proof obligations are in
  scope because the task is Level 0 direct proof.

Do not break current classification artifacts without a clear error message. If
the current corpus does not yet contain proof-contract evidence, emit warning
mode first or document which entries need migration.

- [ ] **Step 2: Add allowed evidence kind if needed**

If implementing strict proof-contract evidence, add `proof_contract` to
`ALLOWED_EVIDENCE_KINDS`.

- [ ] **Step 3: Add tests**

Add tests:

```python
test_textbook_completed_requires_proof_contract_or_level0_reason
test_adapter_evidence_does_not_satisfy_textbook_contract
```

- [ ] **Step 4: Run tests**

Run:

```powershell
python -m unittest tests.test_phase2_completion_classification
python tools/validate_phase2_completion_classification.py
```

Expected: pass, or if strict mode intentionally exposes current corpus gaps,
write those gaps into the Step 5.5 audit report and do not silently weaken the
validator.

## Task 6: Generate Step 5.5 Audit Reports

**Files:**

- Create/update:
  - `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.md`
  - `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.json`

- [ ] **Step 1: Run non-failing corpus audit**

Run:

```powershell
python tools/validate_phase2_obligation_contracts.py --write-report
```

Expected:

- command exits `0`;
- Markdown and JSON reports are written under
  `docs/modification_0525_steps/`;
- report separates `error`, `warning`, and `info`;
- report states that Step 5.5 is a mechanism audit, not Lean proof completion.

- [ ] **Step 2: Run failing gate intentionally**

Run:

```powershell
python tools/validate_phase2_obligation_contracts.py --fail-on-errors
```

Expected:

- if current corpus still has contract errors, command exits `1`;
- that failure is acceptable and should be reported as the Step 5.5 finding;
- do not "fix" the failure by downgrading errors to warnings.

- [ ] **Step 3: Record final Step 5.5 result**

Add a short final section to the Markdown audit:

```text
Step 5.5 result:
- Contract validator implemented: yes/no
- Review apply hardened: yes/no
- Current corpus contract-clean: yes/no
- Lean proof work performed: no
- Next allowed step: Step 6A route extraction refresh or Step 6B signature freeze, not direct proof implementation.
```

## Task 7: Full Verification

- [ ] **Step 1: Compile changed Python**

Run:

```powershell
python -m py_compile tools/validate_phase2_obligation_contracts.py src/toy_apollo/phase2_proof_obligations.py src/toy_apollo/phase2_semantic_review.py src/toy_apollo/phase2_pack_shared/review_basis_parts.py src/toy_apollo/phase2_review_apply.py
```

Expected: no syntax errors.

- [ ] **Step 2: Run unit tests**

Run:

```powershell
python -m unittest tests.test_phase2_obligation_contracts tests.test_phase2_proof_obligations tests.test_phase2_review_apply tests.test_phase2_pack_generation tests.test_phase2_completion_classification
```

Expected: pass.

- [ ] **Step 3: Run current validators**

Run:

```powershell
python tools/validate_phase2_completion_classification.py
python tools/validate_phase2_obligation_contracts.py --write-report
```

Expected: classification validator passes; obligation contract validator writes
a report. If `--fail-on-errors` fails on current corpus, preserve the report and
explain the failing tasks.

## Completion Criteria

Step 5.5 is complete when:

- `expected_theorem_signature` and proof-contract fields are normalized and
  visible in obligation rendering;
- `validate_phase2_obligation_contracts.py` exists and has adversarial tests;
- semantic review requires proof-contract evidence for covered obligations;
- review apply no longer maps `covered` directly to `proved` without contract
  verification;
- current corpus audit report exists under `docs/modification_0525_steps/`;
- no Lean proof files were edited as part of this step.

## Handoff Summary Required From Implementer

The implementing LLM must end with:

```text
Step 5.5 implementation summary:
- Files changed:
- Tests run:
- Current validator result:
- Tasks with contract errors:
- Any intentional compatibility compromises:
- Next recommended step:
```

The next recommended step should not be "write Lean proofs" unless the contract
validator is active and the target theorem signatures are frozen.

## Step 5.5 Implementation Summary

- Files changed:
  `src/toy_apollo/phase2_proof_obligations.py`,
  `src/toy_apollo/phase2_semantic_review.py`,
  `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`,
  `src/toy_apollo/phase2_prompt_pack.py`,
  `tools/validate_phase2_completion_classification.py`,
  `tools/validate_phase2_obligation_contracts.py`,
  `tests/test_phase2_proof_obligations.py`,
  `tests/test_phase2_review_apply.py`,
  `tests/test_phase2_obligation_tasks.py`,
  `tests/test_phase2_pack_generation.py`,
  `tests/test_phase2_completion_classification.py`,
  `tests/test_phase2_obligation_contracts.py`,
  `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.md`,
  `docs/modification_0525_steps/phase2_step5_5_obligation_contract_audit.json`,
  and this work-control document.
- Files inspected but not changed after review:
  `src/toy_apollo/phase2_review_request.py` and
  `src/toy_apollo/phase2_review_apply.py`; the status mutation hook already
  delegates to `phase2_proof_obligations.apply_obligation_review_to_file`, so
  hardening the shared helper covers review apply without duplicating logic.
- Tests run:
  `python -m py_compile tools/validate_phase2_obligation_contracts.py src/toy_apollo/phase2_proof_obligations.py src/toy_apollo/phase2_semantic_review.py src/toy_apollo/phase2_pack_shared/review_basis_parts.py src/toy_apollo/phase2_review_apply.py`;
  `python -m unittest tests.test_phase2_obligation_contracts tests.test_phase2_proof_obligations tests.test_phase2_review_apply tests.test_phase2_pack_generation tests.test_phase2_completion_classification`;
  `python tools/validate_phase2_completion_classification.py`;
  `python tools/validate_phase2_obligation_contracts.py --write-report`;
  `python tools/validate_phase2_obligation_contracts.py --fail-on-errors`.
- Current validator result:
  `--write-report` exits `0`; `--fail-on-errors` exits `1` because the current
  corpus has named contract errors.
- Tasks with contract errors:
  142 tasks are currently error-bearing under the new contract audit. The
  generated JSON report contains the exact task and obligation rows.
- Any intentional compatibility compromises:
  existing `proof_obligations.json` files remain readable and are not migrated
  destructively. The completion-classification proof-contract gate is available
  through strict validation mode so the current corpus validator remains
  backward-compatible while Step 5.5 audit becomes the contract gate.
- Next recommended step:
  Step 6A route extraction refresh or Step 6B signature freeze; do not proceed
  to direct proof implementation until target theorem signatures and contract
  expectations are frozen.
