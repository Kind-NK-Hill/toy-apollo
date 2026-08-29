"""Validate Phase2 proof-obligation review-evidence metadata.

This validator is intentionally stricter than the public-surface audit: a
`proved` obligation must point at theorem-level evidence and carry an explicit
proof-fidelity contract. It does not decide completion without semantic review.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORT_BASE = (
    Path("docs")
    / "phase2"
    / "reports"
    / "obligation_contract_audit"
)
TEXTBOOK_TARGETS_PATH = (
    Path("docs")
    / "phase2"
    / "textbook_complete_targets.json"
)
LEGACY_TEXTBOOK_TARGETS_PATH = (
    Path("docs")
    / "modification_0525_steps"
    / "phase2_step5_textbook_complete_target_selection.json"
)

DECL_RE = re.compile(
    r"^\s*(private\s+)?(theorem|lemma|axiom|def|structure)\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)

ALLOWED_BEYOND_BOOK = "thm_14_8_ProofBeyondBook"
ALLOWED_BEYOND_BOOK_TASK = "thm_14_8"

OPEN_STATUSES = {"open", "partial", "blocked", "in_progress"}
FORBIDDEN_PROVED_LANDING_KINDS = {
    "private_axiom",
    "structure_field",
    "support_predicate",
    "support_constructor",
    "adapter",
    "public_premise",
    "empty",
    "unknown",
}
EXTERNAL_LANDING_KINDS = {"adapter"}
EXTERNAL_CONTRACT_STATUSES = {"accepted_adapter", "beyond_book_exception"}
TEXT_STOP_WORDS = {
    "and",
    "or",
    "uses",
    "use",
    "using",
    "candidate",
    "does",
    "not",
    "prove",
    "proof",
    "theorem",
    "lemma",
    "structure",
    "field",
    "only",
    "still",
    "missing",
    "internal",
    "external",
    "with",
    "without",
}


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    is_private: bool
    file: str
    line: int


@dataclass(frozen=True)
class ValidationContext:
    root: Path
    declarations: dict[str, Declaration]
    textbook_targets: set[str]
    classifications: dict[str, str]


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _strip_lean_comments(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if depth == 0 and source.startswith("--", index):
            newline = source.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
            continue
        if source.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    result.append("\n")
                index += 1
            continue
        result.append(source[index])
        index += 1
    return "".join(result)


def _scan_declarations(root: Path) -> dict[str, Declaration]:
    declarations: dict[str, Declaration] = {}
    output_dir = root / "ToyApollo" / "Output"
    if not output_dir.exists():
        return declarations
    for path in sorted(output_dir.glob("*.lean")):
        try:
            text = _strip_lean_comments(path.read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
        for match in DECL_RE.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            name = match.group(3)
            declarations[name] = Declaration(
                name=name,
                kind=match.group(2),
                is_private=bool(match.group(1)),
                file=_rel(path, root),
                line=line,
            )
    return declarations


def _load_textbook_targets(root: Path) -> set[str]:
    path = root / TEXTBOOK_TARGETS_PATH
    if not path.exists():
        path = root / LEGACY_TEXTBOOK_TARGETS_PATH
    payload = _read_json(path)
    if not isinstance(payload, dict):
        return set()
    targets: set[str] = set()
    for section in ("selected_textbook_targets", "selected_step6_targets", "decision_records"):
        rows = payload.get(section, [])
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            if row.get("target_class") == "textbook_proof_completed":
                task_id = str(row.get("task_id", "") or "").strip()
                if task_id:
                    targets.add(task_id)
    return targets


def _load_classifications(root: Path) -> dict[str, str]:
    path = root / "docs" / "phase2_completion_classification.json"
    payload = _read_json(path)
    if not isinstance(payload, dict):
        return {}
    rows = payload.get("tasks", [])
    if not isinstance(rows, list):
        return {}
    classifications: dict[str, str] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        task_id = str(row.get("task_id", "") or "").strip()
        primary_class = str(row.get("primary_class", "") or "").strip()
        if task_id and primary_class:
            classifications[task_id] = primary_class
    return classifications


def _make_context(root: Path) -> ValidationContext:
    root = root.resolve()
    return ValidationContext(
        root=root,
        declarations=_scan_declarations(root),
        textbook_targets=_load_textbook_targets(root),
        classifications=_load_classifications(root),
    )


def _landing_tokens(raw: str) -> list[str]:
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", raw or "")


def _candidate_landing_names(raw: str) -> list[str]:
    names: list[str] = []
    for token in _landing_tokens(raw):
        base = token.split(".", 1)[0]
        lowered = base.lower()
        if lowered in TEXT_STOP_WORDS:
            continue
        if "_" not in base and "." not in token and not base[:1].isupper():
            continue
        if base not in names:
            names.append(base)
    return names


def _structure_field_landing(raw: str, declarations: dict[str, Declaration], landing_kind: str) -> bool:
    if landing_kind == "structure_field":
        return True
    for token in _landing_tokens(raw):
        if "." not in token:
            continue
        prefix = token.split(".", 1)[0]
        decl = declarations.get(prefix)
        if decl is not None and decl.kind == "structure":
            return True
        if re.search(r"(Support|Spine|Setup|Bridge|Verification|Interface)$", prefix):
            return True
    return False


def _declared_landing_kind(
    raw_landing: str,
    landing_kind: str,
    declarations: dict[str, Declaration],
) -> str:
    if not raw_landing.strip():
        return "empty"
    if _structure_field_landing(raw_landing, declarations, landing_kind):
        return "structure_field"
    for name in _candidate_landing_names(raw_landing):
        decl = declarations.get(name)
        if decl is None:
            continue
        if decl.kind == "axiom":
            return "private_axiom"
    if landing_kind and landing_kind != "unknown":
        return landing_kind
    for name in _candidate_landing_names(raw_landing):
        decl = declarations.get(name)
        if decl is None:
            continue
        if decl.kind in {"theorem", "lemma"}:
            return decl.kind
        if decl.kind == "structure":
            return "support_predicate"
        if decl.kind == "def":
            return "support_predicate"
    return "unknown"


def _landing_is_found(raw_landing: str, declarations: dict[str, Declaration]) -> bool:
    names = _candidate_landing_names(raw_landing)
    return bool(names) and any(name in declarations for name in names)


def _skip_landing_not_found(
    landing_kind: str,
    proof_contract_status: str,
    proof_contract_notes: str,
    landing: str,
) -> bool:
    note = proof_contract_notes.lower()
    return (
        landing_kind in EXTERNAL_LANDING_KINDS
        or proof_contract_status in EXTERNAL_CONTRACT_STATUSES
        or "ProofBeyondBook" in landing
        or "mathlib" in note
        or "external" in note
    )


def _is_allowed_beyond_book(task_id: str, landing: str, proof_contract_status: str) -> bool:
    if task_id != ALLOWED_BEYOND_BOOK_TASK:
        return False
    return ALLOWED_BEYOND_BOOK in landing or proof_contract_status == "beyond_book_exception"


def _finding(
    severity: str,
    task_id: str,
    path: Path,
    root: Path,
    obligation_id: str,
    category: str,
    detail: str,
    action: str,
) -> dict[str, str]:
    return {
        "severity": severity,
        "task_id": task_id,
        "file": _rel(path, root),
        "obligation_id": obligation_id,
        "category": category,
        "detail": detail,
        "action": action,
    }


def _validate_obligation(
    context: ValidationContext,
    path: Path,
    task_id: str,
    obligation: dict[str, Any],
) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    obligation_id = str(obligation.get("id", "") or "")
    status = str(obligation.get("status", "") or "").strip()
    blocking = bool(obligation.get("blocking", True))
    landing = str(obligation.get("lean_landing", "") or obligation.get("landing", "") or "")
    expected_signature = str(obligation.get("expected_theorem_signature", "") or "").strip()
    landing_kind = str(obligation.get("landing_kind", "") or "unknown").strip() or "unknown"
    proof_contract_status = str(obligation.get("proof_contract_status", "") or "unverified").strip()
    proof_contract_notes = str(obligation.get("proof_contract_notes", "") or "").strip()
    signature_match = str(obligation.get("signature_match", "") or "unverified").strip()
    body_reassumption_check = str(obligation.get("body_reassumption_check", "") or "unverified").strip()
    public_premise_check = str(obligation.get("public_premise_check", "") or "unverified").strip()
    effective_landing_kind = _declared_landing_kind(landing, landing_kind, context.declarations)
    is_proved_blocking = status == "proved" and blocking

    if (
        ("ProofBeyondBook" in landing or proof_contract_status == "beyond_book_exception")
        and not _is_allowed_beyond_book(task_id, landing, proof_contract_status)
    ):
        findings.append(
            _finding(
                "error",
                task_id,
                path,
                context.root,
                obligation_id,
                "non_exception_beyond_book",
                "Beyond-book proof contract is only allowed for thm_14_8_ProofBeyondBook.",
                "Reclassify this obligation as open debt or route it through the exact thm_14_8 exception boundary.",
            )
        )

    if is_proved_blocking:
        if not expected_signature:
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_missing_expected_signature",
                    "Blocking proved obligation has no expected theorem signature.",
                    "Add expected_theorem_signature before accepting the obligation as proved.",
                )
            )
        if not landing.strip():
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_missing_landing",
                    "Blocking proved obligation has no Lean landing.",
                    "Record the theorem or lemma that proves the source obligation.",
                )
            )
        if _structure_field_landing(landing, context.declarations, landing_kind):
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_field_projection_landing",
                    f"Lean landing `{landing}` is a structure/support field projection.",
                    "Replace the field projection with a theorem or lemma landing.",
                )
            )
        if effective_landing_kind in FORBIDDEN_PROVED_LANDING_KINDS:
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_forbidden_landing_kind",
                    f"Proved obligation has forbidden landing kind `{effective_landing_kind}`.",
                    "Only theorem or lemma landings may discharge a proved obligation.",
                )
            )
        if proof_contract_status != "verified":
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_contract_not_verified",
                    f"proof_contract_status is `{proof_contract_status}`, not `verified`.",
                    "Verify the proof contract before marking this obligation proved.",
                )
            )
        if signature_match != "passed":
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_signature_not_passed",
                    f"signature_match is `{signature_match}`, not `passed`.",
                    "Compare the expected theorem signature with the Lean landing statement.",
                )
            )
        if body_reassumption_check != "passed":
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_body_reassumption_not_passed",
                    f"body_reassumption_check is `{body_reassumption_check}`, not `passed`.",
                    "Check that the landing body does not re-assume the same source obligation.",
                )
            )
        if public_premise_check != "passed":
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "proved_public_premise_not_passed",
                    f"public_premise_check is `{public_premise_check}`, not `passed`.",
                    "Check that the proof burden was not moved to a public theorem premise.",
                )
            )
        if task_id in context.textbook_targets and effective_landing_kind == "adapter":
            findings.append(
                _finding(
                    "error",
                    task_id,
                    path,
                    context.root,
                    obligation_id,
                    "textbook_target_adapter_landing",
                    "Textbook Complete target has a proved obligation landing classified as adapter.",
                    "Keep the task as adapter/open debt or replace the adapter with source-route theorem evidence.",
                )
            )

    if blocking and status in OPEN_STATUSES and not expected_signature:
        findings.append(
            _finding(
                "warning",
                task_id,
                path,
                context.root,
                obligation_id,
                "open_missing_expected_signature",
                "Open blocking obligation has no expected theorem signature.",
                "Record the intended theorem/lemma statement before proof work resumes.",
            )
        )
    if status == "accepted_as_proof_debt" and not proof_contract_notes:
        findings.append(
            _finding(
                "warning",
                task_id,
                path,
                context.root,
                obligation_id,
                "accepted_debt_missing_contract_note",
                "Accepted proof debt has no proof_contract_notes entry.",
                "Explain why this debt is accepted and what would discharge it.",
            )
        )
    if status == "obsolete" and proof_contract_status == "verified":
        findings.append(
            _finding(
                "warning",
                task_id,
                path,
                context.root,
                obligation_id,
                "obsolete_verified_contract",
                "Obsolete obligation still carries a verified proof contract.",
                "Clear or explain the stale verified contract on obsolete metadata.",
            )
        )
    if effective_landing_kind == "support_constructor":
        findings.append(
            _finding(
                "warning",
                task_id,
                path,
                context.root,
                obligation_id,
                "constructor_return_needs_review",
                "Landing returns or constructs support evidence rather than directly proving a source obligation.",
                "Review whether this constructor is theorem-level evidence or only support packaging.",
            )
        )
    if effective_landing_kind == "adapter" and context.classifications.get(task_id) != "mathlib_backed_adapter_completed":
        findings.append(
            _finding(
                "warning",
                task_id,
                path,
                context.root,
                obligation_id,
                "adapter_completion_needs_classification",
                "Adapter landing is not paired with mathlib_backed_adapter_completed classification.",
                "Update classification honestly or replace the adapter landing with source-route evidence.",
            )
        )
    if (
        landing.strip()
        and not _landing_is_found(landing, context.declarations)
        and not _skip_landing_not_found(landing_kind, proof_contract_status, proof_contract_notes, landing)
    ):
        severity = "error" if is_proved_blocking else "warning"
        findings.append(
            _finding(
                severity,
                task_id,
                path,
                context.root,
                obligation_id,
                "landing_not_found_in_output",
                f"No scanned Lean declaration matches `{landing}`.",
                "Check the landing name or mark it explicitly as external adapter/Mathlib evidence.",
            )
        )
    return findings


def validate_obligations_file(root: Path, path: Path) -> list[dict[str, str]]:
    """Validate one proof_obligations.json file."""
    context = _make_context(root)
    payload = _read_json(path)
    if not isinstance(payload, dict):
        return [
            _finding(
                "error",
                path.parent.name,
                path,
                context.root,
                "",
                "invalid_obligations_json",
                "proof_obligations.json is missing or invalid JSON.",
                "Repair the JSON before running the contract validator.",
            )
        ]
    task_id = str(payload.get("task_id", "") or path.parent.name)
    obligations = payload.get("obligations", [])
    if not isinstance(obligations, list):
        return [
            _finding(
                "error",
                task_id,
                path,
                context.root,
                "",
                "invalid_obligations_shape",
                "proof_obligations.json has no obligations list.",
                "Restore the obligations list before contract validation.",
            )
        ]
    findings: list[dict[str, str]] = []
    for obligation in obligations:
        if isinstance(obligation, dict):
            findings.extend(_validate_obligation(context, path, task_id, obligation))
    return findings


def _validate_with_context(context: ValidationContext, path: Path) -> list[dict[str, str]]:
    payload = _read_json(path)
    if not isinstance(payload, dict):
        return [
            _finding(
                "error",
                path.parent.name,
                path,
                context.root,
                "",
                "invalid_obligations_json",
                "proof_obligations.json is missing or invalid JSON.",
                "Repair the JSON before running the contract validator.",
            )
        ]
    task_id = str(payload.get("task_id", "") or path.parent.name)
    obligations = payload.get("obligations", [])
    if not isinstance(obligations, list):
        return [
            _finding(
                "error",
                task_id,
                path,
                context.root,
                "",
                "invalid_obligations_shape",
                "proof_obligations.json has no obligations list.",
                "Restore the obligations list before contract validation.",
            )
        ]
    findings: list[dict[str, str]] = []
    for obligation in obligations:
        if isinstance(obligation, dict):
            findings.extend(_validate_obligation(context, path, task_id, obligation))
    return findings


def validate_obligation_contracts(root: Path) -> list[dict[str, str]]:
    """Validate all Phase2 proof-obligation contracts under a repository root."""
    context = _make_context(root)
    pack_dir = context.root / "phase2_prompt_packs"
    findings: list[dict[str, str]] = []
    for path in sorted(pack_dir.glob("*/proof_obligations.json")):
        findings.extend(_validate_with_context(context, path))
    return findings


def _findings_payload(root: Path, findings: list[dict[str, str]]) -> dict[str, Any]:
    severity_counts = Counter(finding["severity"] for finding in findings)
    for severity in ("error", "warning", "info"):
        severity_counts.setdefault(severity, 0)
    category_counts = Counter(finding["category"] for finding in findings)
    error_tasks = sorted({finding["task_id"] for finding in findings if finding["severity"] == "error"})
    return {
        "schema_version": 1,
        "generated_at": _utc_stamp(),
        "root": str(root),
        "summary": {
            "finding_count": len(findings),
            "severity_counts": dict(sorted(severity_counts.items())),
            "category_counts": dict(sorted(category_counts.items())),
            "error_task_count": len(error_tasks),
            "error_tasks": error_tasks,
        },
        "findings": findings,
        "contract_audit_result": {
            "contract_validator_implemented": "yes",
            "review_apply_hardened": "yes",
            "current_corpus_contract_clean": "yes" if not error_tasks else "no",
            "lean_proof_work_performed": "no",
            "next_allowed_step": "Normal Phase2 repair loop; do not use a clean contract audit as proof completion.",
        },
    }


def _render_markdown(payload: dict[str, Any]) -> str:
    summary = payload["summary"]
    lines = [
        "# Phase2 Obligation Contract Audit",
        "",
        "This is a mechanism audit for proof-obligation contract fidelity. It is not a Lean proof-completion report.",
        "",
        "## Summary",
        "",
        f"- finding count: `{summary['finding_count']}`",
        f"- error task count: `{summary['error_task_count']}`",
    ]
    for severity, count in summary["severity_counts"].items():
        lines.append(f"- {severity}: `{count}`")
    lines.extend(["", "## Category Counts", ""])
    for category, count in summary["category_counts"].items():
        lines.append(f"- `{category}`: {count}")
    lines.extend(["", "## Findings", ""])
    lines.append("| severity | category | task | obligation | file | detail | action |")
    lines.append("| --- | --- | --- | --- | --- | --- | --- |")
    for finding in payload["findings"]:
        detail = finding["detail"].replace("|", "\\|")
        action = finding["action"].replace("|", "\\|")
        lines.append(
            f"| `{finding['severity']}` | `{finding['category']}` | `{finding['task_id']}` | "
            f"`{finding['obligation_id']}` | `{finding['file']}` | {detail} | {action} |"
        )
    result = payload["contract_audit_result"]
    lines.extend(
        [
            "",
            "## Contract audit result",
            "",
            f"- Contract validator implemented: {result['contract_validator_implemented']}",
            f"- Review apply hardened: {result['review_apply_hardened']}",
            f"- Current corpus contract-clean: {result['current_corpus_contract_clean']}",
            f"- Lean proof work performed: {result['lean_proof_work_performed']}",
            f"- Next allowed step: {result['next_allowed_step']}",
            "",
        ]
    )
    return "\n".join(lines)


def _write_reports(root: Path, findings: list[dict[str, str]]) -> dict[str, Any]:
    payload = _findings_payload(root, findings)
    report_base = root / REPORT_BASE
    _write_json(report_base.with_suffix(".json"), payload)
    report_base.with_suffix(".md").write_text(_render_markdown(payload), encoding="utf-8")
    return payload


def _validate_task(context: ValidationContext, task_id: str) -> list[dict[str, str]]:
    path = context.root / "phase2_prompt_packs" / task_id / "proof_obligations.json"
    if not path.exists():
        return [
            _finding(
                "error",
                task_id,
                path,
                context.root,
                "",
                "missing_obligations_file",
                f"No proof obligations file exists for task `{task_id}`.",
                "Create or restore the task-local proof_obligations.json file.",
            )
        ]
    return _validate_with_context(context, path)


def _print_summary(payload: dict[str, Any]) -> None:
    print(
        json.dumps(
            {
                "severity_counts": payload["summary"]["severity_counts"],
                "category_counts": payload["summary"]["category_counts"],
                "error_task_count": payload["summary"]["error_task_count"],
            },
            indent=2,
            ensure_ascii=False,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help=argparse.SUPPRESS)
    parser.add_argument("--write-report", action="store_true")
    parser.add_argument("--fail-on-errors", action="store_true")
    parser.add_argument("--task", help="Validate one task_id instead of every prompt pack.")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    context = _make_context(root)
    findings = _validate_task(context, args.task) if args.task else validate_obligation_contracts(root)
    payload = _write_reports(root, findings) if args.write_report else _findings_payload(root, findings)
    _print_summary(payload)
    if args.fail_on_errors and payload["summary"]["severity_counts"].get("error", 0):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
