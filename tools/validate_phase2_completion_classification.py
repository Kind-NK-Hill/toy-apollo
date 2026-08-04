"""Validate the Phase2 completion classification evidence/cache artifact.

This validator checks artifact structure and evidence hygiene. Historical
artifacts may reference a retired output layout, so file existence and cited
line freshness are checked only with ``--require-fresh-evidence``. It does not
try to infer mathematical truth from Lean text and is not a completion
authority.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CLASSIFICATION = ROOT / "docs" / "phase2_completion_classification.json"

REQUIRED_TOP_LEVEL_KEYS = {
    "schema_version",
    "created",
    "scope",
    "allowed_primary_classes",
    "allowed_flags",
    "tasks",
}

REQUIRED_TASK_KEYS = {
    "task_id",
    "chapter",
    "lean_file",
    "declarations",
    "primary_class",
    "flags",
    "evidence",
    "validation",
    "classification_reason",
    "next_action",
}

REQUIRED_EVIDENCE_KEYS = {"file", "line", "kind", "text"}

ALLOWED_PRIMARY_CLASSES = {
    "textbook_proof_completed",
    "mathlib_backed_adapter_completed",
    "interface_bridge_completed",
    "open_math_debt",
    "beyond_book_exception",
    "needs_decision",
}

ALLOWED_FLAGS = {
    "public_interface_clean",
    "public_interface_leak",
    "private_axiom_internalized",
    "inherited_beyond_book_exception",
    "source_route_open",
    "metadata_only_cleanliness_risk",
    "mathlib_switch_without_textbook_route",
    "interface_bridge_present",
    "support_constructor_return_only",
    "setup_parameter_review_needed",
    "ledger_unchanged",
}

ALLOWED_EVIDENCE_KINDS = {
    "theorem",
    "def",
    "structure",
    "private_axiom",
    "public_parameter",
    "mathlib_adapter",
    "interface_bridge",
    "metadata_note",
    "audit_signal",
    "validation_command",
    "proof_contract",
}


def _rel_path(path: str) -> Path:
    return ROOT / path


def _line_text(path: Path, line_number: int) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    if line_number > len(lines):
        raise ValueError(f"{path}: line {line_number} exceeds file length {len(lines)}")
    return lines[line_number - 1]


def _has_textbook_contract_evidence(task: dict[str, Any], evidence_kinds: set[str]) -> bool:
    if "proof_contract" in evidence_kinds:
        return True
    validation = task.get("validation", [])
    if isinstance(validation, list) and any(
        "validate_phase2_obligation_contracts.py" in str(item) for item in validation
    ):
        return True
    reason = str(task.get("classification_reason", "") or "").lower()
    return "no task-local proof obligations" in reason and "level 0 direct proof" in reason


def validate_classification(
    path: Path = DEFAULT_CLASSIFICATION,
    *,
    require_textbook_contract: bool = False,
    require_fresh_evidence: bool = False,
) -> list[str]:
    errors: list[str] = []
    payload = json.loads(path.read_text(encoding="utf-8"))

    missing_top = REQUIRED_TOP_LEVEL_KEYS - payload.keys()
    if missing_top:
        errors.append(f"missing top-level keys: {sorted(missing_top)}")

    if payload.get("schema_version") != 1:
        errors.append("schema_version must be 1")

    if set(payload.get("allowed_primary_classes", [])) != ALLOWED_PRIMARY_CLASSES:
        errors.append("allowed_primary_classes does not match validator vocabulary")

    if set(payload.get("allowed_flags", [])) != ALLOWED_FLAGS:
        errors.append("allowed_flags does not match validator vocabulary")

    tasks = payload.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        errors.append("tasks must be a non-empty list")
        return errors

    seen_task_ids: set[str] = set()
    beyond_book_tasks: list[str] = []

    for index, task in enumerate(tasks):
        prefix = f"tasks[{index}]"
        if not isinstance(task, dict):
            errors.append(f"{prefix}: task must be an object")
            continue

        task_id = str(task.get("task_id", ""))
        if not task_id:
            errors.append(f"{prefix}: task_id is required")
        elif task_id in seen_task_ids:
            errors.append(f"{prefix}: duplicate task_id {task_id}")
        seen_task_ids.add(task_id)

        missing_task = REQUIRED_TASK_KEYS - task.keys()
        if missing_task:
            errors.append(f"{task_id}: missing task keys {sorted(missing_task)}")

        lean_file = task.get("lean_file")
        if not isinstance(lean_file, str) or not lean_file:
            errors.append(f"{task_id}: lean_file must be a non-empty string")
        elif require_fresh_evidence and not _rel_path(lean_file).exists():
            errors.append(f"{task_id}: lean_file does not exist: {lean_file}")

        if not isinstance(task.get("chapter"), int) or task["chapter"] <= 0:
            errors.append(f"{task_id}: chapter must be a positive integer")

        declarations = task.get("declarations")
        if not isinstance(declarations, list) or not all(isinstance(item, str) for item in declarations):
            errors.append(f"{task_id}: declarations must be a list of strings")

        primary_class = task.get("primary_class")
        if primary_class not in ALLOWED_PRIMARY_CLASSES:
            errors.append(f"{task_id}: invalid primary_class {primary_class!r}")
        if primary_class == "beyond_book_exception":
            beyond_book_tasks.append(task_id)

        flags = task.get("flags")
        if not isinstance(flags, list):
            errors.append(f"{task_id}: flags must be a list")
            flags = []
        for flag in flags:
            if flag not in ALLOWED_FLAGS:
                errors.append(f"{task_id}: invalid flag {flag!r}")

        evidence = task.get("evidence")
        if not isinstance(evidence, list) or not evidence:
            errors.append(f"{task_id}: evidence must be a non-empty list")
            evidence = []

        evidence_kinds: set[str] = set()
        for ev_index, item in enumerate(evidence):
            ev_prefix = f"{task_id}.evidence[{ev_index}]"
            if not isinstance(item, dict):
                errors.append(f"{ev_prefix}: evidence item must be an object")
                continue
            missing_evidence = REQUIRED_EVIDENCE_KEYS - item.keys()
            if missing_evidence:
                errors.append(f"{ev_prefix}: missing evidence keys {sorted(missing_evidence)}")
            kind = item.get("kind")
            if kind not in ALLOWED_EVIDENCE_KINDS:
                errors.append(f"{ev_prefix}: invalid evidence kind {kind!r}")
            else:
                evidence_kinds.add(kind)
            file_name = item.get("file")
            line = item.get("line")
            text = item.get("text")
            if not isinstance(file_name, str) or not file_name:
                errors.append(f"{ev_prefix}: file must be a non-empty string")
                continue
            evidence_file = _rel_path(file_name)
            if not evidence_file.exists():
                if require_fresh_evidence:
                    errors.append(f"{ev_prefix}: evidence file does not exist: {file_name}")
                continue
            if not isinstance(line, int) or line <= 0:
                errors.append(f"{ev_prefix}: line must be a positive integer")
                continue
            if not isinstance(text, str) or not text:
                errors.append(f"{ev_prefix}: text must be a non-empty string")
                continue
            if require_fresh_evidence:
                try:
                    actual = _line_text(evidence_file, line).strip()
                except ValueError as exc:
                    errors.append(f"{ev_prefix}: {exc}")
                    continue
                if text.strip() not in actual:
                    errors.append(
                        f"{ev_prefix}: evidence text not found at cited line; "
                        f"expected fragment {text!r}, actual {actual!r}"
                    )

        validation = task.get("validation")
        if not isinstance(validation, list) or not all(isinstance(item, str) for item in validation):
            errors.append(f"{task_id}: validation must be a list of strings")

        if "private_axiom_internalized" in flags and "private_axiom" not in evidence_kinds:
            errors.append(f"{task_id}: private_axiom_internalized requires private_axiom evidence")

        if primary_class == "mathlib_backed_adapter_completed" and not (
            {"mathlib_adapter", "interface_bridge"} & evidence_kinds
        ):
            errors.append(
                f"{task_id}: mathlib_backed_adapter_completed requires mathlib_adapter "
                "or interface_bridge evidence"
            )
        if (
            require_textbook_contract
            and primary_class == "textbook_proof_completed"
            and not _has_textbook_contract_evidence(task, evidence_kinds)
        ):
            errors.append(
                f"{task_id}: textbook_proof_completed requires proof_contract evidence, "
                "validate_phase2_obligation_contracts.py validation, or an explicit Level 0 direct proof reason"
            )

    if beyond_book_tasks != ["thm_14_8"]:
        errors.append(
            "thm_14_8 must be the only task with primary_class = beyond_book_exception; "
            f"found {beyond_book_tasks}"
        )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "path",
        nargs="?",
        default=str(DEFAULT_CLASSIFICATION),
        help="classification JSON path",
    )
    parser.add_argument(
        "--require-proof-contract",
        action="store_true",
        help="require proof-contract evidence for textbook_proof_completed entries",
    )
    args = parser.parse_args()
    errors = validate_classification(
        Path(args.path),
        require_textbook_contract=args.require_proof_contract,
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("phase2 completion classification validation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
