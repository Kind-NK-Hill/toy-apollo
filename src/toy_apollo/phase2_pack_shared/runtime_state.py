from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .artifacts import AUTO_LOOP_PHASES, AUTO_LOOP_STATUSES, AUTO_LOOP_STOP_REASONS


def auto_loop_field_defaults() -> dict[str, Any]:
    return {
        "current_auto_loop_enabled": False,
        "current_auto_loop_entry_subject": "",
        "current_auto_loop_round": 0,
        "current_auto_loop_max_rounds": 0,
        "current_auto_loop_max_build_attempts_per_round": 0,
        "current_auto_loop_nonprogress_limit": 0,
        "current_auto_loop_consecutive_nonprogress": 0,
        "current_auto_loop_phase": "",
        "current_auto_loop_status": "",
        "current_auto_loop_stop_reason": "",
        "current_auto_loop_last_candidate_hash": "",
        "current_auto_loop_last_review_fingerprint": "",
        "current_auto_loop_last_repair_request_file": "",
    }


def auto_loop_state_from_record(current_record: dict[str, Any] | None) -> dict[str, Any]:
    record = current_record if isinstance(current_record, dict) else {}
    defaults = auto_loop_field_defaults()
    state = {
        "enabled": bool(record.get("current_auto_loop_enabled", defaults["current_auto_loop_enabled"])),
        "entry_subject": str(record.get("current_auto_loop_entry_subject", defaults["current_auto_loop_entry_subject"]) or ""),
        "round": int(record.get("current_auto_loop_round", defaults["current_auto_loop_round"]) or 0),
        "max_rounds": int(record.get("current_auto_loop_max_rounds", defaults["current_auto_loop_max_rounds"]) or 0),
        "max_build_attempts_per_round": int(record.get("current_auto_loop_max_build_attempts_per_round", defaults["current_auto_loop_max_build_attempts_per_round"]) or 0),
        "nonprogress_limit": int(record.get("current_auto_loop_nonprogress_limit", defaults["current_auto_loop_nonprogress_limit"]) or 0),
        "consecutive_nonprogress": int(record.get("current_auto_loop_consecutive_nonprogress", defaults["current_auto_loop_consecutive_nonprogress"]) or 0),
        "phase": str(record.get("current_auto_loop_phase", defaults["current_auto_loop_phase"]) or ""),
        "status": str(record.get("current_auto_loop_status", defaults["current_auto_loop_status"]) or ""),
        "stop_reason": str(record.get("current_auto_loop_stop_reason", defaults["current_auto_loop_stop_reason"]) or ""),
        "last_candidate_hash": str(record.get("current_auto_loop_last_candidate_hash", defaults["current_auto_loop_last_candidate_hash"]) or ""),
        "last_review_fingerprint": str(record.get("current_auto_loop_last_review_fingerprint", defaults["current_auto_loop_last_review_fingerprint"]) or ""),
        "last_repair_request_file": str(record.get("current_auto_loop_last_repair_request_file", defaults["current_auto_loop_last_repair_request_file"]) or ""),
    }
    if state["phase"] not in AUTO_LOOP_PHASES:
        state["phase"] = ""
    if state["status"] not in AUTO_LOOP_STATUSES:
        state["status"] = ""
    if state["stop_reason"] not in AUTO_LOOP_STOP_REASONS:
        state["stop_reason"] = ""
    return state


def auto_loop_runtime_updates(**overrides: Any) -> dict[str, Any]:
    updates = auto_loop_field_defaults()
    updates.update(overrides)
    return updates


def auto_loop_attempt_payload(current_record: dict[str, Any] | None) -> dict[str, Any]:
    state = auto_loop_state_from_record(current_record)
    if not state["enabled"] or state["status"] != "active":
        return {}
    return {
        "auto_loop_round": state["round"],
        "auto_loop_phase": state["phase"],
        "auto_loop_entry_subject": state["entry_subject"],
    }


def normalize_auto_loop_must_fix(values: Any) -> list[str]:
    normalized: list[str] = []
    if not isinstance(values, list):
        return normalized
    for value in values:
        item = " ".join(str(value or "").strip().lower().split())
        if item and item not in normalized:
            normalized.append(item)
    return normalized


def auto_loop_review_fingerprint(*, primary_failure_kind: str, must_fix: list[str], review_subject_kind: str) -> str:
    basis = {
        "primary_failure_kind": primary_failure_kind,
        "must_fix": must_fix,
        "review_subject_kind": review_subject_kind,
    }
    raw = json.dumps(basis, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def count_consecutive_primary_failures(attempts: list[dict[str, Any]]) -> tuple[str, int]:
    if not attempts:
        return "", 0
    latest_kind = str(attempts[-1].get("primary_failure_kind") or "")
    if not latest_kind:
        return "", 0
    count = 0
    for attempt in reversed(attempts):
        if str(attempt.get("primary_failure_kind") or "") != latest_kind:
            break
        count += 1
    return latest_kind, count


def recommended_action_for_kind(kind: str, repeated_count: int = 0) -> str:
    if kind == "vacuous_candidate":
        action = "Rewrite the declaration so it captures the textbook's mathematical conclusion instead of a vacuous proposition."
    elif kind == "overspecialized_candidate":
        action = "Generalize the statement back to the textbook scope before retrying; do not replace an R^d statement with a fixed low-dimensional special case."
    elif kind == "example_wrapped_theorem":
        action = "Rewrite the example around the source construction and assumptions; do not discharge it by directly invoking another theorem."
    elif kind == "reversed_example_logic":
        action = "Remove the forbidden assumption and re-state the example in the same logical direction as the textbook."
    elif kind == "weakened_statement":
        action = "Restore the original theorem shape and required hard direction instead of strengthening hypotheses to make the proof trivial."
    elif kind == "missing_required_coverage":
        action = "Add the missing textbook content identified in the semantic contract before retrying verification."
    elif kind == "missing_local_foundation_lemma":
        action = "Prove or split the task-local missing lemma; do not report a self-created theorem name as an external hard blocker."
    elif kind in {"missing_import", "unknown_identifier"}:
        action = "Return to `search_manifest.json` first and repair imports or symbol names before touching the proof body."
    elif kind == "noncomputable_required":
        action = "Handle `noncomputable` explicitly or remove the dependency on noncomputable objects before further proof edits."
    elif kind == "type_mismatch":
        action = "Check the statement shape, argument order, and coercions before broadening the search space."
    elif kind == "contains_sorry":
        action = "Finish the remaining proof holes directly; avoid structural rewrites until the current declaration is complete."
    elif kind == "final_build_failed":
        action = "Inspect final module integration conflicts, exported names, and official output imports before changing local proof code."
    elif kind == "temp_build_failed":
        action = "Fix temporary module build errors before promotion; the candidate is not stable enough for final integration."
    elif kind == "repl_failed":
        action = "Resolve the local REPL failures first; the candidate is not syntactically or semantically stable."
    else:
        action = "Review the latest diagnostics and make the smallest change that removes the current blocker."
    if repeated_count >= 2 and kind:
        return action + " This failure repeated across multiple attempts, so rewrite the current declaration instead of continuing patch-style edits."
    return action


def append_review_repair_summary_note(summary_path: Path, note: str) -> None:
    stamp = datetime.now(UTC).isoformat().replace("+00:00", "Z")
    with open(summary_path, "a", encoding="utf-8") as f:
        f.write("\n## Repair Lifecycle Note\n\n")
        f.write(f"- {stamp}: {note.strip()}\n")
