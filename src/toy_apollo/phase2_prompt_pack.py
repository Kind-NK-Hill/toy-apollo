from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import (
    canonicalize_block_id,
    canonicalize_id_list,
    canonicalize_task_dict,
    extract_chapter,
    is_canonical_block_id,
    legacy_ids_for,
)
from src.compiler import LeanCompiler

from .core import LedgerManager, TaskStatus
from .dependency_decisions import DependencyDecision, load_dependency_decisions, record_dependency_decision
from .phase2_failure_budget import (
    PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW,
    PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT,
    PHASE2_AUTO_LOOP_REVIEW_ROUNDS,
    phase2_failure_counters_from_history,
)
from .phase2_pack_shared.artifacts import select_latest_existing_task_file, stale_candidate_official_output_message
from .phase2_pack_shared.io import (
    append_text as _append_text,
    copy_file as _copy_file,
    fs_path as _fs_path,
    make_dirs as _make_dirs,
    path_exists as _path_exists,
    read_file_safely as _shared_read_file_safely,
    read_json_safely as _shared_read_json_safely,
    unlink_path as _unlink_path,
    write_json as _shared_write_json,
    write_text as _shared_write_text,
)
from .phase2_math_review_gate import math_review_gate_blocker
from .phase2_output_binding import resolve_phase2_output_binding
from .phase2_review_decision import evaluate_semantic_review_result, project_normalized_semantic_review_result
from .phase2_semantic_review import (
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    build_semantic_review_input,
    latest_semantic_review_artifact_paths,
    latest_semantic_review_context_path,
    load_reviewer_config_from_env,
    next_semantic_review_artifact_paths,
    next_semantic_review_context_path,
    normalize_reviewer_result,
    render_semantic_review_prompt,
    render_semantic_review_report,
    run_semantic_review,
)
from .phase2_proof_obligations import (
    PROOF_OBLIGATIONS_FILE_NAME,
    maybe_ensure_proof_obligations_file,
    render_proof_obligations_markdown,
    summarize_proof_obligations,
)

IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
MISSING_LOCAL_FOUNDATION_LEMMA_KIND = "missing_local_foundation_lemma"
DECL_RE = re.compile(
    r"(?ms)^\s*(?:@[^\n]+\n\s*)*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+[^\n]*?(?=\s*:=|\s*\bwhere\b)",
)
TOP_LEVEL_DECL_RE = re.compile(r"(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+[A-Za-z0-9_']+")
NAMED_DECL_RE_TEMPLATE = r"(?m)^\s*(?:noncomputable\s+)?(?P<kind>theorem|lemma|def|axiom)\s+{name}\b"
VACUOUS_THEOREM_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:theorem|lemma)\s+[A-Za-z0-9_']+(?:\s*\([^)]*\))*\s*:\s*(True|PUnit|Unit)\b"
)
RD_GENERALITY_CUE_RE = re.compile(
    r"(\\mathbb\{R\}\^d|\\mathbb\{R\}\^\{d\}|R\^d|d-dimensional|for integer d|for positive integer d)",
    re.IGNORECASE,
)
GENERIC_DIMENSION_TOKENS_RE = re.compile(
    r"(\bd\s*:\s*(?:ℕ|Nat)\b|\bn\s*:\s*(?:ℕ|Nat)\b|EuclideanSpace|Fin\s+[A-Za-z0-9_']+|∀\s*\(?\s*(?:d|n)\b)",
    re.MULTILINE,
)
STOPWORDS = {
    "and",
    "the",
    "also",
    "recall",
    "for",
    "with",
    "from",
    "that",
    "this",
    "then",
    "into",
    "such",
    "two",
    "events",
    "event",
    "chapter",
    "introduction",
    "definitions",
    "definition",
    "remark",
    "theorem",
    "lemma",
    "suppose",
    "proof",
    "let",
    "conversely",
    "since",
    "because",
}
LATEX_NOISE_TOKENS = {
    "begin",
    "end",
    "textit",
    "mathcal",
    "frac",
    "cap",
    "section",
    "subsection",
    "label",
    "left",
    "right",
    "qquad",
    "quad",
    "triangleq",
    "hfill",
    "square",
    "textbf",
    "text",
    "mathbb",
    "tag",
    "rightarrow",
    "leftarrow",
    "phantom",
    "defbox",
    "thmbox",
    "bar",
    "ldots",
    "infty",
    "omega",
    "sum",
}
DOMAIN_SEARCH_WORDS = {
    "independent",
    "independence",
    "measurable",
    "measure",
    "probability",
    "random",
    "borel",
    "sigma",
    "algebra",
    "subalgebra",
    "continuous",
    "discrete",
    "pairwise",
    "mutually",
    "joint",
    "conditional",
    "distribution",
    "simple",
    "function",
    "indicator",
    "integral",
    "supremum",
    "infimum",
    "upper",
    "bound",
    "bounds",
}
CHAPTER5_SOURCE_PREFIXES = (
    "13_chap5_",
    "14_chap5_",
    "15_chap5_",
)

DRAFT_FILE_NAME = "draft.lean"
SEARCH_MANIFEST_FILE_NAME = "search_manifest.json"
DEFAULT_DEPENDENCY_SYMBOL_CHECK_LIMIT = 0
DEPENDENCY_DECISION_CONTEXT_JSON = "dependency_decision_context.json"
DEPENDENCY_DECISION_CONTEXT_MD = "dependency_decision_context.md"
ATTEMPT_HISTORY_FILE_NAME = "attempt_history.json"
FAILURE_SUMMARY_FILE_NAME = "failure_summary.md"
INTENT_CONTRACT_FILE_NAME = "intent_contract.json"
BUILD_RESULT_PREFIX = "build_result"
OFFICIAL_SNAPSHOT_PREFIX = "official_snapshot"
REVIEW_EXISTING_QUEUE_REPORT_PREFIX = "review_existing_queue"
SEMANTIC_REVIEW_RESULT_TEMPLATE_ALIAS = "semantic_review_result_template.json"
SEMANTIC_REVIEW_REQUEST_PREFIX = "semantic_review_request"
SEMANTIC_REVIEW_REQUEST_ALIAS = "semantic_review_request.json"
REVIEW_REPAIR_REQUEST_PREFIX = "review_repair_request"
REVIEW_REPAIR_REQUEST_ALIAS = "review_repair_request.json"
REVIEW_REPAIR_SUMMARY_PREFIX = "review_repair_summary"
REVIEW_REPAIR_SUMMARY_ALIAS = "review_repair_summary.md"
DRAFT_PRE_REPAIR_PREFIX = "draft_pre_repair"
NON_OFFICIAL_OUTPUT_PREFIXES = ("PackBuildCheck_", "PackVerify_", "Temp_Validation")
MUTATION_LOCK_FILE_NAME = ".phase2_mutation.lock"
STAGING_DIR_NAME = ".staging"
PACK_CANDIDATE_STATES = {
    "draft",
    "build_failed",
    "build_ready",
    "review_pending",
    "review_rejected",
}
AUTO_LOOP_PHASES = {
    "entry",
    "repair_seeded",
    "authoring",
    "build_checking",
    "review_prepared",
    "reviewing",
    "applying",
    "completed",
    "stopped",
}
AUTO_LOOP_STATUSES = {"", "active", "completed", "stopped"}
AUTO_LOOP_STOP_REASONS = {
    "",
    "passed",
    "max_rounds",
    "nonprogress",
    "build_budget_exhausted",
    "freshness_error",
    "hard_failure",
    "diagnoser_required",
}


def _auto_loop_field_defaults() -> dict[str, Any]:
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


def _auto_loop_state_from_record(current_record: dict[str, Any] | None) -> dict[str, Any]:
    from .phase2_review_loop import _auto_loop_state_from_record as _owner_auto_loop_state_from_record

    return _owner_auto_loop_state_from_record(current_record)
    record = current_record if isinstance(current_record, dict) else {}
    defaults = _auto_loop_field_defaults()
    state = {
        "enabled": bool(record.get("current_auto_loop_enabled", defaults["current_auto_loop_enabled"])),
        "entry_subject": str(record.get("current_auto_loop_entry_subject", defaults["current_auto_loop_entry_subject"]) or ""),
        "round": int(record.get("current_auto_loop_round", defaults["current_auto_loop_round"]) or 0),
        "max_rounds": int(record.get("current_auto_loop_max_rounds", defaults["current_auto_loop_max_rounds"]) or 0),
        "max_build_attempts_per_round": int(
            record.get(
                "current_auto_loop_max_build_attempts_per_round",
                defaults["current_auto_loop_max_build_attempts_per_round"],
            )
            or 0
        ),
        "nonprogress_limit": int(record.get("current_auto_loop_nonprogress_limit", defaults["current_auto_loop_nonprogress_limit"]) or 0),
        "consecutive_nonprogress": int(
            record.get("current_auto_loop_consecutive_nonprogress", defaults["current_auto_loop_consecutive_nonprogress"]) or 0
        ),
        "phase": str(record.get("current_auto_loop_phase", defaults["current_auto_loop_phase"]) or ""),
        "status": str(record.get("current_auto_loop_status", defaults["current_auto_loop_status"]) or ""),
        "stop_reason": str(record.get("current_auto_loop_stop_reason", defaults["current_auto_loop_stop_reason"]) or ""),
        "last_candidate_hash": str(
            record.get("current_auto_loop_last_candidate_hash", defaults["current_auto_loop_last_candidate_hash"]) or ""
        ),
        "last_review_fingerprint": str(
            record.get("current_auto_loop_last_review_fingerprint", defaults["current_auto_loop_last_review_fingerprint"]) or ""
        ),
        "last_repair_request_file": str(
            record.get("current_auto_loop_last_repair_request_file", defaults["current_auto_loop_last_repair_request_file"]) or ""
        ),
    }
    if state["phase"] not in AUTO_LOOP_PHASES:
        state["phase"] = ""
    if state["status"] not in AUTO_LOOP_STATUSES:
        state["status"] = ""
    if state["stop_reason"] not in AUTO_LOOP_STOP_REASONS:
        state["stop_reason"] = ""
    return state


def _auto_loop_runtime_updates(**overrides: Any) -> dict[str, Any]:
    from .phase2_review_loop import _auto_loop_runtime_updates as _owner_auto_loop_runtime_updates

    return _owner_auto_loop_runtime_updates(**overrides)
    updates = _auto_loop_field_defaults()
    updates.update(overrides)
    return updates


def _clear_current_auto_loop_metadata(task_id: str, ledger: LedgerManager) -> None:
    from .phase2_review_loop import _clear_current_auto_loop_metadata as _owner_clear_current_auto_loop_metadata

    return _owner_clear_current_auto_loop_metadata(task_id, ledger)
    ledger.update_runtime_metadata(task_id, **_auto_loop_field_defaults())


def _set_current_auto_loop_metadata(task_id: str, ledger: LedgerManager, **fields: Any) -> None:
    from .phase2_review_loop import _set_current_auto_loop_metadata as _owner_set_current_auto_loop_metadata

    return _owner_set_current_auto_loop_metadata(task_id, ledger, **fields)
    ledger.update_runtime_metadata(task_id, **fields)


def _auto_loop_attempt_payload(current_record: dict[str, Any] | None) -> dict[str, Any]:
    from .phase2_review_loop import _auto_loop_attempt_payload as _owner_auto_loop_attempt_payload

    return _owner_auto_loop_attempt_payload(current_record)
    state = _auto_loop_state_from_record(current_record)
    if not state["enabled"] or state["status"] != "active":
        return {}
    return {
        "auto_loop_round": state["round"],
        "auto_loop_phase": state["phase"],
        "auto_loop_entry_subject": state["entry_subject"],
    }


def _auto_loop_next_action(current_record: dict[str, Any] | None) -> str:
    if isinstance(current_record, dict) and {
        "enabled",
        "phase",
        "status",
    }.issubset(current_record.keys()):
        state = {
            "enabled": bool(current_record.get("enabled")),
            "phase": str(current_record.get("phase", "") or ""),
            "status": str(current_record.get("status", "") or ""),
        }
    else:
        state = _auto_loop_state_from_record(current_record)
    if not state["enabled"] or state["status"] != "active":
        return ""
    if state["phase"] in {"review_prepared", "reviewing"}:
        return "reviewer_write_result"
    if state["phase"] in {"applying", "repair_seeded"}:
        return "runtime_apply_or_repair"
    return "author_continue"


def _auto_loop_stop_reason_note(stop_reason: str) -> str:
    reason = str(stop_reason or "").strip().lower()
    if reason == "nonprogress":
        return (
            "Semantic non-progress means the loop has repeated the same semantic review failure "
            "or the same candidate content across auto-loop rounds without a meaningful fix."
        )
    return ""


def _normalize_auto_loop_must_fix(values: Any) -> list[str]:
    from .phase2_review_loop import _normalize_auto_loop_must_fix as _owner_normalize_auto_loop_must_fix

    return _owner_normalize_auto_loop_must_fix(values)
    normalized: list[str] = []
    if not isinstance(values, list):
        return normalized
    for value in values:
        item = " ".join(str(value or "").strip().lower().split())
        if item and item not in normalized:
            normalized.append(item)
    return normalized


def _auto_loop_review_fingerprint(
    *,
    primary_failure_kind: str,
    must_fix: list[str],
    review_subject_kind: str,
) -> str:
    from .phase2_review_loop import _auto_loop_review_fingerprint as _owner_auto_loop_review_fingerprint

    return _owner_auto_loop_review_fingerprint(
        primary_failure_kind=primary_failure_kind,
        must_fix=must_fix,
        review_subject_kind=review_subject_kind,
    )
    basis = {
        "primary_failure_kind": primary_failure_kind,
        "must_fix": must_fix,
        "review_subject_kind": review_subject_kind,
    }
    raw = json.dumps(basis, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def find_task_in_plans(task_id: str, plans_dir: Path) -> dict[str, Any] | None:
    canonical_task_id = canonicalize_block_id(task_id)
    for plan_file in sorted(plans_dir.glob("*_plan.json")):
        try:
            tasks = json.loads(plan_file.read_text(encoding="utf-8"))
        except Exception:
            continue
        for raw_task in tasks:
            if not isinstance(raw_task, dict):
                continue
            task = canonicalize_task_dict(raw_task)
            if task.get("block_id") != canonical_task_id:
                continue
            task["source_plan"] = task.get("source_plan") or plan_file.stem.replace("_plan", "")
            task["_source_plan_file"] = str(plan_file)
            return task
    return None


def _load_task_from_phase2_pack(task_id: str, settings) -> dict[str, Any] | None:
    canonical_task_id = canonicalize_block_id(task_id)
    task_path = settings.phase2_prompt_packs_dir / canonical_task_id / "task.json"
    task = _read_json_safely(task_path, None)
    if not isinstance(task, dict):
        return None
    task = canonicalize_task_dict(task)
    if task.get("block_id") != canonical_task_id:
        return None
    if not str(task.get("content", "")).strip():
        return None
    return task


def _task_final_import_union(task: dict[str, Any]) -> list[str]:
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    explicit_union = canonicalize_id_list(task.get("final_import_union", []))
    return canonicalize_id_list(hard_deps + soft_imports + explicit_union)


def _merge_task_import_fields(
    *,
    task_id: str,
    hard_deps: list[str],
    soft_imports: list[str],
    import_union: list[str],
    payload: dict[str, Any] | None,
) -> tuple[list[str], list[str], list[str]]:
    if not isinstance(payload, dict):
        return hard_deps, soft_imports, import_union
    hard_deps = canonicalize_id_list(hard_deps + payload.get("dependencies", []))
    soft_imports = canonicalize_id_list(soft_imports + payload.get("soft_imports", []))
    import_union = canonicalize_id_list(import_union + payload.get("final_import_union", []))
    extra_soft = [
        dep
        for dep in import_union
        if dep and dep != task_id and dep not in hard_deps and dep not in soft_imports
    ]
    soft_imports = canonicalize_id_list(soft_imports + extra_soft)
    import_union = canonicalize_id_list(hard_deps + soft_imports + import_union)
    return hard_deps, soft_imports, import_union


def _merge_effective_task_imports(task: dict[str, Any], task_id: str, ledger: LedgerManager, settings) -> dict[str, Any]:
    merged = canonicalize_task_dict(task)
    canonical_task_id = canonicalize_block_id(task_id)
    hard_deps = canonicalize_id_list(merged.get("dependencies", []))
    soft_imports = canonicalize_id_list(merged.get("soft_imports", []))
    import_union = canonicalize_id_list(merged.get("final_import_union", []))

    pack_task = _load_task_from_phase2_pack(canonical_task_id, settings)
    pack_has_import_manifest = isinstance(pack_task, dict) and any(
        key in pack_task for key in ("dependencies", "soft_imports", "final_import_union")
    )
    if pack_has_import_manifest:
        hard_deps = canonicalize_id_list(pack_task.get("dependencies", hard_deps))
        soft_imports = canonicalize_id_list(pack_task.get("soft_imports", []))
        import_union = canonicalize_id_list(pack_task.get("final_import_union", hard_deps + soft_imports))
        extra_soft = [
            dep
            for dep in import_union
            if dep and dep != canonical_task_id and dep not in hard_deps and dep not in soft_imports
        ]
        soft_imports = canonicalize_id_list(soft_imports + extra_soft)
        import_union = canonicalize_id_list(hard_deps + soft_imports + import_union)
    else:
        hard_deps, soft_imports, import_union = _merge_task_import_fields(
            task_id=canonical_task_id,
            hard_deps=hard_deps,
            soft_imports=soft_imports,
            import_union=import_union,
            payload=pack_task,
        )

    record = ledger.ledger.get("tasks", {}).get(canonical_task_id, {})
    snapshot = record.get("candidate_snapshot", {}) if isinstance(record, dict) else {}
    is_obligation_task = str(merged.get("type", "") or "").strip() == "Phase2ObligationTask"
    if is_obligation_task and pack_has_import_manifest:
        snapshot_soft_imports = canonicalize_id_list(
            snapshot.get("soft_imports", []) if isinstance(snapshot, dict) else []
        )
        soft_imports = canonicalize_id_list(soft_imports + snapshot_soft_imports)
        import_union = canonicalize_id_list(hard_deps + soft_imports + import_union)
    elif is_obligation_task or not pack_has_import_manifest:
        hard_deps, soft_imports, import_union = _merge_task_import_fields(
            task_id=canonical_task_id,
            hard_deps=hard_deps,
            soft_imports=soft_imports,
            import_union=import_union,
            payload=snapshot if isinstance(snapshot, dict) else None,
        )

    merged["dependencies"] = canonicalize_id_list([dep for dep in hard_deps if dep and dep != canonical_task_id])
    merged["soft_imports"] = canonicalize_id_list(
        dep
        for dep in soft_imports
        if dep and dep != canonical_task_id and dep not in merged["dependencies"]
    )
    merged["final_import_union"] = canonicalize_id_list(merged["dependencies"] + merged["soft_imports"] + import_union)
    return merged


def resolve_phase2_task(task_id: str, ledger: LedgerManager, settings) -> dict[str, Any]:
    canonical_task_id = canonicalize_block_id(task_id)
    tasks = ledger.ledger.get("tasks", {})
    if isinstance(tasks, dict):
        task_record = tasks.get(canonical_task_id)
        if isinstance(task_record, dict):
            task = canonicalize_task_dict(task_record)
            if task.get("block_id") == canonical_task_id and str(task.get("content", "")).strip():
                return _merge_effective_task_imports(task, canonical_task_id, ledger, settings)

    task = find_task_in_plans(canonical_task_id, settings.plans_dir)
    if task is not None:
        return _merge_effective_task_imports(task, canonical_task_id, ledger, settings)

    task = _load_task_from_phase2_pack(canonical_task_id, settings)
    if task is not None:
        return _merge_effective_task_imports(task, canonical_task_id, ledger, settings)

    pack_task_path = settings.phase2_prompt_packs_dir / canonical_task_id / "task.json"
    raise FileNotFoundError(
        f"Phase 2 task {canonical_task_id} could not be recovered from ledger, plans/*.json, or {pack_task_path}"
    )


def is_remark_task(task: dict[str, Any] | None) -> bool:
    if not isinstance(task, dict):
        return False
    return str(task.get("type", "")).strip().lower() == "remark"


def ensure_task_registered(task: dict[str, Any], ledger: LedgerManager) -> dict[str, Any]:
    task = canonicalize_task_dict(task)
    ledger.add_or_update_task(task)
    return task


def _clear_phase2_runtime_fields(task_id: str, ledger: LedgerManager) -> None:
    updates = {
        "last_pack_at": "",
        "last_verify_at": "",
        "pack_round": 0,
        "verify_attempts": 0,
        "build_attempts": 0,
        "latest_candidate_file": "",
        "latest_build_result_file": "",
        "latest_verify_result_file": "",
        "latest_semantic_review_input_file": "",
        "latest_semantic_review_result_file": "",
        "latest_semantic_review_report_file": "",
        "latest_semantic_review_context_file": "",
        "latest_math_proof_skeleton_file": "",
        "latest_math_proof_skeleton_hash": "",
        "latest_math_review_result_file": "",
        "latest_math_review_result_hash": "",
        "latest_math_review_verdict": "",
        "latest_math_review_reason": "",
        "latest_math_review_triggers": [],
        "math_review_gate_required": False,
        "math_review_gate_status": "",
        "latest_official_snapshot_file": "",
        "latest_operation_kind": "",
        "latest_operation_file": "",
        "pack_candidate_state": "draft",
        "latest_build_candidate_kind": "",
        "latest_build_candidate_file": "",
        "latest_build_candidate_hash": "",
        "latest_build_ready_candidate_kind": "",
        "latest_build_ready_candidate_file": "",
        "latest_build_ready_candidate_hash": "",
        "latest_search_manifest_file": "",
        "current_review_input_file": "",
        "current_review_prompt_file": "",
        "current_review_template_file": "",
        "current_review_context_file": "",
        "current_review_request_file": "",
        "current_review_backend_id": "",
        "current_review_expected_result_file": "",
        "current_review_subject_kind": "",
        "current_review_subject_file": "",
        "current_review_subject_hash": "",
        "current_review_origin": "",
        "last_error": "",
    }
    updates.update(_auto_loop_field_defaults())
    ledger.update_runtime_metadata(task_id, **updates)


def mark_remark_completed_without_pack(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    delete_pack_dir: bool = True,
) -> bool:
    task_id = canonicalize_block_id(task_id)
    if not task_id:
        return False

    task_record = ledger.ledger.get("tasks", {}).get(task_id)
    if not isinstance(task_record, dict) or str(task_record.get("type", "")).strip().lower() != "remark":
        return False

    ledger.update_status(task_id, TaskStatus.COMPLETED)
    _clear_phase2_runtime_fields(task_id, ledger)

    if delete_pack_dir:
        packs_root = settings.phase2_prompt_packs_dir.resolve()
        pack_dir = (settings.phase2_prompt_packs_dir / task_id).resolve()
        if pack_dir.exists() and packs_root in pack_dir.parents:
            shutil.rmtree(pack_dir, ignore_errors=True)
    return True


def repair_packed_remark_tasks(
    ledger: LedgerManager,
    settings,
    *,
    source_plan_prefixes: tuple[str, ...] | None = None,
    delete_pack_dirs: bool = True,
) -> list[str]:
    repaired: list[str] = []
    tasks = ledger.ledger.get("tasks", {})
    for task_id, task_record in tasks.items():
        if not isinstance(task_record, dict):
            continue
        if str(task_record.get("type", "")).strip().lower() != "remark":
            continue
        if str(task_record.get("status", "")) != TaskStatus.PACKED.value:
            continue
        source_plan = str(task_record.get("source_plan", ""))
        if source_plan_prefixes and not source_plan.startswith(source_plan_prefixes):
            continue
        if mark_remark_completed_without_pack(
            task_id,
            ledger,
            settings,
            delete_pack_dir=delete_pack_dirs,
        ):
            repaired.append(task_id)
    return sorted(repaired)


def list_candidate_files(pack_dir: Path) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(r"candidate_v(\d+)\.lean", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted(
        [p for p in pack_dir.glob("candidate_v*.lean") if p.is_file()],
        key=sort_key,
    )


def select_latest_candidate(pack_dir: Path) -> Path | None:
    candidates = list_candidate_files(pack_dir)
    return candidates[-1] if candidates else None


def _list_versioned_json_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.json", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted(
        [p for p in pack_dir.glob(f"{prefix}_v*.json") if p.is_file()],
        key=sort_key,
    )


def _list_versioned_md_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.md", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted(
        [p for p in pack_dir.glob(f"{prefix}_v*.md") if p.is_file()],
        key=sort_key,
    )


def _list_versioned_lean_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.lean", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted(
        [p for p in pack_dir.glob(f"{prefix}_v*.lean") if p.is_file()],
        key=sort_key,
    )


def select_latest_verify_result(pack_dir: Path) -> Path | None:
    results = _list_versioned_json_files(pack_dir, "verify_result")
    return results[-1] if results else None


def select_latest_build_result(pack_dir: Path) -> Path | None:
    results = _list_versioned_json_files(pack_dir, BUILD_RESULT_PREFIX)
    return results[-1] if results else None


def select_latest_official_snapshot(pack_dir: Path) -> Path | None:
    results = _list_versioned_lean_files(pack_dir, OFFICIAL_SNAPSHOT_PREFIX)
    return results[-1] if results else None


def _next_candidate_path(pack_dir: Path) -> tuple[int, Path]:
    latest = select_latest_candidate(pack_dir)
    if latest is None:
        return 1, pack_dir / "candidate_v1.lean"
    match = re.fullmatch(r"candidate_v(\d+)\.lean", latest.name)
    version = int(match.group(1)) + 1 if match else 1
    return version, pack_dir / f"candidate_v{version}.lean"


def _next_build_result_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{BUILD_RESULT_PREFIX}_v{attempt}.json"


def _next_review_attempt(pack_dir: Path) -> int:
    latest = _list_versioned_json_files(pack_dir, "semantic_review_input")
    if not latest:
        return 1
    match = re.fullmatch(r"semantic_review_input_v(\d+)\.json", latest[-1].name)
    return int(match.group(1)) + 1 if match else 1


def _next_official_snapshot_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{OFFICIAL_SNAPSHOT_PREFIX}_v{attempt}.lean"


def _result_template_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"semantic_review_result_template_v{attempt}.json"


def _review_request_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{SEMANTIC_REVIEW_REQUEST_PREFIX}_v{attempt}.json"


def _latest_review_request_path(pack_dir: Path) -> Path:
    return pack_dir / SEMANTIC_REVIEW_REQUEST_ALIAS


def _review_repair_request_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{REVIEW_REPAIR_REQUEST_PREFIX}_v{attempt}.json"


def _latest_review_repair_request_path(pack_dir: Path) -> Path:
    return pack_dir / REVIEW_REPAIR_REQUEST_ALIAS


def _review_repair_summary_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{REVIEW_REPAIR_SUMMARY_PREFIX}_v{attempt}.md"


def _latest_review_repair_summary_path(pack_dir: Path) -> Path:
    return pack_dir / REVIEW_REPAIR_SUMMARY_ALIAS


def _next_review_repair_attempt(pack_dir: Path) -> int:
    latest = _list_versioned_json_files(pack_dir, REVIEW_REPAIR_REQUEST_PREFIX)
    if not latest:
        return 1
    match = re.fullmatch(rf"{re.escape(REVIEW_REPAIR_REQUEST_PREFIX)}_v(\d+)\.json", latest[-1].name)
    return int(match.group(1)) + 1 if match else 1


def _next_pre_repair_draft_path(pack_dir: Path) -> Path:
    latest = _list_versioned_lean_files(pack_dir, DRAFT_PRE_REPAIR_PREFIX)
    if not latest:
        return pack_dir / f"{DRAFT_PRE_REPAIR_PREFIX}_v1.lean"
    match = re.fullmatch(rf"{re.escape(DRAFT_PRE_REPAIR_PREFIX)}_v(\d+)\.lean", latest[-1].name)
    version = int(match.group(1)) + 1 if match else 1
    return pack_dir / f"{DRAFT_PRE_REPAIR_PREFIX}_v{version}.lean"


def _next_verify_result_path(pack_dir: Path, attempt: int | None = None) -> Path:
    if attempt is None:
        attempt = len(_list_versioned_json_files(pack_dir, "verify_result")) + 1
    return pack_dir / f"verify_result_v{attempt}.json"


def extract_search_terms(title: str, content: str, limit: int = 8) -> list[str]:
    terms: list[str] = []

    def add_term(term: str) -> None:
        normalized = term.strip()
        if not normalized:
            return
        if normalized not in terms:
            terms.append(normalized)

    def should_skip(term: str) -> bool:
        lowered = term.lower()
        return (
            lowered in STOPWORDS
            or lowered in LATEX_NOISE_TOKENS
            or re.fullmatch(r"[A-Za-z]_[A-Za-z0-9]+", term) is not None
        )

    normalized_content = re.sub(r"\\begin\{[^}]*\}|\\end\{[^}]*\}", " ", content)
    normalized_content = re.sub(r"\\[A-Za-z]+\*?(?:\{[^}]*\})?", " ", normalized_content)
    normalized_content = normalized_content.replace("{", " ").replace("}", " ")

    for word in re.findall(r"[A-Za-z][A-Za-z0-9_']{2,}", title):
        if not should_skip(word):
            add_term(word)

    for cmd in re.findall(r"\\([A-Za-z]+)", content):
        if len(cmd) >= 3 and not should_skip(cmd):
            add_term(cmd)

    for ident in re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", normalized_content):
        if len(ident) < 3:
            continue
        if should_skip(ident):
            continue
        if ident[0].isupper() or any(ch.isupper() for ch in ident[1:]) or ident in {"sup", "inf", "limsup", "liminf"}:
            add_term(ident)

    for word in re.findall(r"\b[a-z][a-z]{3,}\b", normalized_content.lower()):
        if word in DOMAIN_SEARCH_WORDS and not should_skip(word):
            add_term(word)

    return terms[:limit]


def build_import_lines(task: dict[str, Any]) -> list[str]:
    final_union = _task_final_import_union(task)
    import_lines = ["import Mathlib"]
    for dep in final_union:
        import_lines.append(f"import ToyApollo.Output.{canonicalize_block_id(dep)}")
    return import_lines


def build_dependency_decision_context(task: dict[str, Any], settings) -> dict[str, Any]:
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    final_union = _task_final_import_union(task)
    decisions_by_dep: dict[str, list[dict[str, Any]]] = {}
    missing: list[str] = []
    decisions = load_dependency_decisions(settings, task_id)
    for dep_id in final_union:
        dep_decisions = [decision for decision in decisions if decision.get("dep_id") == dep_id]
        decisions_by_dep[dep_id] = dep_decisions
        if not dep_decisions:
            missing.append(dep_id)
    return {
        "task_id": task_id,
        "hard_dependencies": hard_deps,
        "soft_imports": soft_imports,
        "final_import_union": final_union,
        "decisions_by_dep": decisions_by_dep,
        "missing_decision_records": missing,
    }


def render_dependency_decision_context_markdown(context: dict[str, Any]) -> str:
    lines = [
        f"# Dependency Decision Context for {context.get('task_id', '')}",
        "",
        f"- Hard dependencies: `{', '.join(context.get('hard_dependencies', [])) or '(none)'}`",
        f"- Soft imports: `{', '.join(context.get('soft_imports', [])) or '(none)'}`",
        f"- Final import union: `{', '.join(context.get('final_import_union', [])) or '(none)'}`",
        "",
        "## Decisions",
        "",
    ]
    decisions_by_dep = context.get("decisions_by_dep", {})
    for dep_id in context.get("final_import_union", []):
        dep_decisions = decisions_by_dep.get(dep_id, [])
        lines.append(f"### `{dep_id}`")
        lines.append("")
        if not dep_decisions:
            lines.append("- Missing decision record.")
            lines.append("")
            continue
        for decision in dep_decisions:
            evidence = str(decision.get("evidence", "") or "")
            lines.append(
                "- "
                f"{decision.get('kind', '')} via {decision.get('phase', '')} "
                f"({decision.get('criterion', '')})"
            )
            if evidence:
                lines.append(f"  Evidence: {evidence}")
        lines.append("")
    missing = context.get("missing_decision_records", [])
    lines.append("## Missing Decision Records")
    lines.append("")
    lines.append(f"- `{', '.join(missing) if missing else '(none)'}`")
    lines.append("")
    return "\n".join(lines)


def write_dependency_decision_context(pack_dir: Path, task: dict[str, Any], settings) -> dict[str, Any]:
    context = build_dependency_decision_context(task, settings)
    _write_json(pack_dir / DEPENDENCY_DECISION_CONTEXT_JSON, context)
    _shared_write_text(pack_dir / DEPENDENCY_DECISION_CONTEXT_MD, render_dependency_decision_context_markdown(context))
    return context


def _record_undeclared_import_violations(
    task: dict[str, Any],
    diagnostics: list[dict[str, Any]],
    settings,
    source_file: Path,
) -> None:
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    if not task_id:
        return
    source_plan = str(task.get("source_plan", "") or "")
    for diagnostic in diagnostics:
        if diagnostic.get("kind") != "undeclared_local_import":
            continue
        for dep_id in canonicalize_id_list(diagnostic.get("blocking_symbols", [])):
            record_dependency_decision(
                settings,
                DependencyDecision(
                    task_id=task_id,
                    dep_id=dep_id,
                    kind="violation",
                    phase="phase2_build_check",
                    criterion="undeclared_candidate_import",
                    evidence=str(diagnostic.get("message", "") or ""),
                    source_plan=source_plan,
                    source_file=str(source_file),
                ),
            )


def extract_declaration_stub(code: str) -> str | None:
    if not code or "sorry" in code:
        return None
    matches = list(DECL_RE.finditer(code))
    if len(matches) != 1:
        return None
    return matches[0].group(0).strip()


def has_meaningful_declaration(code: str) -> bool:
    if not code.strip():
        return False
    if "-- WRITE FINAL LEAN CODE BELOW" in code:
        return False
    return TOP_LEVEL_DECL_RE.search(code) is not None


def has_top_level_declaration(code: str) -> bool:
    return bool(code.strip() and TOP_LEVEL_DECL_RE.search(code) is not None)


def _source_text(task: dict[str, Any]) -> str:
    return f"{task.get('title', '')}\n{task.get('content', '')}"


def _normalized_source_text(task: dict[str, Any]) -> str:
    return _source_text(task).lower()


def _dedupe_strings(values: list[str]) -> list[str]:
    seen: set[str] = set()
    deduped: list[str] = []
    for value in values:
        normalized = str(value or "").strip()
        if not normalized or normalized in seen:
            continue
        seen.add(normalized)
        deduped.append(normalized)
    return deduped


def build_legacy_intent_contract(task: dict[str, Any]) -> dict[str, Any]:
    task_type = str(task.get("type", "")).strip().lower()
    source_text = _normalized_source_text(task)
    task_role = "theorem"
    if "definition" in task_type:
        task_role = "definition"
    elif "example" in task_type:
        task_role = "example"

    required_cues: list[str] = []
    forbidden_relaxations: list[str] = []
    must_not_assume: list[str] = []

    is_counterexample_example = (
        "example" in task_type
        and (
            "converse of" in source_text
            or "not independent" in source_text
            or "joint density" in source_text
            or "fxy" in source_text
            or "f_{xy}" in source_text
            or "f_{x,y}" in source_text
        )
    )
    is_analytic_example = (
        "example" in task_type
        and (
            "gaussian" in source_text
            or "joint gaussian" in source_text
            or "correlation" in source_text
            or "correlated" in source_text
        )
    )
    is_generator_theorem = (
        "theorem" in task_type
        and (
            "π-system" in source_text
            or "pi-system" in source_text
            or "lambda-system" in source_text
            or "generatefrom" in source_text
            or "dynkin" in source_text
        )
    )
    is_iff_theorem = (
        "theorem" in task_type
        and (
            "if and only if" in source_text
            or " iff " in f" {source_text} "
            or "converse" in source_text
        )
    )

    if is_counterexample_example:
        task_role = "counterexample_example"
        required_cues.extend(
            [
                "counterexample_construction",
                "dependence_of_original_objects",
                "independence_of_transforms",
            ]
        )
        if any(token in source_text for token in ("fxy", "f_{xy}", "f_{x,y}", "1/4(1+xy)", "\\frac{1}{4}(1+xy)")):
            required_cues.append("explicit_joint_density_formula")
        if any(token in source_text for token in ("x^2", "y^2", "sqrt{x}\\sqrt{y}", "\\sqrt{x}\\sqrt{y}", "p(x^2")):
            required_cues.append("square_cdf_factorization")
        forbidden_relaxations.extend(
            [
                "theorem_wrapper",
                "assume_original_independence",
            ]
        )
        must_not_assume.append("original_independence")
    elif is_analytic_example:
        task_role = "analytic_example"
        required_cues.extend(
            [
                "joint_gaussian_or_density_factorization",
                "zero_correlation",
                "independence_conclusion",
            ]
        )
        if (
            ("factoriz" in source_text and "density" in source_text)
            or any(
                token in source_text
                for token in ("exp\\left", "1/(2\\pi", "\\frac{1}{2\\pi", "joint gaussian probability density function")
            )
        ):
            required_cues.append("explicit_density_factorization")
        forbidden_relaxations.append("assume_independence_up_front")
        must_not_assume.append("independence_up_front")
    elif (
        "example" in task_type
        and "pairwise independent" in source_text
        and "mutually independent" in source_text
    ):
        task_role = "example"
        required_cues.extend(
            [
                "counterexample_construction",
                "pairwise_not_mutual_gap",
            ]
        )
        forbidden_relaxations.append("theorem_wrapper")
    elif is_generator_theorem:
        task_role = "generator_theorem"
        required_cues.extend(["generator_family", "extension_argument"])
        forbidden_relaxations.append("assume_all_measurable_sets_already_in_generator")
    elif is_iff_theorem:
        task_role = "iff_theorem"
        required_cues.append("both_directions")
        forbidden_relaxations.append("drop_hard_direction")

    if "open balls" in source_text:
        required_cues.append("open_balls_generation")

    if (
        "cantor" in source_text
        and ("distribution" in source_text or "random" in source_text or "probability" in source_text or "cdf" in source_text)
        and "example" in task_type
    ):
        required_cues.extend(
            [
                "cantor_distribution_construction",
                "cdf_or_probability_property",
                "cantor_set_conclusion",
            ]
        )

    if task_role == "iff_theorem" and ("cdf" in source_text or "distribution" in source_text or "probability" in source_text):
        required_cues.append("cdf_or_probability_property")

    return {
        "task_role": task_role,
        "required_cues": _dedupe_strings(required_cues),
        "forbidden_relaxations": _dedupe_strings(forbidden_relaxations),
        "must_not_assume": _dedupe_strings(must_not_assume),
        "coverage_mode": "strict_source_alignment",
    }


def _intent_contract_path(pack_dir: Path) -> Path:
    return pack_dir / INTENT_CONTRACT_FILE_NAME


def ensure_intent_contract(pack_dir: Path, task: dict[str, Any]) -> dict[str, Any]:
    contract = build_legacy_intent_contract(task)
    _write_json(_intent_contract_path(pack_dir), contract)
    return contract


def load_or_create_intent_contract(pack_dir: Path, task: dict[str, Any]) -> dict[str, Any]:
    expected = build_legacy_intent_contract(task)
    contract = _read_json_safely(_intent_contract_path(pack_dir), None)
    if isinstance(contract, dict) and isinstance(contract.get("required_cues", []), list) and contract == expected:
        return contract
    _write_json(_intent_contract_path(pack_dir), expected)
    return expected


def iter_official_output_targets(task_id: str, source_plan: str, settings) -> list[Path]:
    targets = [
        settings.toyapollo_output_dir / f"{task_id}.lean",
        settings.output_lean_files_dir / "general" / f"{task_id}.lean",
    ]
    if source_plan and source_plan != "unknown":
        targets.append(settings.output_lean_files_dir / source_plan / f"{task_id}.lean")

    deduped: list[Path] = []
    seen: set[Path] = set()
    for target in targets:
        if target not in seen:
            seen.add(target)
            deduped.append(target)
    return deduped


def _has_active_official_output(task_id: str, source_plan: str, ledger: LedgerManager, settings) -> bool:
    status = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("status", "") or "")
    existing = find_existing_task_file(task_id, source_plan, settings)
    completed_statuses = {TaskStatus.COMPLETED.value, TaskStatus.COMPLETED_WITH_PROOF_DEBT.value}
    return status in completed_statuses and existing is not None and existing.exists()


def _status_counts_have_accepted_proof_debt(status_counts: Any) -> bool:
    if not isinstance(status_counts, dict):
        return False
    try:
        return int(status_counts.get("accepted_as_proof_debt", 0) or 0) > 0
    except (TypeError, ValueError):
        return False


def _ledger_record_has_accepted_proof_debt(record: dict[str, Any]) -> bool:
    status = str(record.get("status", "") or "").strip()
    if status == TaskStatus.COMPLETED_WITH_PROOF_DEBT.value:
        return True
    summary = record.get("proof_obligation_summary")
    if isinstance(summary, dict) and _status_counts_have_accepted_proof_debt(summary.get("status_counts", {})):
        return True
    obligations = record.get("proof_obligations")
    if isinstance(obligations, dict):
        if _status_counts_have_accepted_proof_debt(obligations.get("status_counts", {})):
            return True
        raw_items = obligations.get("obligations", [])
        if isinstance(raw_items, list) and any(
            isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt"
            for item in raw_items
        ):
            return True
    obligation_review = record.get("obligation_review")
    if isinstance(obligation_review, dict):
        raw_items = obligation_review.get("items", [])
        if isinstance(raw_items, list) and any(
            isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt"
            for item in raw_items
        ):
            return True
    return False


def _ledger_record_is_explicit_allowed_exception(record: dict[str, Any]) -> bool:
    phase2_status = str(record.get("phase2_status") or record.get("phase2_task_status") or "").strip()
    evidence_type = str(
        record.get("phase2_status_evidence_type") or record.get("phase2_task_status_evidence_type") or ""
    ).strip()
    return phase2_status == "allowed_exception" and evidence_type == "explicit_allowed_exception"


def _ledger_record_dependencies(record: dict[str, Any]) -> list[str]:
    deps: list[str] = []
    deps.extend(canonicalize_id_list(record.get("dependencies", [])))
    snapshot = record.get("candidate_snapshot", {})
    if isinstance(snapshot, dict):
        deps.extend(canonicalize_id_list(snapshot.get("dependencies", [])))
    return canonicalize_id_list(deps)


def hard_dependency_proof_debt_blockers(task: dict[str, Any], ledger: LedgerManager) -> list[str]:
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    task_map = ledger.ledger.get("tasks", {})
    if not isinstance(task_map, dict):
        return []
    blockers: list[str] = []
    seen: set[str] = {task_id} if task_id else set()
    stack = list(reversed(canonicalize_id_list(task.get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        dep_record = task_map.get(dep_id, {})
        if not isinstance(dep_record, dict):
            continue
        if _ledger_record_is_explicit_allowed_exception(dep_record):
            stack.extend(reversed(_ledger_record_dependencies(dep_record)))
            continue
        if _ledger_record_has_accepted_proof_debt(dep_record) or str(dep_record.get("status", "") or "") == "DEPENDENCY_PROOF_DEBT":
            blockers.append(dep_id)
            continue
        stack.extend(reversed(_ledger_record_dependencies(dep_record)))
    return canonicalize_id_list(blockers)


def hard_dependency_proof_debt_blocker_message(task: dict[str, Any], ledger: LedgerManager) -> str:
    blockers = hard_dependency_proof_debt_blockers(task, ledger)
    if not blockers:
        return ""
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    blocker_text = ", ".join(blockers)
    return (
        f"Task {task_id} is blocked because hard dependency {blocker_text} carries accepted proof debt. "
        "Run debt-fix on the blocker and finish the repair loop before generating downstream Phase 2 work."
    )


def _raise_if_hard_dependency_has_proof_debt(task: dict[str, Any], ledger: LedgerManager) -> None:
    detail = hard_dependency_proof_debt_blocker_message(task, ledger)
    if detail:
        raise ValueError(detail)


def _pack_metadata_path(pack_dir: Path) -> Path:
    return pack_dir / "metadata.json"


def _task_lock_path(pack_dir: Path) -> Path:
    return pack_dir / MUTATION_LOCK_FILE_NAME


def _task_staging_root(pack_dir: Path) -> Path:
    return pack_dir / STAGING_DIR_NAME


def _utc_now_z() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _pid_is_running(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def _read_lock_payload(lock_path: Path) -> dict[str, Any] | None:
    payload = _read_json_safely(lock_path, None)
    return payload if isinstance(payload, dict) else None


def _remove_tree(path: Path) -> None:
    shutil.rmtree(_fs_path(path), ignore_errors=True)


def _restore_staging_manifest(manifest_path: Path) -> bool:
    manifest = _read_json_safely(manifest_path, None)
    if not isinstance(manifest, dict):
        return False
    targets = manifest.get("targets", [])
    if not isinstance(targets, list):
        return False
    try:
        for entry in targets:
            if not isinstance(entry, dict):
                return False
            target = Path(str(entry.get("target", "") or ""))
            backup_path = Path(str(entry.get("backup_path", "") or ""))
            original_existed = bool(entry.get("original_existed", False))
            if original_existed:
                if not _path_exists(backup_path):
                    return False
                _make_dirs(target.parent, exist_ok=True)
                _copy_file(backup_path, target)
                original_atime_ns = entry.get("original_atime_ns")
                original_mtime_ns = entry.get("original_mtime_ns")
                if isinstance(original_atime_ns, int) and isinstance(original_mtime_ns, int):
                    os.utime(_fs_path(target), ns=(original_atime_ns, original_mtime_ns))
            elif _path_exists(target):
                _unlink_path(target)
    except Exception:
        return False

    try:
        staging_dir = manifest_path.parent
        _remove_tree(staging_dir)
    except Exception:
        return False
    return True


def _remove_empty_staging_dir_without_manifest(staging_dir: Path) -> None:
    if not os.path.isdir(_fs_path(staging_dir)):
        return
    if _path_exists(staging_dir / "staging_manifest.json"):
        return
    try:
        with os.scandir(_fs_path(staging_dir)) as entries:
            if next(entries, None) is not None:
                return
        os.rmdir(_fs_path(staging_dir))
    except FileNotFoundError:
        return


def _staging_backup_path(staging_dir: Path, index: int, target: Path) -> Path:
    return staging_dir / f"backup_{index}{target.suffix}"


def _recover_stale_mutation_lock(task_id: str, pack_dir: Path, payload: dict[str, Any] | None) -> None:
    candidates: list[Path] = []
    if isinstance(payload, dict):
        staging_dir = str(payload.get("staging_dir", "") or "").strip()
        if staging_dir:
            manifest = Path(staging_dir) / "staging_manifest.json"
            if _path_exists(manifest):
                candidates.append(manifest)
    staging_root = _task_staging_root(pack_dir)
    if os.path.isdir(_fs_path(staging_root)):
        with os.scandir(_fs_path(staging_root)) as entries:
            for entry in entries:
                if not entry.is_dir():
                    continue
                manifest = Path(entry.path) / "staging_manifest.json"
                if _path_exists(manifest) and manifest not in candidates:
                    candidates.append(manifest)

    for manifest in candidates:
        if not _restore_staging_manifest(manifest):
            raise RuntimeError(
                f"Phase 2 mutation lock recovery failed for {task_id}; could not restore {manifest}"
            )


def _acquire_task_local_lock(task_id: str, pack_dir: Path, mode: str) -> tuple[Path, dict[str, Any]]:
    lock_path = _task_lock_path(pack_dir)
    if _path_exists(lock_path):
        payload = _read_lock_payload(lock_path)
        if (
            payload is None
            or not {"task_id", "pid", "created_at", "mode", "staging_dir"}.issubset(payload.keys())
            or not _pid_is_running(int(payload.get("pid") or 0))
        ):
            _recover_stale_mutation_lock(task_id, pack_dir, payload)
            if _path_exists(lock_path):
                _unlink_path(lock_path)
        else:
            raise RuntimeError(
                "Phase 2 mutation lock is active for "
                f"{task_id}: pid={payload.get('pid')} mode={payload.get('mode')} created_at={payload.get('created_at')}"
            )
    payload = {
        "task_id": task_id,
        "pid": os.getpid(),
        "created_at": _utc_now_z(),
        "mode": mode,
        "staging_dir": "",
    }
    _write_json(lock_path, payload)
    return lock_path, payload


def _rewrite_task_lock(lock_path: Path, payload: dict[str, Any]) -> None:
    _write_json(lock_path, payload)


def _release_task_local_lock(lock_path: Path) -> None:
    if _path_exists(lock_path):
        _unlink_path(lock_path)


def _run_staged_official_build(
    task_id: str,
    source_plan: str,
    settings,
    pack_dir: Path,
    candidate_code: str,
    *,
    attempt: int,
    mode: str,
    restore_on_success: bool = True,
    output_owner_task_id: str | None = None,
) -> tuple[bool, str]:
    output_owner_task_id = canonicalize_block_id(output_owner_task_id or task_id)
    lock_pack_dir = settings.phase2_prompt_packs_dir / output_owner_task_id if output_owner_task_id != task_id else pack_dir
    _make_dirs(lock_pack_dir, exist_ok=True)
    lock_path, lock_payload = _acquire_task_local_lock(output_owner_task_id, lock_pack_dir, mode)
    staging_dir = _task_staging_root(lock_pack_dir) / f"{mode}-{attempt}"
    _remove_empty_staging_dir_without_manifest(staging_dir)
    _make_dirs(staging_dir, exist_ok=False)
    lock_payload["staging_dir"] = str(staging_dir)
    _rewrite_task_lock(lock_path, lock_payload)

    manifest_path = staging_dir / "staging_manifest.json"
    manifest: dict[str, Any] = {
        "task_id": task_id,
        "output_owner_task_id": output_owner_task_id,
        "mode": mode,
        "created_at": _utc_now_z(),
        "targets": [],
    }
    restore_completed = False
    try:
        for index, target in enumerate(iter_official_output_targets(output_owner_task_id, source_plan, settings), start=1):
            _make_dirs(target.parent, exist_ok=True)
            original_existed = _path_exists(target)
            backup_path = _staging_backup_path(staging_dir, index, target)
            original_atime_ns = 0
            original_mtime_ns = 0
            if original_existed:
                stat = os.stat(_fs_path(target))
                original_atime_ns = stat.st_atime_ns
                original_mtime_ns = stat.st_mtime_ns
                _copy_file(target, backup_path)
            manifest["targets"].append(
                {
                    "target": str(target),
                    "backup_path": str(backup_path),
                    "original_existed": original_existed,
                    "original_atime_ns": original_atime_ns,
                    "original_mtime_ns": original_mtime_ns,
                }
            )
        _write_json(manifest_path, manifest)

        for entry in manifest["targets"]:
            _shared_write_text(Path(str(entry["target"])), candidate_code)

        success, output = _run_official_module_build(output_owner_task_id, settings)
        if not success or restore_on_success:
            restore_completed = _restore_staging_manifest(manifest_path)
            if not restore_completed:
                raise RuntimeError(
                    f"Phase 2 staging restore failed for {output_owner_task_id} after {mode}; manual recovery required."
                )
        else:
            _remove_tree(staging_dir)
            restore_completed = True
        return success, output
    finally:
        if restore_completed:
            _release_task_local_lock(lock_path)


def _set_latest_operation(task_id: str, ledger: LedgerManager, *, kind: str, file_path: str) -> None:
    ledger.update_runtime_metadata(
        task_id,
        latest_operation_kind=kind,
        latest_operation_file=file_path,
    )


def _sync_stale_build_ready_candidate(task_id: str, ledger: LedgerManager, settings, pack_dir: Path) -> bool:
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    if not isinstance(current_record, dict):
        return False
    if str(current_record.get("latest_build_ready_candidate_kind", "") or "") != "draft":
        return False
    ready_hash = str(current_record.get("latest_build_ready_candidate_hash", "") or "")
    if not ready_hash:
        return False
    draft_path = pack_dir / DRAFT_FILE_NAME
    draft_hash = _sha256_text(_read_file_safely(draft_path)) if _path_exists(draft_path) else ""
    if draft_hash == ready_hash:
        return False

    updates: dict[str, Any] = {
        "latest_build_ready_candidate_kind": "",
        "latest_build_ready_candidate_file": "",
        "latest_build_ready_candidate_hash": "",
    }
    if str(current_record.get("pack_candidate_state", "") or "") in {"build_ready", "review_pending", "review_rejected"}:
        updates["pack_candidate_state"] = "draft"
    ledger.update_runtime_metadata(task_id, **updates)
    return True


def _update_pack_candidate_state(task_id: str, ledger: LedgerManager, state: str) -> None:
    if state not in PACK_CANDIDATE_STATES:
        raise ValueError(f"unknown pack candidate state: {state}")
    ledger.update_runtime_metadata(task_id, pack_candidate_state=state)


def _semantic_diagnostic(kind: str, detail: str) -> list[dict[str, Any]]:
    return [
        {
            "stage": "candidate_semantics",
            "kind": kind,
            "message": detail,
            "line": None,
            "column": None,
            "blocking_symbols": [],
        }
    ]


def _hard_check_diagnostic(kind: str, detail: str) -> list[dict[str, Any]]:
    return [
        {
            "stage": "candidate_hard_checks",
            "kind": kind,
            "message": detail,
            "line": None,
            "column": None,
            "blocking_symbols": [],
        }
    ]


def _hard_check_diagnostic_with_symbols(kind: str, detail: str, symbols: list[str]) -> list[dict[str, Any]]:
    diagnostic = _hard_check_diagnostic(kind, detail)
    diagnostic[0]["blocking_symbols"] = canonicalize_id_list(symbols)
    return diagnostic


def _task_local_import_allowlist(task: dict[str, Any], ledger: LedgerManager | None = None) -> set[str]:
    allowed = set(canonicalize_id_list(task.get("dependencies", [])))
    allowed.update(canonicalize_id_list(task.get("soft_imports", [])))
    allowed.update(canonicalize_id_list(task.get("final_import_union", [])))
    if ledger is not None:
        record = ledger.ledger.get("tasks", {}).get(canonicalize_block_id(str(task.get("block_id", ""))), {})
        snapshot = record.get("candidate_snapshot", {}) if isinstance(record, dict) else {}
        if isinstance(snapshot, dict):
            allowed.update(canonicalize_id_list(snapshot.get("soft_imports", [])))
    expanded = set(allowed)
    for dep in list(allowed):
        expanded.update(legacy_ids_for(dep))
    return expanded


def _candidate_local_imports(candidate_code: str) -> list[str]:
    imports: list[str] = []
    for match in re.finditer(r"(?m)^\s*import\s+ToyApollo\.Output\.([A-Za-z0-9_']+)\s*$", candidate_code):
        dep = str(match.group(1) or "").strip().lower()
        if dep:
            imports.append(dep)
    return imports


def _task_like_local_imports(imported_modules: list[str]) -> list[str]:
    task_imports: list[str] = []
    for module in imported_modules:
        canonical = canonicalize_block_id(module)
        if not canonical:
            continue
        if module == canonical or module in legacy_ids_for(canonical) or is_canonical_block_id(module):
            task_imports.append(canonical)
    return task_imports


def validate_candidate_hard_checks(
    task: dict[str, Any],
    candidate_code: str,
    ledger: LedgerManager | None = None,
) -> tuple[bool, list[dict[str, Any]], str]:
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    target_task_ids = _hard_check_target_task_ids(task, ledger)
    target_task_id = target_task_ids[0] if target_task_ids else task_id
    if not candidate_code.strip():
        detail = "Candidate file is empty."
        return False, _hard_check_diagnostic("empty_candidate", detail), detail

    if re.search(r"(?m)^\s*sorry\b|\bsorry\b", candidate_code):
        detail = "Candidate contains `sorry`, so it is not a complete formalization."
        return False, _hard_check_diagnostic("contains_sorry", detail), detail

    if _candidate_uses_axiom(candidate_code):
        detail = "Candidate introduces a top-level axiom placeholder, so the result is not a real formalization."
        return False, _hard_check_diagnostic("axiom_placeholder", detail), detail

    exported_kind = None
    exported_target_task_id = target_task_id
    for candidate_target in target_task_ids:
        exported_kind = _candidate_decl_kind(candidate_target, candidate_code)
        if exported_kind is not None:
            exported_target_task_id = candidate_target
            break
    if exported_kind is None:
        rendered_targets = "`, `".join(target_task_ids)
        detail = (
            "Candidate does not declare the target task id "
            f"`{rendered_targets}` as a top-level def/theorem/lemma."
        )
        return False, _hard_check_diagnostic("missing_target_declaration", detail), detail

    imported_modules = _candidate_local_imports(candidate_code)
    self_import_names = set(target_task_ids)
    for candidate_target in target_task_ids:
        self_import_names.update(legacy_ids_for(candidate_target))
    if any(module in self_import_names for module in imported_modules):
        detail = f"Candidate self-imports ToyApollo.Output.{target_task_id}, which would bypass verification."
        return False, _hard_check_diagnostic("self_import", detail), detail

    imported = _task_like_local_imports(imported_modules)
    allowed_imports = _task_local_import_allowlist(task, ledger)
    undeclared = sorted([dep for dep in imported if dep not in allowed_imports])
    if undeclared:
        detail = "Candidate imports undeclared local outputs: " + ", ".join(undeclared) + "."
        return False, _hard_check_diagnostic_with_symbols("undeclared_local_import", detail, undeclared), detail

    task_type = str(task.get("type", "")).strip().lower()
    if ("theorem" in task_type or exported_target_task_id.startswith("thm_")) and exported_kind == "def":
        prop_def_re = re.compile(rf"(?ms)^\s*(?:noncomputable\s+)?def\s+{re.escape(exported_target_task_id)}\b.*?:\s*Prop\s*:=\s*")
        if prop_def_re.search(candidate_code):
            detail = "Theorem-like task exports only a Prop-valued definition instead of a theorem/lemma."
            return False, _hard_check_diagnostic("theorem_declared_as_prop_def", detail), detail

    return True, [], ""


def _hard_check_target_task_ids(task: dict[str, Any], ledger: LedgerManager | None = None) -> list[str]:
    task_id = canonicalize_block_id(str(task.get("block_id", "")))
    targets = [task_id] if task_id else []
    merged = dict(task)
    if ledger is not None:
        record = ledger.ledger.get("tasks", {}).get(task_id, {})
        if isinstance(record, dict):
            merged = dict(record)
            merged.update(task)
    if str(merged.get("type", "") or "") == "Phase2ObligationTask" and task_id.startswith("obl_"):
        focused_id = task_id.removeprefix("obl_")
        if focused_id and focused_id not in targets:
            targets.append(focused_id)
    return targets


def _is_vacuous_candidate(task: dict[str, Any], candidate_code: str) -> bool:
    guarded_types = {"theorem_statement", "theorem_with_proof", "example_proof"}
    task_type = str(task.get("type", "")).strip().lower()
    if task_type not in guarded_types:
        return False
    normalized = " ".join(candidate_code.split())
    if VACUOUS_THEOREM_RE.search(candidate_code):
        return True
    return ": True := by trivial" in normalized or ": True := by exact trivial" in normalized


def _source_requires_dimension_generality(task: dict[str, Any]) -> bool:
    source_text = f"{task.get('title', '')}\n{task.get('content', '')}"
    return RD_GENERALITY_CUE_RE.search(source_text) is not None


def _candidate_has_dimension_parameterization(candidate_code: str) -> bool:
    if GENERIC_DIMENSION_TOKENS_RE.search(candidate_code):
        return True
    normalized = " ".join(candidate_code.split())
    generic_tokens = (
        "Set (Fin ",
        "Fin d",
        "Fin n",
        "EuclideanSpace",
        "fun d :",
        "fun n :",
        "(d : Nat)",
        "(n : Nat)",
        "(d : ℕ)",
        "(n : ℕ)",
    )
    return any(token in normalized for token in generic_tokens)


def _is_overspecialized_candidate(task: dict[str, Any], candidate_code: str) -> bool:
    if not _source_requires_dimension_generality(task):
        return False
    if _candidate_has_dimension_parameterization(candidate_code):
        return False

    normalized = " ".join(candidate_code.split())
    fixed_specializations = (
        "ℝ × ℝ",
        "Set ℝ",
        "borel ℝ",
    )
    return any(token in normalized for token in fixed_specializations)

def _normalize_candidate(candidate_code: str) -> str:
    return " ".join(candidate_code.split())


def _candidate_wrapper_reference(candidate_code: str) -> bool:
    return re.search(r"\b(?:exact|apply)\s+(?:thm|def)_[A-Za-z0-9_']+", candidate_code) is not None or re.search(
        r"\bsimpa\b.*\busing\s+(?:thm|def)_[A-Za-z0-9_']+",
        candidate_code,
        re.DOTALL,
    ) is not None


def _candidate_assumes_independence(candidate_code: str) -> bool:
    assumption_pattern = re.compile(
        r"\([^)]+:\s*(?:ProbabilityTheory\.IndepFun|def_5_2)\b",
        re.MULTILINE,
    )
    return assumption_pattern.search(candidate_code) is not None


def _candidate_has_both_directions(candidate_code: str) -> bool:
    return any(token in candidate_code for token in ("↔", "<->", " Iff", ":= by\n  constructor", "constructor", ".mp", ".mpr"))


def _candidate_uses_all_measurable_generator_shortcut(candidate_code: str) -> bool:
    return re.search(r"∀\s+[A-Za-z0-9_']+,\s*MeasurableSet\s+[A-Za-z0-9_']+\s*→\s*[A-Za-z0-9_']+\s*∈\s*[A-Za-z0-9_']+", candidate_code) is not None


def _candidate_uses_axiom(candidate_code: str) -> bool:
    return re.search(r"(?m)^\s*axiom\b", candidate_code) is not None


def _candidate_decl_kind(task_id: str, candidate_code: str) -> str | None:
    pattern = re.compile(NAMED_DECL_RE_TEMPLATE.format(name=re.escape(task_id)))
    match = pattern.search(candidate_code)
    if not match:
        return None
    return str(match.group("kind"))


def _candidate_is_example_structure_wrapper(task_id: str, candidate_code: str) -> bool:
    exported_kind = _candidate_decl_kind(task_id, candidate_code)
    if exported_kind != "def":
        return False
    if re.search(r"(?m)^\s*structure\s+[A-Za-z0-9_']+\s+where\b", candidate_code) is None:
        return False
    alias_pattern = re.compile(rf"(?m)^\s*def\s+{re.escape(task_id)}\b[^\n]*:=\s*[A-Za-z0-9_']+\s*$")
    return alias_pattern.search(candidate_code) is not None


def _cue_matchers() -> dict[str, tuple[str, ...]]:
    return {
        "joint_gaussian_or_density_factorization": ("gaussian", "normal", "density", "haspdf", "joint density", "fxy", "pdf"),
        "explicit_density_factorization": ("exp", "sigma", "ρ", "rho", "2 * real.pi", "sqrt (2", "hpdffactorization"),
        "zero_correlation": ("corr", "covariance", "cov", "uncorrelated", "correlation"),
        "independence_conclusion": ("def_5_2", "indepfun", "independent"),
        "counterexample_construction": ("density", "sample", "finite", "event", "events", "ω", "omega", "fin ", "set "),
        "explicit_joint_density_formula": ("1 / 4", "1 + x * y", "1 + x*y", "[-1,1]", "set.icc (-1) 1", "hjointdensityformula"),
        "dependence_of_original_objects": ("¬", "not independent", "dependent"),
        "independence_of_transforms": ("def_5_2", "indepfun", "fun ω =>", "^2", "* x", "* y"),
        "square_cdf_factorization": ("sqrt", "^2", "jointcdf", "marginalcdf", "hsquarefactorization"),
        "pairwise_not_mutual_gap": ("pairwise", "mutually", "1/4", "1/8", "product"),
        "generator_family": ("generatefrom", "pi", "π", "lambda", "λ", "dynkin", "generator"),
        "extension_argument": ("generatefrom", "pi", "π", "lambda", "λ", "dynkin", "m_iunion", "iunion"),
        "both_directions": ("↔", "<->", " iff", " if and only if ", "constructor", ".mp", ".mpr"),
        "open_balls_generation": ("metric.ball", "emetric.ball", " ball", "(ball", "{ball"),
        "cantor_distribution_construction": ("cantor", "distribution", "series", "∑", "random", "ternary"),
        "cdf_or_probability_property": ("measure", "probability", "cdf", "distribution", " μ ", " P("),
        "cantor_set_conclusion": ("cantorset", "cantor", "≃", "equiv", "nonempty", "uncountable"),
    }


def _missing_required_cues(contract: dict[str, Any], candidate_code: str) -> list[str]:
    normalized = _normalize_candidate(candidate_code).lower()
    missing: list[str] = []
    for cue in contract.get("required_cues", []):
        patterns = _cue_matchers().get(str(cue), ())
        if not patterns:
            continue
        if not any(pattern.lower() in normalized for pattern in patterns):
            missing.append(str(cue))
    return missing


def _unused_prop_placeholders(candidate_code: str) -> list[str]:
    placeholders = re.findall(r"\((h[A-Za-z0-9_']+)\s*:\s*Prop\)", candidate_code)
    unused: list[str] = []
    for name in placeholders:
        count = len(re.findall(rf"\b{re.escape(name)}\b", candidate_code))
        if count <= 1:
            unused.append(name)
    return unused


def _missing_explicit_source_construction(contract: dict[str, Any], candidate_code: str) -> tuple[list[str], list[str]]:
    required = set(str(value) for value in contract.get("required_cues", []))
    explicit_cues = [
        cue
        for cue in ("explicit_density_factorization", "explicit_joint_density_formula", "square_cdf_factorization")
        if cue in required
    ]
    if not explicit_cues:
        return [], []

    missing = [cue for cue in _missing_required_cues(contract, candidate_code) if cue in explicit_cues]
    unused_placeholders = _unused_prop_placeholders(candidate_code)
    relevant_unused: list[str] = []
    for name in unused_placeholders:
        lowered = name.lower()
        if "explicit_density_factorization" in explicit_cues and any(
            token in lowered for token in ("density", "gaussian", "correlation", "pdf")
        ):
            relevant_unused.append(name)
            continue
        if "explicit_joint_density_formula" in explicit_cues and "density" in lowered:
            relevant_unused.append(name)
            continue
        if "square_cdf_factorization" in explicit_cues and any(
            token in lowered for token in ("square", "factor", "cdf")
        ):
            relevant_unused.append(name)
    return _dedupe_strings(missing), _dedupe_strings(relevant_unused)


def validate_legacy_candidate_semantics(
    task: dict[str, Any],
    candidate_code: str,
    intent_contract: dict[str, Any] | None = None,
) -> tuple[bool, list[dict[str, Any]], str]:
    contract = intent_contract or build_legacy_intent_contract(task)
    task_id = canonicalize_block_id(str(task.get("block_id", "")))

    if _candidate_uses_axiom(candidate_code):
        detail = "Candidate introduces a top-level axiom placeholder, so the audited result is not a real formalization."
        return False, _semantic_diagnostic("axiom_placeholder", detail), detail

    if _is_vacuous_candidate(task, candidate_code):
        detail = "Candidate is vacuous: the exported theorem/example collapses to a trivial proposition instead of the textbook mathematical content."
        return False, _semantic_diagnostic("vacuous_candidate", detail), detail

    if _is_overspecialized_candidate(task, candidate_code):
        detail = "Candidate is overspecialized: the textbook task requires an R^d / d-dimensional statement, but the Lean candidate only encodes a fixed low-dimensional special case."
        return False, _semantic_diagnostic("overspecialized_candidate", detail), detail

    task_role = str(contract.get("task_role", ""))
    exported_kind = _candidate_decl_kind(task_id, candidate_code)
    if task_role in {"theorem", "generator_theorem", "iff_theorem"} and exported_kind == "def":
        detail = "Candidate encodes the target theorem as a definition or proposition alias instead of proving a theorem statement."
        return False, _semantic_diagnostic("theorem_declared_as_definition", detail), detail

    if task_role in {"example", "counterexample_example", "analytic_example"} and _candidate_is_example_structure_wrapper(task_id, candidate_code):
        detail = "Candidate reduces the textbook example to a structure wrapper placeholder instead of formalizing the example's mathematical construction."
        return False, _semantic_diagnostic("example_structure_wrapper", detail), detail

    if task_role in {"example", "counterexample_example", "analytic_example"} and _candidate_wrapper_reference(candidate_code):
        missing = _missing_required_cues(contract, candidate_code)
        if missing:
            detail = (
                "Candidate wraps an existing theorem/definition instead of preserving the textbook example's own construction or assumptions. "
                f"Missing cues: {', '.join(missing)}."
            )
            return False, _semantic_diagnostic("example_wrapped_theorem", detail), detail

    must_not_assume = set(contract.get("must_not_assume", []))
    if "original_independence" in must_not_assume and _candidate_assumes_independence(candidate_code):
        detail = "Candidate assumes original independence even though the source example is a counterexample where the original objects must remain dependent."
        return False, _semantic_diagnostic("reversed_example_logic", detail), detail
    if "independence_up_front" in must_not_assume and _candidate_assumes_independence(candidate_code):
        detail = "Candidate assumes the target independence conclusion up front; the source example requires deriving independence from analytic hypotheses such as Gaussian structure or zero correlation."
        return False, _semantic_diagnostic("reversed_example_logic", detail), detail

    missing_explicit, unused_placeholders = _missing_explicit_source_construction(contract, candidate_code)
    if missing_explicit or unused_placeholders:
        detail_parts: list[str] = []
        if "explicit_density_factorization" in missing_explicit:
            detail_parts.append("the Gaussian density factorization from the source example is not explicitly reflected")
        if "explicit_joint_density_formula" in missing_explicit:
            detail_parts.append("the source joint density formula is not explicitly reflected")
        if "square_cdf_factorization" in missing_explicit:
            detail_parts.append("the square-transform CDF factorization from the source example is not explicitly reflected")
        if unused_placeholders:
            detail_parts.append("placeholder Prop assumptions are present but unused: " + ", ".join(unused_placeholders))
        detail = "Candidate does not preserve the source example's explicit construction: " + "; ".join(detail_parts) + "."
        return False, _semantic_diagnostic("missing_explicit_source_construction", detail), detail

    if task_role == "generator_theorem" and _candidate_uses_all_measurable_generator_shortcut(candidate_code):
        detail = "Candidate weakens the generator theorem by assuming every measurable set already belongs to the generating family, which removes the required extension argument."
        return False, _semantic_diagnostic("weakened_statement", detail), detail
    if task_role == "iff_theorem" and not _candidate_has_both_directions(candidate_code):
        detail = "Candidate weakens an iff-style textbook theorem to a single direction, so the hard converse direction is missing."
        return False, _semantic_diagnostic("weakened_statement", detail), detail

    missing = _missing_required_cues(contract, candidate_code)
    if missing:
        detail = "Candidate does not cover all required textbook content. Missing cues: " + ", ".join(missing) + "."
        return False, _semantic_diagnostic("missing_required_coverage", detail), detail

    return True, [], ""


# Compatibility aliases for existing callers and tests. The underlying
# heuristic is legacy advisory/regression code, not the semantic promotion gate.
build_intent_contract = build_legacy_intent_contract
validate_candidate_semantics = validate_legacy_candidate_semantics


def find_existing_task_file(task_id: str, source_plan: str, settings) -> Path | None:
    for candidate in iter_official_output_targets(task_id, source_plan, settings):
        if candidate.exists():
            return candidate
    return None


def build_target_stub(task: dict[str, Any], import_lines: list[str], existing_code: str | None = None) -> str:
    header = extract_declaration_stub(existing_code or "")
    comment_block = "\n".join(
        [
            "/-",
            f"TASK ID: {task['block_id']}",
            f"TYPE: {task.get('type', 'Unknown')}",
            f"SOURCE PLAN: {task.get('source_plan', 'unknown')}",
            "TASK CONTENT:",
            task.get("content", "").strip() or "(no content)",
            "-/",
            "",
        ]
    )
    lines = import_lines + ["", comment_block]
    if header:
        lines.extend([header, "  := by", "    sorry"])
    else:
        lines.append("-- WRITE FINAL LEAN CODE BELOW")
    return "\n".join(lines).strip() + "\n"


def build_obligation_target_stub(existing_code: str | None, fallback_stub: str) -> str:
    existing = (existing_code or "").strip()
    if existing and has_top_level_declaration(existing):
        return existing + "\n"
    return fallback_stub


def _read_file_safely(path: Path) -> str:
    return _shared_read_file_safely(path)


def _read_json_safely(path: Path, default: Any) -> Any:
    return _shared_read_json_safely(path, default)


def _write_json(path: Path, payload: Any) -> None:
    _shared_write_json(path, payload)


def _build_semantic_review_request(
    *,
    task_id: str,
    origin: str,
    attempt: int,
    review_subject_kind: str,
    review_subject_file: str,
    review_subject_hash: str,
    review_basis_hash: str,
    review_input_hash: str,
    review_input_file: str,
    review_prompt_file: str,
    review_context_file: str,
    review_result_template_file: str,
    expected_result_file: str,
    reviewer_backend_id: str,
    prompt_version: int,
    rubric_version: int,
) -> dict[str, Any]:
    from .phase2_review_request import _build_semantic_review_request as _owner_build_semantic_review_request

    return _owner_build_semantic_review_request(
        task_id=task_id,
        origin=origin,
        attempt=attempt,
        review_subject_kind=review_subject_kind,
        review_subject_file=review_subject_file,
        review_subject_hash=review_subject_hash,
        review_basis_hash=review_basis_hash,
        review_input_hash=review_input_hash,
        review_input_file=review_input_file,
        review_prompt_file=review_prompt_file,
        review_context_file=review_context_file,
        review_result_template_file=review_result_template_file,
        expected_result_file=expected_result_file,
        reviewer_backend_id=reviewer_backend_id,
        prompt_version=prompt_version,
        rubric_version=rubric_version,
    )
    return {
        "schema_version": "phase2.semantic_review.request.v1",
        "task_id": task_id,
        "origin": origin,
        "attempt": attempt,
        "review_subject_kind": review_subject_kind,
        "review_subject_file": review_subject_file,
        "review_subject_hash": review_subject_hash,
        "review_basis_hash": review_basis_hash,
        "review_input_file": review_input_file,
        "review_prompt_file": review_prompt_file,
        "review_context_file": review_context_file,
        "review_result_template_file": review_result_template_file,
        "expected_result_file": expected_result_file,
        "reviewer_backend_id": reviewer_backend_id,
        "prompt_version": prompt_version,
        "rubric_version": rubric_version,
    }


def _clear_current_review_metadata(task_id: str, ledger: LedgerManager) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_input_file="",
        current_review_prompt_file="",
        current_review_template_file="",
        current_review_context_file="",
        current_review_request_file="",
        current_review_backend_id="",
        current_review_expected_result_file="",
        current_review_subject_kind="",
        current_review_subject_file="",
        current_review_subject_hash="",
        current_review_origin="",
    )


def _set_current_review_metadata(
    task_id: str,
    ledger: LedgerManager,
    *,
    input_file: str,
    prompt_file: str,
    template_file: str,
    context_file: str,
    request_file: str,
    backend_id: str,
    expected_result_file: str,
    subject_kind: str,
    subject_file: str,
    subject_hash: str,
    origin: str,
) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_input_file=input_file,
        current_review_prompt_file=prompt_file,
        current_review_template_file=template_file,
        current_review_context_file=context_file,
        current_review_request_file=request_file,
        current_review_backend_id=backend_id,
        current_review_expected_result_file=expected_result_file,
        current_review_subject_kind=subject_kind,
        current_review_subject_file=subject_file,
        current_review_subject_hash=subject_hash,
        current_review_origin=origin,
    )


def _clear_current_review_repair_metadata(task_id: str, ledger: LedgerManager) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_repair_request_file="",
        current_review_repair_summary_file="",
        current_review_repair_seed_file="",
        current_review_repair_origin_result_file="",
        current_review_repair_archive_file="",
    )


def _set_current_review_repair_metadata(
    task_id: str,
    ledger: LedgerManager,
    *,
    request_file: str,
    summary_file: str,
    seed_file: str,
    origin_result_file: str,
    archive_file: str = "",
) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_repair_request_file=request_file,
        current_review_repair_summary_file=summary_file,
        current_review_repair_seed_file=seed_file,
        current_review_repair_origin_result_file=origin_result_file,
        current_review_repair_archive_file=archive_file,
    )


def _load_attempt_history(pack_dir: Path, task_id: str) -> dict[str, Any]:
    default = {"task_id": task_id, "attempts": []}
    payload = _read_json_safely(pack_dir / ATTEMPT_HISTORY_FILE_NAME, default)
    if not isinstance(payload, dict):
        return default
    attempts = payload.get("attempts", [])
    if not isinstance(attempts, list):
        attempts = []
    payload["task_id"] = str(payload.get("task_id") or task_id)
    payload["attempts"] = attempts
    return payload


def _latest_attempt_summary(history: dict[str, Any]) -> dict[str, Any] | None:
    attempts = history.get("attempts", [])
    if not attempts:
        return None
    latest = attempts[-1]
    return latest if isinstance(latest, dict) else None




def _derive_import_from_mathlib_path(mathlib_root: Path, file_path: Path) -> str:
    rel = file_path.relative_to(mathlib_root.parent)
    return ".".join(rel.with_suffix("").parts)


def _derive_import_from_runtime_path(runtime_root: Path, file_path: Path) -> str:
    rel = file_path.relative_to(runtime_root)
    return ".".join(rel.with_suffix("").parts)


def _extract_decl_name(text: str) -> str:
    match = re.search(r"(?:theorem|def|lemma)\s+([A-Za-z0-9_']+)", text)
    return match.group(1) if match else ""


def determine_mathlib_search_roots(task: dict[str, Any], mathlib_root: Path) -> list[Path]:
    source_plan = str(task.get("source_plan", "") or "")
    prioritized: list[Path] = []

    def add_root(path: Path) -> None:
        if path not in prioritized and path.exists():
            prioritized.append(path)

    if source_plan.startswith(CHAPTER5_SOURCE_PREFIXES):
        add_root(mathlib_root / "Probability")
        add_root(mathlib_root / "MeasureTheory")
        add_root(mathlib_root / "Analysis")

    add_root(mathlib_root)
    return prioritized


def _describe_mathlib_root(mathlib_root: Path, root: Path) -> str:
    if root == mathlib_root:
        return "Mathlib"
    try:
        rel = root.relative_to(mathlib_root)
    except ValueError:
        return root.name or str(root)
    return rel.as_posix() or "Mathlib"


def _iter_lean_files(root: Path, file_cache: dict[Path, list[Path]] | None = None) -> list[Path]:
    if file_cache is not None and root in file_cache:
        return file_cache[root]
    files = list(root.rglob("*.lean"))
    if file_cache is not None:
        file_cache[root] = files
    return files


def _python_search_files(
    root: Path,
    term: str,
    max_results: int = 5,
    file_cache: dict[Path, list[Path]] | None = None,
) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    lowered = term.lower()
    for file_path in _iter_lean_files(root, file_cache):
        try:
            content = file_path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        idx = content.lower().find(lowered)
        if idx < 0:
            continue
        line_no = content.count("\n", 0, idx) + 1
        lines = content.splitlines()
        line = lines[line_no - 1] if line_no - 1 < len(lines) else ""
        results.append(
            {
                "path": str(file_path),
                "line_no": line_no,
                "line": line.strip(),
                "snippet": content[max(0, idx - 180): idx + 420].strip(),
            }
        )
        if len(results) >= max_results:
            break
    return results


def _search_with_rg(root: Path, term: str, max_results: int = 5) -> list[dict[str, Any]]:
    try:
        proc = subprocess.run(
            ["rg", "-n", "-F", "-m", str(max_results), "--glob", "*.lean", term, str(root)],
            capture_output=True,
            text=True,
            check=False,
        )
    except Exception:
        return []

    if proc.returncode not in (0, 1):
        return []

    results: list[dict[str, str]] = []
    for raw_line in proc.stdout.splitlines():
        match = re.match(r"^(.*):(\d+):(.*)$", raw_line)
        if not match:
            continue
        path_str, line_no, line_text = match.groups()
        file_path = Path(path_str)
        content = _read_file_safely(file_path)
        idx = content.find(line_text.strip())
        snippet = content[max(0, idx - 180): idx + 420].strip() if idx >= 0 else line_text.strip()
        results.append(
            {
                "path": path_str,
                "line_no": int(line_no),
                "line": line_text.strip(),
                "snippet": snippet,
            }
        )
    return results[:max_results]


def _search_top_level_decls(
    root: Path,
    term: str,
    max_results: int = 5,
    file_cache: dict[Path, list[Path]] | None = None,
) -> list[dict[str, Any]]:
    if not IDENTIFIER_RE.match(term):
        return []
    candidates = [term, f"{term}'", f"{term}''"]
    pattern = re.compile(
        rf"^\s*(?:noncomputable\s+)?(?:theorem|def|lemma)\s+({'|'.join(re.escape(c) for c in candidates)})\b",
        re.MULTILINE,
    )
    rg_pattern = (
        r"^\s*(?:noncomputable\s+)?(?:theorem|def|lemma)\s+"
        rf"({'|'.join(re.escape(c) for c in candidates)})\b"
    )
    try:
        proc = subprocess.run(
            ["rg", "-n", "--glob", "*.lean", rg_pattern, str(root)],
            capture_output=True,
            text=True,
            check=False,
        )
    except Exception:
        proc = None

    if proc is not None and proc.returncode in (0, 1):
        results: list[dict[str, Any]] = []
        for raw_line in proc.stdout.splitlines():
            match = re.match(r"^(.*):(\d+):(.*)$", raw_line)
            if not match:
                continue
            path_str, line_no, line_text = match.groups()
            file_path = Path(path_str)
            content = _read_file_safely(file_path)
            idx = content.find(line_text.strip())
            snippet = content[max(0, idx - 180): idx + 420].strip() if idx >= 0 else line_text.strip()
            results.append(
                {
                    "path": path_str,
                    "line_no": int(line_no),
                    "line": line_text.strip(),
                    "snippet": snippet,
                }
            )
            if len(results) >= max_results:
                return results
        if results:
            return results
        return []

    results: list[dict[str, Any]] = []
    for file_path in _iter_lean_files(root, file_cache):
        try:
            content = file_path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        for match in pattern.finditer(content):
            line_no = content.count("\n", 0, match.start()) + 1
            lines = content.splitlines()
            line = lines[line_no - 1] if line_no - 1 < len(lines) else ""
            results.append(
                {
                    "path": str(file_path),
                    "line_no": line_no,
                    "line": line.strip(),
                    "snippet": content[max(0, match.start() - 180): match.start() + 420].strip(),
                }
            )
            if len(results) >= max_results:
                return results
    return results


def _run_check_with_import(
    compiler: LeanCompiler,
    import_path: str,
    symbol: str,
    search_stats: dict[str, Any] | None = None,
) -> tuple[bool, str]:
    if search_stats is not None:
        search_stats["check_attempts"] = int(search_stats.get("check_attempts", 0)) + 1
    response = compiler.run_repl_command(f"import {import_path}\n#check {symbol}")
    messages = response.get("messages", []) if isinstance(response, dict) else []
    rendered: list[str] = []
    success = True
    for message in messages:
        severity = message.get("severity", "")
        data = str(message.get("data", "")).strip()
        if not data:
            continue
        if severity == "error":
            success = False
        rendered.append(f"[{severity}] {data}")
    if isinstance(response, dict) and response.get("error"):
        success = False
        rendered.append(f"[error] {response['error']}")
    return success, "\n".join(rendered).strip() or "(no REPL output)"


def _build_search_manifest_entry(
    *,
    term: str,
    source_kind: str,
    import_path: str,
    symbol: str,
    file_path: str,
    line: int | None,
    snippet: str,
    check_success: bool,
    check_output: str,
    status: str,
    source_line: str = "",
    reason: str = "",
) -> dict[str, Any]:
    return {
        "term": term,
        "source_kind": source_kind,
        "import_path": import_path,
        "symbol": symbol,
        "file_path": file_path,
        "line": line,
        "snippet": snippet,
        "source_line": source_line,
        "check_success": check_success,
        "check_output": check_output,
        "status": status,
        "reason": reason,
    }


def _dedupe_manifest_entries(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str, str, str, int | None]] = set()
    deduped: list[dict[str, Any]] = []
    for entry in entries:
        key = (
            str(entry.get("source_kind", "")),
            str(entry.get("import_path", "")),
            str(entry.get("symbol", "")),
            str(entry.get("file_path", "")),
            entry.get("line"),
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append(entry)
    return deduped


def _collect_local_dependency_entries(
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    compiler: LeanCompiler,
    search_stats: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    final_union = canonicalize_id_list(hard_deps + soft_imports)
    entries: list[dict[str, Any]] = []
    try:
        symbol_check_limit = max(
            0,
            int(os.getenv("TOY_APOLLO_DEP_SYMBOL_CHECK_LIMIT", str(DEFAULT_DEPENDENCY_SYMBOL_CHECK_LIMIT))),
        )
    except ValueError:
        symbol_check_limit = DEFAULT_DEPENDENCY_SYMBOL_CHECK_LIMIT
    for dep in final_union:
        dep_id = canonicalize_block_id(dep)
        dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
        dep_file = find_existing_task_file(dep_id, dep_record.get("source_plan", "unknown"), settings)
        import_path = f"ToyApollo.Output.{dep_id}"
        exported = dep_record.get("exported_symbols", [])
        symbols = exported if exported else [dep_id]
        skipped_symbol_count = max(0, len(symbols) - symbol_check_limit)
        snippet = _read_file_safely(dep_file)[:600].strip() if dep_file else ""
        for symbol in symbols[:symbol_check_limit]:
            check_success, check_output = _run_check_with_import(compiler, import_path, symbol, search_stats=search_stats)
            entries.append(
                _build_search_manifest_entry(
                    term=symbol,
                    source_kind="local_dependency",
                    import_path=import_path,
                    symbol=symbol,
                    file_path=str(dep_file) if dep_file else "",
                    line=None,
                    snippet=snippet,
                    source_line="",
                    check_success=check_success,
                    check_output=check_output,
                    status="verified" if check_success else "rejected",
                    reason="dependency_export" if exported else "dependency_module",
                )
            )
        if skipped_symbol_count:
            entries.append(
                _build_search_manifest_entry(
                    term=dep_id,
                    source_kind="local_dependency",
                    import_path=import_path,
                    symbol="",
                    file_path=str(dep_file) if dep_file else "",
                    line=None,
                    snippet=snippet,
                    source_line="",
                    check_success=False,
                    check_output=(
                        f"Skipped {skipped_symbol_count} exported dependency symbols during pack generation "
                        f"after checking the first {symbol_check_limit}; set "
                        "TOY_APOLLO_DEP_SYMBOL_CHECK_LIMIT to override."
                    ),
                    status="unverified",
                    reason="dependency_symbol_check_budget",
                )
            )
    return entries


def _collect_text_search_entries(
    *,
    root: Path,
    term: str,
    source_kind: str,
    import_builder,
    compiler: LeanCompiler,
    max_results: int = 3,
    file_cache: dict[Path, list[Path]] | None = None,
    search_stats: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    hits = _search_top_level_decls(root, term, max_results=max_results, file_cache=file_cache)
    if not hits:
        hits = _search_with_rg(root, term, max_results=max_results)
    if not hits:
        hits = _python_search_files(root, term, max_results=max_results, file_cache=file_cache)

    entries: list[dict[str, Any]] = []
    for hit in hits:
        file_path = Path(str(hit.get("path", "")))
        import_path = import_builder(file_path)
        symbol = _extract_decl_name(str(hit.get("snippet", "") or hit.get("line", "")))
        if symbol:
            check_success = False
            check_output = "REPL verification skipped for text search hit during pack generation."
            status = "unverified"
            reason = "text_hit_only"
        else:
            check_success = False
            check_output = "No stable declaration name could be extracted for #check."
            status = "rejected"
            reason = "missing_symbol"

        entries.append(
            _build_search_manifest_entry(
                term=term,
                source_kind=source_kind,
                import_path=import_path,
                symbol=symbol,
                file_path=str(file_path),
                line=hit.get("line_no"),
                snippet=str(hit.get("snippet", "")),
                source_line=str(hit.get("line", "")),
                check_success=check_success,
                check_output=check_output,
                status=status,
                reason=reason,
            )
        )
    return entries


def _collect_optional_faiss_entries(
    *,
    term: str,
    task: dict[str, Any],
    settings,
    compiler: LeanCompiler,
    search_stats: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    if os.getenv("TOY_APOLLO_ENABLE_FAISS", "").strip() != "1":
        return []
    if not settings.mathlib_index_file.exists() or not settings.mathlib_corpus_file.exists():
        return []
    try:
        from src.searcher import MathlibSearcher
    except Exception:
        return []

    try:
        searcher = MathlibSearcher(
            lib_root_dir=str(settings.mathlib_path),
            local_output_dir=str(settings.toyapollo_output_dir),
        )
        hits = searcher.search(
            {"keywords": [term], "signatures": [], "paths": [], "aliases": []},
            task.get("content", ""),
            top_k=2,
            rerank=False,
        )
    except Exception:
        return []

    entries: list[dict[str, Any]] = []
    for hit in hits:
        path_str = str(hit.get("path", ""))
        if not path_str:
            continue
        file_path = Path(path_str)
        if not file_path.exists():
            continue
        try:
            if hit.get("is_local"):
                import_path = _derive_import_from_runtime_path(settings.runtime_root, file_path)
                source_kind = "local_faiss"
            else:
                import_path = _derive_import_from_mathlib_path(settings.mathlib_path, file_path)
                source_kind = "mathlib_faiss"
        except Exception:
            continue

        symbol = term if IDENTIFIER_RE.match(term) else _extract_decl_name(str(hit.get("content", "")))
        if symbol:
            check_success, check_output = _run_check_with_import(compiler, import_path, symbol, search_stats=search_stats)
            status = "verified" if check_success else "rejected"
            reason = "verified_by_check" if check_success else "check_failed"
        else:
            check_success = False
            check_output = "No stable declaration name could be extracted for #check."
            status = "rejected"
            reason = "missing_symbol"

        entries.append(
            _build_search_manifest_entry(
                term=term,
                source_kind=source_kind,
                import_path=import_path,
                symbol=symbol,
                file_path=str(file_path),
                line=None,
                snippet=str(hit.get("content", ""))[:800],
                source_line="",
                check_success=check_success,
                check_output=check_output,
                status=status,
                reason=reason,
            )
        )
    return entries


def build_search_manifest(task: dict[str, Any], ledger: LedgerManager, settings) -> dict[str, Any]:
    started = time.perf_counter()
    compiler = LeanCompiler(root_dir=str(settings.runtime_root))
    mathlib_root = settings.mathlib_path
    local_root = settings.toyapollo_output_dir
    terms = extract_search_terms(task.get("title", ""), task.get("content", ""))
    entries: list[dict[str, Any]] = []
    file_cache: dict[Path, list[Path]] = {}
    search_stats: dict[str, Any] = {"check_attempts": 0}
    roots_searched: list[str] = []
    timings_ms: dict[str, float] = {
        "local_dependency_ms": 0.0,
        "scoped_mathlib_ms": 0.0,
        "full_mathlib_ms": 0.0,
        "local_project_ms": 0.0,
        "faiss_ms": 0.0,
        "dedupe_ms": 0.0,
    }

    def record_root(label: str) -> None:
        if label not in roots_searched:
            roots_searched.append(label)

    local_dependency_started = time.perf_counter()
    entries.extend(_collect_local_dependency_entries(task, ledger, settings, compiler, search_stats=search_stats))
    timings_ms["local_dependency_ms"] += (time.perf_counter() - local_dependency_started) * 1000
    mathlib_roots = determine_mathlib_search_roots(task, mathlib_root)
    scoped_mathlib_roots = [root for root in mathlib_roots if root != mathlib_root]
    scoped_verified_any = False
    for term in terms:
        term_entries: list[dict[str, Any]] = []
        for root in scoped_mathlib_roots:
            record_root(_describe_mathlib_root(mathlib_root, root))
            scoped_started = time.perf_counter()
            term_entries.extend(
                _collect_text_search_entries(
                    root=root,
                    term=term,
                    source_kind="mathlib",
                    import_builder=lambda file_path: _derive_import_from_mathlib_path(mathlib_root, file_path),
                    compiler=compiler,
                    file_cache=file_cache,
                    search_stats=search_stats,
                )
            )
            timings_ms["scoped_mathlib_ms"] += (time.perf_counter() - scoped_started) * 1000
        if any(entry.get("status") == "verified" for entry in term_entries):
            scoped_verified_any = True
        entries.extend(term_entries)
        if local_root.exists():
            record_root("ToyApollo.Output")
            local_project_started = time.perf_counter()
            entries.extend(
                _collect_text_search_entries(
                    root=local_root,
                    term=term,
                    source_kind="local_project",
                    import_builder=lambda file_path: _derive_import_from_runtime_path(settings.runtime_root, file_path),
                    compiler=compiler,
                    file_cache=file_cache,
                    search_stats=search_stats,
                )
            )
            timings_ms["local_project_ms"] += (time.perf_counter() - local_project_started) * 1000

    if not scoped_mathlib_roots or not scoped_verified_any:
        record_root(_describe_mathlib_root(mathlib_root, mathlib_root))
        full_mathlib_started = time.perf_counter()
        for term in terms:
            entries.extend(
                _collect_text_search_entries(
                    root=mathlib_root,
                    term=term,
                    source_kind="mathlib",
                    import_builder=lambda file_path: _derive_import_from_mathlib_path(mathlib_root, file_path),
                    compiler=compiler,
                    file_cache=file_cache,
                    search_stats=search_stats,
                )
            )
        timings_ms["full_mathlib_ms"] += (time.perf_counter() - full_mathlib_started) * 1000

    dedupe_started = time.perf_counter()
    entries = _dedupe_manifest_entries(entries)
    timings_ms["dedupe_ms"] += (time.perf_counter() - dedupe_started) * 1000
    for term in terms:
        term_verified = any(entry.get("status") == "verified" for entry in entries if entry.get("term") == term)
        if not term_verified:
            faiss_started = time.perf_counter()
            faiss_entries = _collect_optional_faiss_entries(
                term=term,
                task=task,
                settings=settings,
                compiler=compiler,
                search_stats=search_stats,
            )
            if faiss_entries:
                if any(entry.get("source_kind") == "mathlib_faiss" for entry in faiss_entries):
                    record_root("FAISS:Mathlib")
                if any(entry.get("source_kind") == "local_faiss" for entry in faiss_entries):
                    record_root("FAISS:Local")
                entries.extend(faiss_entries)
            timings_ms["faiss_ms"] += (time.perf_counter() - faiss_started) * 1000

    dedupe_started = time.perf_counter()
    entries = _dedupe_manifest_entries(entries)
    timings_ms["dedupe_ms"] += (time.perf_counter() - dedupe_started) * 1000
    total_search_ms = int((time.perf_counter() - started) * 1000)
    return {
        "task_id": task["block_id"],
        "generated_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "search_terms": terms,
        "term_count": len(terms),
        "roots_searched": roots_searched,
        "check_attempts": int(search_stats.get("check_attempts", 0)),
        "search_time_ms": total_search_ms,
        "timings_ms": {key: int(value) for key, value in timings_ms.items()},
        "verified_count": sum(1 for entry in entries if entry.get("status") == "verified"),
        "unverified_count": sum(1 for entry in entries if entry.get("status") == "unverified"),
        "rejected_count": sum(1 for entry in entries if entry.get("status") == "rejected"),
        "entries": entries,
    }


def build_search_notes(task: dict[str, Any], ledger: LedgerManager, settings, search_manifest: dict[str, Any]) -> str:
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    final_union = canonicalize_id_list(hard_deps + soft_imports)

    lines = [
        f"# Search Notes for {task['block_id']}",
        "",
        "## Search Terms",
        "",
    ]
    terms = search_manifest.get("search_terms", [])
    if terms:
        for term in terms:
            lines.append(f"- `{term}`")
    else:
        lines.append("- (no terms extracted)")

    lines.extend(["", "## Local Dependency Facts", ""])
    if not final_union:
        lines.append("- No hard or soft dependencies.")
    else:
        for dep in final_union:
            dep_id = canonicalize_block_id(dep)
            dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
            dep_file = find_existing_task_file(dep_id, dep_record.get("source_plan", "unknown"), settings)
            dep_code = _read_file_safely(dep_file) if dep_file else ""
            lines.append(f"### `{dep_id}`")
            exported = dep_record.get("exported_symbols", [])
            lines.append(f"- Exported symbols: `{', '.join(exported) if exported else '(none recorded)'}`")
            lines.append(f"- File: `{dep_file}`" if dep_file else "- File: `(not found)`")
            if dep_code:
                lines.extend(["", "```lean", dep_code[:1000].strip(), "```", ""])
            else:
                lines.append("")

    verified = [entry for entry in search_manifest.get("entries", []) if entry.get("status") == "verified"]
    unverified = [entry for entry in search_manifest.get("entries", []) if entry.get("status") == "unverified"]
    rejected = [entry for entry in search_manifest.get("entries", []) if entry.get("status") == "rejected"]

    lines.extend(["## Verified Grounding Hits", ""])
    if not verified:
        lines.append("- No verified hits found.")
    else:
        for entry in verified:
            lines.append(
                f"- `{entry.get('term', '')}` -> `{entry.get('import_path', '')}` / `{entry.get('symbol', '') or '(no symbol)'}`"
            )
            if entry.get("line") is not None:
                lines.append(f"  - line `{entry['line']}`")
            if entry.get("source_line"):
                lines.append(f"  - Source line: `{entry['source_line']}`")
            if entry.get("snippet"):
                lines.append("  - Snippet:")
                lines.append("```lean")
                lines.append(str(entry["snippet"]).strip())
                lines.append("```")
            if entry.get("check_output"):
                lines.append("  - `#check` result:")
                lines.append("```text")
                lines.append(str(entry["check_output"]).strip())
                lines.append("```")

    lines.extend(["", "## Unverified Grounding Hits", ""])
    if not unverified:
        lines.append("- No unverified hits.")
    else:
        for entry in unverified:
            lines.append(
                f"- `{entry.get('term', '')}` -> `{entry.get('import_path', '')}` / `{entry.get('symbol', '') or '(no symbol)'}`"
            )
            lines.append(f"  - reason: `{entry.get('reason', 'unknown')}`")
            if entry.get("source_line"):
                lines.append(f"  - Source line: `{entry['source_line']}`")
            if entry.get("snippet"):
                lines.append("  - Snippet:")
                lines.append("```lean")
                lines.append(str(entry["snippet"]).strip())
                lines.append("```")

    lines.extend(["", "## Rejected Hits", ""])
    if not rejected:
        lines.append("- No rejected hits.")
    else:
        for entry in rejected:
            lines.append(
                f"- `{entry.get('term', '')}` -> `{entry.get('import_path', '')}` / `{entry.get('symbol', '') or '(no symbol)'}`"
            )
            lines.append(f"  - reason: `{entry.get('reason', 'unknown')}`")
            if entry.get("check_output"):
                lines.append("  - `#check` result:")
                lines.append("```text")
                lines.append(str(entry["check_output"]).strip())
                lines.append("```")

    return "\n".join(lines).rstrip() + "\n"


def _ensure_attempt_history(pack_dir: Path, task_id: str) -> dict[str, Any]:
    history = _load_attempt_history(pack_dir, task_id)
    _write_json(pack_dir / ATTEMPT_HISTORY_FILE_NAME, history)
    return history


def _count_consecutive_primary_failures(attempts: list[dict[str, Any]]) -> tuple[str, int]:
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


def _recommended_action_for_kind(kind: str, repeated_count: int = 0) -> str:
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
    elif kind == MISSING_LOCAL_FOUNDATION_LEMMA_KIND:
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






def _collect_direct_downstream_consumers(task_id: str, settings) -> list[dict[str, str]]:
    consumers: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    canonical_task_id = canonicalize_block_id(task_id)
    for plan_file in sorted(settings.plans_dir.glob("*_plan.json")):
        tasks = _read_json_safely(plan_file, [])
        if not isinstance(tasks, list):
            continue
        for raw_task in tasks:
            if not isinstance(raw_task, dict):
                continue
            task = canonicalize_task_dict(raw_task)
            consumer_id = task.get("block_id", "")
            if not consumer_id or consumer_id == canonical_task_id:
                continue
            hard_deps = canonicalize_id_list(task.get("dependencies", []))
            soft_imports = canonicalize_id_list(task.get("soft_imports", []))
            relation = ""
            if canonical_task_id in hard_deps:
                relation = "hard_dependency"
            elif canonical_task_id in soft_imports:
                relation = "soft_import"
            if not relation:
                continue
            key = (consumer_id, relation)
            if key in seen:
                continue
            seen.add(key)
            consumers.append(
                {
                    "block_id": consumer_id,
                    "relation": relation,
                    "type": str(task.get("type", "") or ""),
                    "title": str(task.get("title", "") or ""),
                    "source_plan": str(task.get("source_plan", "") or plan_file.stem.replace("_plan", "")),
                }
            )
    return consumers


def _review_allowed_abstractions(task: dict[str, Any]) -> list[str]:
    task_type = str(task.get("type", "") or "").strip().lower()
    lines = [
        "可以在证明内部调用 Mathlib 或已有测度论/积分论引理，但导出的 theorem/definition statement 必须忠实对应教材对象。",
    ]
    if task_type.startswith("theorem"):
        lines.extend(
            [
                "可以引入局部 helper lemma，但不能把全局 theorem 偷换成更弱、局部或带额外结构假设的版本。",
                "可以在 proof spine 上做抽象化压缩，但不能跳过教材真正依赖的桥接对象或中间结论。",
            ]
        )
    elif task_type == "definition":
        lines.extend(
            [
                "可以新增 supporting structures/lemmas，但导出的定义不能退化成 existential shell 或 placeholder。",
                "若定义承担公共接口职责，review 必须按下游可消费性而不是单文件可编译性判断。",
            ]
        )
    elif "example" in task_type:
        lines.extend(
            [
                "可以用离散化、有限支撑或等价编码复现教材构造，但必须保留原结论、关键构造和反例/计算逻辑。",
            ]
        )
    return lines


def _review_forbidden_weakenings(task: dict[str, Any]) -> list[str]:
    task_id = task["block_id"]
    task_type = str(task.get("type", "") or "").strip().lower()
    weakenings = [
        "禁止把教材中的公共接口偷换成纯存在性壳、占位定义或只记录 witness 的结构。",
        "禁止把应当供下游复用的 theorem 改写成只够当前文件自证的 theorem-specific wrapper。",
    ]
    if task_type.startswith("theorem"):
        weakenings.append("禁止通过额外 theorem-level 假设来掩盖上游接口缺口，除非任务文本本身明确包含该假设。")
    if task_id == "thm_7_8":
        weakenings.extend(
            [
                "禁止把有限区间 LS↔RS interface translation 弱化成纯 measure-side interval integral 等式，却无法支撑 thm_7_9 的 improper RS 主线。",
                "禁止把端点无原子条件扩张为教材外的结构性假设。",
                "禁止让 direct downstream 在 `[-n,n]` 截断调用时额外补充新的端点原子假设；如果做不到无新增假设实例化，则 thm_7_8 不得通过。",
            ]
        )
    elif task_id == "thm_7_9":
        weakenings.extend(
            [
                "禁止绕开 def_1_4 的 improper RS 定义，直接用 measure-side shortcut 代替教材主线。",
                "禁止把 finite-interval interface translation 缩成局部可用版本，再在 thm_7_9 中偷偷补 theorem-level 新假设。",
            ]
        )
    elif task_id == "thm_7_12":
        weakenings.extend(
            [
                "禁止绕开 thm_7_9，直接从 LS 积分跳到 ordinary integral。",
                "禁止把 `LS -> improper RS -> ordinary integral` 压扁成一跳式 measure-side shortcut。",
            ]
        )
    elif task_id == "def_1_2":
        weakenings.append("禁止把 RS integrability 定义成 Nonempty witness 之类的抽象壳，而不暴露 partition / sum / integral 接口。")
    elif task_id == "def_1_4":
        weakenings.extend(
            [
                "禁止把 improper RS 定义成 `∃ I, True` 或任何不含双端截断极限内容的占位壳。",
                "禁止用 `else 0`、`default` 或任意 fallback 值掩盖 divergence / undefinedness。",
                "若定义拆成 convergence predicate + chosen value，禁止让 downstream 能在没有收敛证明的情况下直接消费 chosen value。",
            ]
        )
    elif task_id == "thm_8_6":
        weakenings.append("禁止只 formalize 离散分支却 promote 为总 theorem；若连续分支未覆盖，总 theorem 不得通过。")
    elif task_id == "ex_8_4_3":
        weakenings.append("禁止绕开 thm_8_6_discrete 自己手搓一套 Bernoulli-vs-Poisson TV 推导。")
    elif task_id == "thm_8_7":
        weakenings.append("禁止在 thm_8_7 内重新定义 totalVariationDistance；必须消费 def_8_5 的公共定义。")
    return _dedupe_strings(weakenings)


def _review_history_risks(task_id: str) -> list[str]:
    risks: dict[str, list[str]] = {
        "def_1_2": [
            "历史版本把 RS integrability 退化成 `Nonempty` witness 壳，下游无法从中抽取可复用接口。",
        ],
        "def_1_4": [
            "历史版本把 improper RS integral 写成 `∃ I, True` 占位壳，无法支撑 thm_7_9 / thm_7_12。",
            "历史版本曾用 `else 0` 作为 divergence fallback，导致定义在语义上掩盖了“积分不存在”。",
        ],
        "thm_7_8": [
            "历史版本只给出有限区间上的局部 measure-side translation，review 通过后仍不足以支撑 thm_7_9。",
            "历史版本要求额外端点无原子条件，导致 thm_7_9 的 `[-n,n]` 截断主线无法无新增假设复用。",
        ],
        "thm_7_12": [
            "历史主线风险是直接走 measure-side shortcut，跳过 thm_7_9 所需的 improper RS 接口。",
        ],
        "thm_8_6": [
            "历史主线风险是只 formalize 离散 half，或把 continuous case 留成“similar proof”的空壳。",
        ],
        "thm_8_7": [
            "历史版本在 theorem 文件里复制定义 totalVariationDistance，削弱了 def_8_5 的公共接口地位。",
        ],
    }
    return list(risks.get(task_id, []))


def _review_downstream_checklist(task_id: str) -> list[str]:
    checks: dict[str, list[str]] = {
        "thm_7_8": [
            "必须检查 thm_7_9 能否在每个截断区间 `[-n,n]` 上直接实例化 thm_7_8，而不新增教材外 theorem-level 假设。",
            "若候选版本只在局部区间语义下成立，但 closed-interval textbook 消费路径需要额外补端点条件，则 verdict 必须为 fail。",
        ],
        "def_1_4": [
            "必须检查 downstream 是否只能在收敛已证明的前提下读取 improper RS 的具体值。",
            "若 exported definition 通过 fallback 数值掩盖 divergence，或把收敛失败编码成一个普通数值，verdict 必须为 fail。",
        ],
        "thm_7_9": [
            "必须检查证明主线是否真实经过修好的 thm_7_8 与 def_1_4，而不是直接改写成 measure-side shortcut。",
        ],
        "thm_7_12": [
            "必须检查证明是否真实经过 `LS -> improper RS -> ordinary integral`，并显式消费 thm_7_9。",
        ],
    }
    return list(checks.get(task_id, []))


def _sha256_json(payload: Any) -> str:
    return _sha256_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))


def _dependency_review_metadata(
    dep_id: str,
    dep_record: dict[str, Any] | None,
    settings,
) -> dict[str, Any]:
    dep_id = canonicalize_block_id(dep_id)
    record = dep_record if isinstance(dep_record, dict) else {}
    source_plan = str(record.get("source_plan", "unknown") or "unknown")
    dep_file = find_existing_task_file(dep_id, source_plan, settings)
    exported_symbols = record.get("exported_symbols", [])
    if not isinstance(exported_symbols, list):
        exported_symbols = []

    if record:
        return {
            "title": str(record.get("title", "") or "(untitled)"),
            "status": str(record.get("status", "UNKNOWN") or "UNKNOWN"),
            "source_plan": source_plan,
            "file": str(dep_file or ""),
            "exported_symbols": exported_symbols,
            "ledger_missing": False,
        }

    inferred_source_plan = source_plan
    inferred_exports: list[str] = []
    if dep_file:
        dep_code = _read_file_safely(dep_file)
        source_match = re.search(r"(?m)^\s*SOURCE PLAN:\s*(?P<source>.+?)\s*$", dep_code)
        if source_match:
            inferred_source_plan = source_match.group("source").strip() or source_plan
        for match in re.finditer(
            r"(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)\b",
            dep_code,
        ):
            inferred_exports.append(match.group(1))
            if len(inferred_exports) >= 8:
                break

    return {
        "title": "(ledger entry missing; output file present)" if dep_file else "(untitled)",
        "status": "OUTPUT_PRESENT_LEDGER_MISSING" if dep_file else "UNKNOWN",
        "source_plan": inferred_source_plan,
        "file": str(dep_file or ""),
        "exported_symbols": inferred_exports,
        "ledger_missing": not bool(record),
    }




def build_semantic_review_context_markdown(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> str:
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    output_binding = resolve_phase2_output_binding(task, ledger, settings)
    output_owner_id = output_binding.output_owner_task_id
    output_owner_record = ledger.ledger.get("tasks", {}).get(output_owner_id, {})
    if not isinstance(output_owner_record, dict):
        output_owner_record = {}
    output_owner_task = canonicalize_task_dict(output_owner_record) if output_owner_record else task
    if output_binding.is_obligation_task and output_owner_task.get("block_id") != output_owner_id:
        output_owner_task = dict(output_owner_task)
        output_owner_task["block_id"] = output_owner_id
    obligations_pack_dir = output_binding.owner_pack_dir if output_binding.is_obligation_task else pack_dir
    downstream = _collect_direct_downstream_consumers(output_owner_id, settings)
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    active_targets = list(output_binding.official_targets)
    public_exports_source = output_owner_record if output_binding.is_obligation_task else current_record
    public_exports = public_exports_source.get("exported_symbols", []) if isinstance(public_exports_source, dict) else []
    if not isinstance(public_exports, list):
        public_exports = []
    lines = [
        f"# Semantic Review Context for {task_id}",
        "",
        "This file is the authoritative review context for `review-pack` and `review-existing`.",
        "A local build is not enough: the reviewer must check statement fidelity, proof spine adequacy, interface contract, and downstream adequacy against this context.",
        "",
    ]
    source_decision_path = pack_dir / "source_decision_resolution.json"
    if source_decision_path.is_file():
        source_decision = _read_json_safely(source_decision_path, {})
        if isinstance(source_decision, dict):
            lines.extend(
                [
                    "## Resolved Source/Statement Decision",
                    "",
                    f"- Decision file: `{source_decision_path}`",
                    f"- Status: `{source_decision.get('status', '')}`",
                    f"- Decision: {str(source_decision.get('decision', '') or '').strip()}",
                ]
            )
            corrected_statement = str(source_decision.get("corrected_statement", "") or "").strip()
            if corrected_statement:
                lines.append(f"- Corrected statement: {corrected_statement}")
            reason = str(source_decision.get("reason", "") or "").strip()
            if reason:
                lines.append(f"- Reason: {reason}")
            lines.append("")
    lines.extend([
        "## Original Task Text",
        "",
        f"- Type: `{task.get('type', '')}`",
        f"- Source plan: `{source_plan}`",
        f"- Title: `{str(task.get('title', '') or '(untitled)').strip()}`",
        "",
        str(task.get("content", "") or "(no content)").strip(),
        "",
        "## Upstream Textbook Chain",
        "",
    ])
    if not hard_deps and not soft_imports:
        lines.append("- No declared upstream textbook tasks.")
    else:
        for relation_name, deps in (("Hard dependencies", hard_deps), ("Soft imports", soft_imports)):
            lines.append(f"### {relation_name}")
            if not deps:
                lines.append("- None")
                continue
            for dep in deps:
                dep_id = canonicalize_block_id(dep)
                dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
                dep_meta = _dependency_review_metadata(dep_id, dep_record, settings)
                lines.append(
                    f"- `{dep_id}` from `{dep_meta['source_plan']}` / `{dep_meta['status']}`: {dep_meta['title']}"
                )
                if dep_meta["ledger_missing"] and dep_meta["file"]:
                    lines.append(f"  - Fallback output file: `{dep_meta['file']}`")
                if dep_meta["ledger_missing"] and dep_meta["exported_symbols"]:
                    lines.append(
                        f"  - Fallback declarations: `{', '.join(str(item) for item in dep_meta['exported_symbols'])}`"
                    )
    lines.extend(["", "## Direct Downstream Consumers", ""])
    if not downstream:
        lines.append("- No direct downstream consumers were found in current plans.")
    else:
        for consumer in downstream:
            lines.append(
                f"- `{consumer['block_id']}` from `{consumer['source_plan']}` via `{consumer['relation']}` / `{consumer['type']}`: {consumer['title'] or '(untitled)'}"
            )
    lines.extend(["", "## Current Public Interface Summary", ""])
    lines.append(f"- Output owner task: `{output_owner_id}`")
    if output_binding.focus_obligation_ids:
        lines.append(f"- Focused obligation ids: `{', '.join(output_binding.focus_obligation_ids)}`")
    lines.append(f"- Official output targets: `{', '.join(str(path) for path in active_targets) if active_targets else '(none)'}`")
    lines.append(f"- Recorded exported symbols: `{', '.join(str(item) for item in public_exports) if public_exports else '(none recorded)'}`")
    lines.append(f"- Current ledger status: `{current_record.get('status', 'UNKNOWN')}`")
    if output_binding.is_obligation_task:
        lines.append(f"- Output owner ledger status: `{output_owner_record.get('status', 'UNKNOWN')}`")
    lines.append(f"- Build candidate state: `{current_record.get('pack_candidate_state', 'draft')}`")
    latest_review_result = str(current_record.get("latest_semantic_review_result_file", "") or "")
    lines.append(f"- Last completed semantic review result: `{latest_review_result or '(none)'}`")
    obligations_record = output_owner_record if output_binding.is_obligation_task else current_record
    proof_obligations = maybe_ensure_proof_obligations_file(
        obligations_pack_dir,
        output_owner_task,
        current_record=obligations_record if isinstance(obligations_record, dict) else {},
        tracking_level=2,
    )
    if proof_obligations is None:
        lines.extend(
            [
                "",
                "## Proof Obligation Tracking",
                "",
                "- Proof obligation tracking: `Level 0 ordinary Phase2 path`.",
                "- No task-local `proof_obligations.json` is generated for this normal task.",
            ]
        )
    else:
        lines.extend(
            [
                "",
                render_proof_obligations_markdown(
                    proof_obligations,
                    path=obligations_pack_dir / PROOF_OBLIGATIONS_FILE_NAME,
                ).rstrip(),
            ]
        )
    lines.extend(["", "## Allowed Abstraction Layer", ""])
    for item in _review_allowed_abstractions(task):
        lines.append(f"- {item}")
    lines.extend(["", "## Forbidden Weakenings", ""])
    for item in _review_forbidden_weakenings(task):
        lines.append(f"- {item}")
    lines.extend(["", "## Historical Shortcut / Shell Risks", ""])
    risks = _review_history_risks(task_id)
    if risks:
        for item in risks:
            lines.append(f"- {item}")
    else:
        lines.append("- No task-specific historical shortcut is recorded; still enforce the general forbidden weakenings above.")
    lines.extend(["", "## Downstream Acceptance Checklist", ""])
    checklist = _review_downstream_checklist(task_id)
    if checklist:
        for item in checklist:
            lines.append(f"- {item}")
    else:
        lines.append("- No extra downstream checklist recorded beyond the general rubric.")
    lines.extend(["", "## Pack Snapshot", ""])
    lines.append(f"- Pack directory: `{pack_dir}`")
    lines.append(f"- Context markdown: `{pack_dir / 'context.md'}`")
    lines.append(f"- Search manifest: `{pack_dir / SEARCH_MANIFEST_FILE_NAME}`")
    lines.append(f"- Intent contract: `{_intent_contract_path(pack_dir)}`")
    return "\n".join(lines).rstrip() + "\n"


def _build_review_repair_contract(
    *,
    task: dict[str, Any],
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    failed_review_input_file: Path,
    failed_review_result_file: Path,
    failed_review_report_file: Path,
    failed_review_subject_file: Path,
    next_draft_seed_file: Path,
    attempt: int,
    origin_review_mode: str,
) -> dict[str, Any]:
    from .phase2_review_apply import _build_review_repair_contract as _owner_build_review_repair_contract

    return _owner_build_review_repair_contract(
        task=task,
        review_input=review_input,
        review_result=review_result,
        failed_review_input_file=failed_review_input_file,
        failed_review_result_file=failed_review_result_file,
        failed_review_report_file=failed_review_report_file,
        failed_review_subject_file=failed_review_subject_file,
        next_draft_seed_file=next_draft_seed_file,
        attempt=attempt,
        origin_review_mode=origin_review_mode,
    )
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    findings = review_result.get("findings", []) if isinstance(review_result.get("findings", []), list) else []
    downstream = review_result.get("downstream_adequacy", {}) if isinstance(review_result.get("downstream_adequacy", {}), dict) else {}
    blocking_issues = downstream.get("blocking_issues", []) if isinstance(downstream.get("blocking_issues", []), list) else []
    forbidden_shortcuts = review_basis.get("forbidden_weakenings", []) if isinstance(review_basis.get("forbidden_weakenings", []), list) else []

    must_fix: list[str] = []
    summary = str(review_result.get("summary", "") or "").strip()
    if summary:
        must_fix.append(summary)
    normalization_reason = str(review_result.get("normalization_reason", "") or "").strip()
    if normalization_reason:
        must_fix.append(normalization_reason)
    for finding in findings:
        if isinstance(finding, dict):
            message = str(finding.get("message", "") or finding.get("summary", "") or "").strip()
            if message and message not in must_fix:
                must_fix.append(message)
    if not must_fix:
        must_fix.append(f"Resolve semantic review verdict `{review_result.get('verdict', 'inconclusive')}` for {task['block_id']}.")

    must_preserve = _dedupe_strings(
        [
            f"Preserve the original task statement: {str(task.get('content', '') or '').strip()}",
            *[
                f"Preserve allowed abstraction: {item}"
                for item in review_basis.get("allowed_abstractions", [])
                if isinstance(item, str) and item.strip()
            ],
        ]
    )
    downstream_blockers = _dedupe_strings(
        [
            str(item.get("issue", "") or item.get("summary", "") or "").strip()
            for item in blocking_issues
            if isinstance(item, dict)
        ]
    )
    result_text = failed_review_result_file.read_text(encoding="utf-8") if failed_review_result_file.exists() else ""
    subject_text = failed_review_subject_file.read_text(encoding="utf-8") if failed_review_subject_file.exists() else ""
    return {
        "schema_version": "phase2.review_repair.request.v1",
        "task_id": task["block_id"],
        "origin_review_mode": origin_review_mode,
        "origin_review_attempt": int(review_input.get("attempt") or 0) or attempt,
        "review_subject_kind": str(review_input.get("review_subject_kind", "") or "candidate"),
        "failed_verdict": str(review_result.get("verdict", "inconclusive") or "inconclusive"),
        "failed_review_input_file": str(failed_review_input_file),
        "failed_review_result_file": str(failed_review_result_file),
        "failed_review_report_file": str(failed_review_report_file),
        "failed_review_subject_file": str(failed_review_subject_file),
        "failed_review_subject_hash": str(review_input.get("review_subject_hash", "") or review_input.get("candidate", {}).get("hash", "") or _sha256_text(subject_text)),
        "review_basis_hash": str(review_input.get("review_basis_hash", "") or ""),
        "review_result_hash": _sha256_text(result_text) if result_text else "",
        "origin_prompt_version": int(review_input.get("prompt_version") or SEMANTIC_REVIEW_PROMPT_VERSION),
        "origin_rubric_version": int(review_input.get("rubric_version") or SEMANTIC_REVIEW_RUBRIC_VERSION),
        "origin_result_schema_version": str(review_result.get("schema_version", "") or ""),
        "source_task_content": str(task.get("content", "") or ""),
        "must_fix": must_fix,
        "must_preserve": must_preserve,
        "forbidden_shortcuts": [item for item in forbidden_shortcuts if isinstance(item, str) and item.strip()],
        "downstream_blockers": downstream_blockers,
        "next_draft_seed_file": str(next_draft_seed_file),
    }




def _append_review_repair_summary_note(summary_path: Path, note: str) -> None:
    stamp = _utc_now_z()
    with open(summary_path, "a", encoding="utf-8") as f:
        f.write("\n## Repair Lifecycle Note\n\n")
        f.write(f"- {stamp}: {note.strip()}\n")


def _extract_effective_failed_review_result(payload: Any) -> dict[str, Any]:
    best: dict[str, Any] = {}
    current = payload if isinstance(payload, dict) else {}
    seen: set[int] = set()
    while isinstance(current, dict) and id(current) not in seen:
        seen.add(id(current))
        verdict = str(current.get("verdict", "") or "").strip().lower()
        cache_class = str(current.get("cache_class", "") or "").strip().lower()
        if verdict in {"fail", "inconclusive"}:
            if cache_class == "semantic_verdict":
                best = current
            elif not best:
                best = current
        raw_result = current.get("raw_result")
        nested: dict[str, Any] | None = None
        if isinstance(raw_result, dict):
            if isinstance(raw_result.get("raw_result"), dict):
                nested = raw_result.get("raw_result")
            else:
                nested = raw_result
        if not isinstance(nested, dict):
            break
        current = nested
    return dict(best) if isinstance(best, dict) and best else (dict(payload) if isinstance(payload, dict) else {})


def _latest_quarantined_seed_path(pack_dir: Path, current_record: dict[str, Any], task_id: str) -> Path | None:
    candidate_dirs: list[Path] = []
    latest_quarantine_dir = str(current_record.get("latest_quarantine_dir", "") or "").strip()
    if latest_quarantine_dir:
        latest_path = Path(latest_quarantine_dir).expanduser()
        if not latest_path.is_absolute():
            latest_path = (pack_dir / latest_path).resolve()
        candidate_dirs.append(latest_path)
    numbered_dirs: list[tuple[int, Path]] = []
    for path in pack_dir.glob("rejected_official_v*"):
        match = re.fullmatch(r"rejected_official_v(\d+)", path.name)
        if match and path.is_dir():
            numbered_dirs.append((int(match.group(1)), path))
    numbered_dirs.sort(key=lambda item: item[0], reverse=True)
    candidate_dirs.extend(path for _, path in numbered_dirs)

    seen: set[str] = set()
    ordered_dirs: list[Path] = []
    for path in candidate_dirs:
        resolved = path.resolve()
        key = str(resolved)
        if key in seen:
            continue
        seen.add(key)
        ordered_dirs.append(resolved)

    for quarantine_dir in ordered_dirs:
        manifest = _read_json_safely(quarantine_dir / "quarantine_manifest.json", {})
        if not isinstance(manifest, dict):
            continue
        files = manifest.get("files", [])
        if not isinstance(files, list):
            continue
        fallback: Path | None = None
        for item in files:
            if not isinstance(item, dict):
                continue
            raw_path = str(item.get("quarantine_path", "") or "").strip()
            if not raw_path:
                continue
            seed_path = Path(raw_path).expanduser()
            if not seed_path.is_absolute():
                seed_path = (quarantine_dir / seed_path).resolve()
            if not seed_path.exists():
                continue
            if seed_path.name == f"{task_id}.lean":
                return seed_path
            if fallback is None:
                fallback = seed_path
        if fallback is not None:
            return fallback
    return None


def _backfill_review_repair_request_from_latest_failed_review(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
) -> tuple[str, dict[str, Any]]:
    from .phase2_review_loop import (
        _backfill_review_repair_request_from_latest_failed_review as _owner_backfill_review_repair_request_from_latest_failed_review,
    )

    return _owner_backfill_review_repair_request_from_latest_failed_review(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
    )
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    repair_dispositions = {
        "official_output_review_fail",
        "official_output_review_inconclusive",
        "codex_review_fail_no_promotion",
        "codex_review_inconclusive_no_promotion",
    }
    for verify_path in reversed(_list_versioned_json_files(pack_dir, "verify_result")):
        verify_payload = _read_json_safely(verify_path, {})
        if not isinstance(verify_payload, dict):
            continue
        if str(verify_payload.get("mode", "") or "") != "review-apply":
            continue
        if str(verify_payload.get("disposition", "") or "") not in repair_dispositions:
            continue
        semantic_review = verify_payload.get("semantic_review", {})
        if not isinstance(semantic_review, dict):
            continue
        review_input_path = _resolve_review_binding_path(str(semantic_review.get("review_input_file", "") or ""), pack_dir=pack_dir)
        review_result_path = _resolve_review_binding_path(str(semantic_review.get("review_result_file", "") or ""), pack_dir=pack_dir)
        review_report_path = _resolve_review_binding_path(str(semantic_review.get("review_report_file", "") or ""), pack_dir=pack_dir)
        if not review_input_path.exists() or not review_result_path.exists() or not review_report_path.exists():
            continue
        review_input = _read_json_safely(review_input_path, {})
        if not isinstance(review_input, dict):
            continue
        review_result_payload = _read_json_safely(review_result_path, {})
        effective_result = _extract_effective_failed_review_result(review_result_payload)
        if not isinstance(effective_result, dict):
            continue
        verdict = str(effective_result.get("verdict", "") or "").strip().lower()
        if verdict not in {"fail", "inconclusive"}:
            continue
        subject_file_raw = str(
            review_input.get("review_subject_file", "")
            or review_input.get("candidate", {}).get("file", "")
            or ""
        ).strip()
        if not subject_file_raw:
            continue
        subject_path = _resolve_review_binding_path(subject_file_raw, pack_dir=pack_dir)
        if not subject_path.exists():
            continue
        review_subject_kind = str(review_input.get("review_subject_kind", "") or "candidate")
        if review_subject_kind == "official_output":
            seed_path = _latest_quarantined_seed_path(pack_dir, current_record if isinstance(current_record, dict) else {}, task_id) or subject_path
        else:
            seed_path = subject_path
        repair_ready = _write_review_repair_artifacts(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            review_input=review_input,
            review_result=effective_result,
            failed_review_input_file=review_input_path,
            failed_review_result_file=review_result_path,
            failed_review_report_file=review_report_path,
            failed_review_subject_file=subject_path,
            next_draft_seed_file=seed_path,
            origin_review_mode="review-apply-backfill",
        )
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return "", repair_ready
    return "No failed review-apply result is available to backfill a repair cycle.", {}






def _build_dependency_review_summary(task: dict[str, Any], ledger: LedgerManager, settings) -> list[dict[str, Any]]:
    summary: list[dict[str, Any]] = []
    for dep in _task_final_import_union(task):
        dep_record = ledger.ledger.get("tasks", {}).get(dep, {})
        source_plan = dep_record.get("source_plan", "unknown") if isinstance(dep_record, dict) else "unknown"
        dep_file = find_existing_task_file(dep, str(source_plan), settings)
        dep_code = _read_file_safely(dep_file) if dep_file else ""
        decls = []
        for match in TOP_LEVEL_DECL_RE.finditer(dep_code):
            decls.append(match.group(0).strip())
            if len(decls) >= 8:
                break
        summary.append(
            {
                "task_id": dep,
                "source_plan": source_plan,
                "file": str(dep_file or ""),
                "exported_symbols": dep_record.get("exported_symbols", []) if isinstance(dep_record, dict) else [],
                "declarations": decls,
            }
        )
    return summary


def _build_search_review_summary(pack_dir: Path) -> dict[str, Any]:
    manifest = _read_json_safely(pack_dir / SEARCH_MANIFEST_FILE_NAME, {})
    if not isinstance(manifest, dict):
        return {}
    entries = manifest.get("entries", [])
    verified = [entry for entry in entries if isinstance(entry, dict) and entry.get("status") == "verified"] if isinstance(entries, list) else []
    return {
        "search_terms": manifest.get("search_terms", [])[:12] if isinstance(manifest.get("search_terms", []), list) else [],
        "verified_entry_count": len(verified),
        "verified_symbols": [
            {"symbol": entry.get("symbol", ""), "import_path": entry.get("import_path", "")}
            for entry in verified[:20]
        ],
    }


def _phase2_queue_reports_dir(settings) -> Path:
    return settings.phase2_prompt_packs_dir / "_reports"


def _queue_report_base_name() -> str:
    return f"{REVIEW_EXISTING_QUEUE_REPORT_PREFIX}_{datetime.now(UTC).strftime('%Y%m%d_%H%M%S')}"


def _is_queue_skipped_temp_output(file_path: Path) -> bool:
    return any(file_path.stem.startswith(prefix) for prefix in NON_OFFICIAL_OUTPUT_PREFIXES)


def _is_canonical_official_output(file_path: Path) -> bool:
    if file_path.suffix != ".lean":
        return False
    stem = file_path.stem
    return bool(stem) and stem == canonicalize_block_id(stem) and extract_chapter(stem) is not None


def _iter_review_existing_queue_outputs(settings, selected_task_ids: set[str] | None = None) -> tuple[list[Path], list[str]]:
    outputs_by_task: dict[str, Path] = {}
    skipped_non_official: list[str] = []
    root = settings.toyapollo_output_dir
    if not root.exists():
        return [], skipped_non_official
    for file_path in sorted(root.glob("*.lean")):
        if _is_queue_skipped_temp_output(file_path):
            continue
        if not _is_canonical_official_output(file_path):
            skipped_non_official.append(str(file_path))
            continue
        canonical_task_id = canonicalize_block_id(file_path.stem)
        if selected_task_ids is not None and canonical_task_id not in selected_task_ids:
            continue
        outputs_by_task[canonical_task_id] = file_path
    return [outputs_by_task[task_id] for task_id in sorted(outputs_by_task)], skipped_non_official


def _resolve_plan_task_for_output(task_id: str, settings) -> dict[str, Any] | None:
    task = find_task_in_plans(task_id, settings.plans_dir)
    return canonicalize_task_dict(task) if isinstance(task, dict) else None


def _ensure_queue_pack_dir(task: dict[str, Any], ledger: LedgerManager, settings) -> Path:
    task_id = canonicalize_block_id(task.get("block_id", ""))
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    pack_dir.mkdir(parents=True, exist_ok=True)
    _write_json(
        pack_dir / "task.json",
        {
            "block_id": task_id,
            "type": task.get("type", "Unknown"),
            "title": task.get("title", ""),
            "content": task.get("content", ""),
            "source_plan": task.get("source_plan", "unknown"),
            "dependencies": canonicalize_id_list(task.get("dependencies", [])),
            "soft_imports": canonicalize_id_list(task.get("soft_imports", [])),
            "final_import_union": canonicalize_id_list(task.get("dependencies", []) + task.get("soft_imports", [])),
        },
    )
    if not (pack_dir / ATTEMPT_HISTORY_FILE_NAME).exists():
        _write_json(pack_dir / ATTEMPT_HISTORY_FILE_NAME, {"task_id": task_id, "attempts": []})
    for relative_path, default_text in (
        (FAILURE_SUMMARY_FILE_NAME, ""),
        ("build_feedback.txt", ""),
        ("verification_report.md", f"# Verification Report for {task_id}\n\n"),
        ("context.md", ""),
    ):
        target = pack_dir / relative_path
        if not target.exists():
            target.write_text(default_text, encoding="utf-8")
    metadata = _read_json_safely(pack_dir / "metadata.json", {})
    if not isinstance(metadata, dict):
        metadata = {}
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    metadata.update(
        {
            "task_id": task_id,
            "draft_file": str(pack_dir / DRAFT_FILE_NAME),
            "intent_contract_file": str(_intent_contract_path(pack_dir)),
            "search_manifest_file": str(pack_dir / SEARCH_MANIFEST_FILE_NAME),
            "attempt_history_file": str(pack_dir / ATTEMPT_HISTORY_FILE_NAME),
            "failure_summary_file": str(pack_dir / FAILURE_SUMMARY_FILE_NAME),
            "pack_candidate_state": str(current_record.get("pack_candidate_state", "draft") or "draft"),
            "latest_operation_kind": str(current_record.get("latest_operation_kind", "") or ""),
            "latest_operation_file": str(current_record.get("latest_operation_file", "") or ""),
        }
    )
    _write_json(pack_dir / "metadata.json", metadata)
    return pack_dir


def _sync_current_review_aliases(
    pack_dir: Path,
    *,
    input_path: Path,
    prompt_path: Path,
    template_path: Path,
    context_path: Path | None = None,
    request_path: Path | None = None,
) -> None:
    alias_paths = {
        "input": pack_dir / "semantic_review_input.json",
        "prompt": pack_dir / "semantic_review_prompt.md",
        "template": pack_dir / SEMANTIC_REVIEW_RESULT_TEMPLATE_ALIAS,
        "context": latest_semantic_review_context_path(pack_dir),
        "request": _latest_review_request_path(pack_dir),
    }
    for source, alias in (
        (input_path, alias_paths["input"]),
        (prompt_path, alias_paths["prompt"]),
        (template_path, alias_paths["template"]),
        (context_path, alias_paths["context"]),
        (request_path, alias_paths["request"]),
    ):
        if source is None:
            continue
        if _path_exists(alias):
            _unlink_path(alias)
        _copy_file(source, alias)


def _sync_current_review_repair_aliases(
    pack_dir: Path,
    *,
    request_path: Path | None = None,
    summary_path: Path | None = None,
) -> None:
    alias_paths = {
        "request": _latest_review_repair_request_path(pack_dir),
        "summary": _latest_review_repair_summary_path(pack_dir),
    }
    for source, alias in (
        (request_path, alias_paths["request"]),
        (summary_path, alias_paths["summary"]),
    ):
        if source is None:
            continue
        if _path_exists(alias):
            _unlink_path(alias)
        _copy_file(source, alias)


def _semantic_review_attempt_from_path(path: Path, prefix: str) -> int | None:
    match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.(?:json|md)", path.name)
    if not match:
        return None
    return int(match.group(1))


def _queue_review_result_is_valid(result_path: Path, review_input: dict[str, Any], task_id: str) -> bool:
    raw_result = _read_json_safely(result_path, {})
    if not isinstance(raw_result, dict):
        return False
    if canonicalize_block_id(str(raw_result.get("task_id", "") or "")) != task_id:
        return False
    if int(raw_result.get("prompt_version") or 0) != SEMANTIC_REVIEW_PROMPT_VERSION:
        return False
    if int(raw_result.get("rubric_version") or 0) != SEMANTIC_REVIEW_RUBRIC_VERSION:
        return False
    review_input_file = str(raw_result.get("review_input_file", "") or "")
    if not review_input_file:
        return False
    resolved_input = Path(review_input_file).expanduser()
    if not resolved_input.is_absolute():
        resolved_input = (result_path.parent / resolved_input).resolve()
    if resolved_input != result_path.parent / f"semantic_review_input_v{int(review_input.get('attempt') or 0)}.json":
        return False
    if str(raw_result.get("candidate_hash", "") or "") != str(review_input.get("candidate", {}).get("hash", "") or ""):
        return False
    decision = evaluate_semantic_review_result(
        raw_result,
        review_input=review_input,
        runner_metadata=raw_result.get("runner", {}) if isinstance(raw_result.get("runner"), dict) else {"status": "queue-inspection"},
    )
    return decision.is_semantic_verdict


def _find_matching_existing_review_materials(
    pack_dir: Path,
    task_id: str,
    subject_hash: str,
    review_basis_hash: str,
    subject_kind: str = "official_output",
) -> dict[str, Any]:
    matching_without_result: dict[str, Any] | None = None
    matching_with_result: dict[str, Any] | None = None
    stale_result_files: list[str] = []
    for input_path in sorted(_list_versioned_json_files(pack_dir, "semantic_review_input"), reverse=True):
        attempt = _semantic_review_attempt_from_path(input_path, "semantic_review_input")
        if attempt is None:
            continue
        review_input = _read_json_safely(input_path, {})
        review_paths = next_semantic_review_artifact_paths(pack_dir, attempt)
        result_path = review_paths["result"]
        prompt_path = review_paths["prompt"]
        template_path = _result_template_path(pack_dir, attempt)
        context_path = next_semantic_review_context_path(pack_dir, attempt)
        if not isinstance(review_input, dict):
            if result_path.exists():
                stale_result_files.append(str(result_path))
            continue
        input_task_id = canonicalize_block_id(str(review_input.get("task", {}).get("block_id", "") or ""))
        input_subject_kind = str(review_input.get("review_subject_kind", "") or "")
        input_hash = str(review_input.get("review_subject_hash", "") or "")
        input_basis_hash = str(review_input.get("review_basis_hash", "") or "")
        prompt_version = int(review_input.get("prompt_version") or 0)
        rubric_version = int(review_input.get("rubric_version") or 0)
        if (
            input_task_id != task_id
            or input_subject_kind != subject_kind
            or input_hash != subject_hash
            or not input_basis_hash
            or input_basis_hash != review_basis_hash
            or prompt_version != SEMANTIC_REVIEW_PROMPT_VERSION
            or rubric_version != SEMANTIC_REVIEW_RUBRIC_VERSION
            or not prompt_path.exists()
            or not template_path.exists()
            or not context_path.exists()
        ):
            if result_path.exists():
                stale_result_files.append(str(result_path))
            continue
        candidate = {
            "attempt": attempt,
            "input_path": input_path,
            "prompt_path": prompt_path,
            "template_path": template_path,
            "context_path": context_path,
            "result_path": result_path if result_path.exists() else None,
            "review_input": review_input,
        }
        if result_path.exists() and _queue_review_result_is_valid(result_path, review_input, task_id):
            if matching_with_result is None:
                matching_with_result = candidate
            continue
        if result_path.exists():
            stale_result_files.append(str(result_path))
            continue
        if matching_without_result is None:
            matching_without_result = candidate
    return {
        "matching_with_result": matching_with_result,
        "matching_without_result": matching_without_result,
        "stale_result_files": stale_result_files,
    }


def _prepare_existing_output_review_materials(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    output_path: Path,
    mode: str,
    build_output: str,
    force_new_attempt: bool = False,
    review_subject_kind: str = "official_output",
) -> dict[str, Any]:
    task_id = task["block_id"]
    candidate_code = _read_file_safely(output_path)
    candidate_hash = _sha256_text(candidate_code) if candidate_code else ""
    review_basis = build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind=review_subject_kind,
        review_subject_hash=candidate_hash,
        review_subject_file=output_path,
    )
    review_basis_hash = _sha256_json(review_basis)
    attempt_info = _find_matching_existing_review_materials(
        pack_dir,
        task_id,
        candidate_hash,
        review_basis_hash,
        subject_kind=review_subject_kind,
    )
    current_materials = None if force_new_attempt else (attempt_info["matching_with_result"] or attempt_info["matching_without_result"])
    reused = current_materials is not None
    if not reused:
        review_attempt = _next_review_attempt(pack_dir)
        snapshot_path = (
            output_path
            if review_subject_kind == "existing_support"
            else _next_official_snapshot_path(pack_dir, review_attempt)
        )
        if review_subject_kind != "existing_support":
            snapshot_path.write_text(candidate_code, encoding="utf-8")
        semantic_review = _write_codex_handoff_review_artifacts(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            attempt=review_attempt,
            candidate_path=snapshot_path,
            candidate_code=candidate_code,
            build_summary={"final_build": {"success": True, "output": build_output}},
            mode=mode,
            review_subject_kind=review_subject_kind,
        )
        current_materials = {
            "attempt": review_attempt,
            "input_path": Path(str(semantic_review["review_input_file"])),
            "prompt_path": Path(str(semantic_review["review_prompt_file"])),
            "template_path": Path(str(semantic_review["review_result_template_file"])),
            "context_path": Path(str(semantic_review["review_context_file"])),
            "request_path": Path(str(semantic_review["review_request_file"])),
            "result_path": None,
        }
    else:
        review_attempt = int(current_materials["attempt"])
        snapshot_path = (
            output_path
            if review_subject_kind == "existing_support"
            else _next_official_snapshot_path(pack_dir, review_attempt)
        )
        if review_subject_kind != "existing_support" and not snapshot_path.exists():
            snapshot_path.write_text(candidate_code, encoding="utf-8")
        request_path = _review_request_path(pack_dir, review_attempt)
        if not request_path.exists():
            review_input = current_materials.get("review_input", {})
            if isinstance(review_input, dict):
                request_payload = _build_semantic_review_request(
                    task_id=task_id,
                    origin=mode,
                    attempt=review_attempt,
                    review_subject_kind=review_subject_kind,
                    review_subject_file=str(snapshot_path),
                    review_subject_hash=str(review_input.get("review_subject_hash", "") or candidate_hash),
                    review_basis_hash=str(review_input.get("review_basis_hash", "") or review_basis_hash),
                    review_input_hash=_sha256_json(review_input),
                    review_input_file=str(current_materials["input_path"]),
                    review_prompt_file=str(current_materials["prompt_path"]),
                    review_context_file=str(current_materials["context_path"]),
                    review_result_template_file=str(current_materials["template_path"]),
                    expected_result_file=str(current_materials["result_path"] or next_semantic_review_artifact_paths(pack_dir, review_attempt)["result"]),
                    reviewer_backend_id="codex-handoff",
                    prompt_version=int(review_input.get("prompt_version") or SEMANTIC_REVIEW_PROMPT_VERSION),
                    rubric_version=int(review_input.get("rubric_version") or SEMANTIC_REVIEW_RUBRIC_VERSION),
                )
                _write_json(request_path, request_payload)
        current_materials["request_path"] = request_path
    _sync_current_review_aliases(
        pack_dir,
        input_path=current_materials["input_path"],
        prompt_path=current_materials["prompt_path"],
        template_path=current_materials["template_path"],
        context_path=current_materials["context_path"],
        request_path=current_materials.get("request_path"),
    )
    return {
        "attempt": review_attempt,
        "reused": reused,
        "snapshot_path": snapshot_path,
        "input_path": current_materials["input_path"],
        "prompt_path": current_materials["prompt_path"],
        "template_path": current_materials["template_path"],
        "context_path": current_materials["context_path"],
        "request_path": current_materials.get("request_path"),
        "result_path": current_materials["result_path"],
        "latest_matching_review_result_file": str(current_materials["result_path"]) if current_materials["result_path"] is not None else "",
        "candidate_code": candidate_code,
        "candidate_hash": candidate_hash,
        "has_stale_result": bool(attempt_info["stale_result_files"]),
        "stale_result_files": attempt_info["stale_result_files"],
    }


def _queue_source_resolution(task_id: str, task: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(task, dict):
        return {
            "status": "missing_in_plans",
            "task_id": task_id,
            "source_plan": "",
            "detail": f"No source task was found in plans/*.json for {task_id}.",
        }
    return {
        "status": "resolved_from_plans",
        "task_id": task_id,
        "source_plan": str(task.get("source_plan", "unknown") or "unknown"),
        "detail": f"Resolved source task for {task_id} from plans/*.json.",
    }


def _queue_sanity_build_status(task_id: str, success: bool, detail: str) -> dict[str, Any]:
    return {
        "status": "passed" if success else "failed",
        "module": f"ToyApollo.Output.{task_id}",
        "detail": detail,
    }


def _clear_current_review_metadata_for_existing_subjects(task_id: str, ledger: LedgerManager) -> None:
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    subject_kind = str(current_record.get("current_review_subject_kind", "") or "")
    origin = str(current_record.get("current_review_origin", "") or "")
    if subject_kind == "official_output" or origin in {"review-existing", "review-existing-queue"}:
        _clear_current_review_metadata(task_id, ledger)


def _queue_status_for_prepared_materials(prepared: dict[str, Any]) -> tuple[str, str, str]:
    if str(prepared.get("latest_matching_review_result_file", "") or ""):
        return (
            "review_result_present",
            "inspect_existing_result",
            "A current matching semantic review result already exists for this official output snapshot.",
        )
    if bool(prepared.get("has_stale_result")):
        return (
            "stale_review_result",
            "codex_review",
            "Only stale or invalid semantic review results were found; fresh reviewer output is required.",
        )
    return (
        "ready_for_codex_review",
        "codex_review",
        "Reviewer materials are prepared and no current matching review result exists yet.",
    )


def _review_existing_queue_material_summary(counts: dict[str, Any]) -> dict[str, int]:
    ready_for_codex_review = int(counts.get("ready_for_codex_review", 0) or 0)
    stale_review_result = int(counts.get("stale_review_result", 0) or 0)
    review_result_present = int(counts.get("review_result_present", 0) or 0)
    blocked_build = int(counts.get("blocked_build", 0) or 0)
    source_missing = int(counts.get("source_missing", 0) or 0)
    return {
        "prepared_review_materials": ready_for_codex_review + stale_review_result + review_result_present,
        "fresh_review_required": ready_for_codex_review + stale_review_result,
        "ready_without_prior_result": ready_for_codex_review,
        "stale_or_invalid_prior_results": stale_review_result,
        "current_matching_review_results": review_result_present,
        "blocked_build": blocked_build,
        "source_missing": source_missing,
    }


def _render_review_existing_queue_markdown(report: dict[str, Any]) -> str:
    counts = report.get("counts", {}) if isinstance(report.get("counts", {}), dict) else {}
    material_summary = (
        report.get("review_material_summary", {})
        if isinstance(report.get("review_material_summary", {}), dict)
        else _review_existing_queue_material_summary(counts)
    )
    lines = [
        "# Phase 2 review-existing-queue",
        "",
        f"- Scanned at: `{report.get('scanned_at', '')}`",
        f"- Official outputs scanned: `{report.get('official_outputs_scanned', 0)}`",
        f"- Skipped non-official files: `{len(report.get('skipped_non_official_files', []))}`",
        "",
        "## Queue Counts",
        "",
    ]
    if counts:
        for status in (
            "blocked_build",
            "source_missing",
            "review_result_present",
            "stale_review_result",
            "ready_for_codex_review",
        ):
            lines.append(f"- `{status}`: `{counts.get(status, 0)}`")
    else:
        lines.append("- No official outputs were scanned.")
    lines.extend(
        [
            "",
            "## Review Material Summary",
            "",
            f"- Prepared review materials: `{material_summary.get('prepared_review_materials', 0)}`",
            f"- Fresh review required: `{material_summary.get('fresh_review_required', 0)}`",
            f"- Ready without prior result: `{material_summary.get('ready_without_prior_result', 0)}`",
            f"- Stale or invalid prior results: `{material_summary.get('stale_or_invalid_prior_results', 0)}`",
            f"- Current matching review results: `{material_summary.get('current_matching_review_results', 0)}`",
            f"- Blocked build: `{material_summary.get('blocked_build', 0)}`",
            f"- Source missing: `{material_summary.get('source_missing', 0)}`",
            "",
            "Note: `stale_review_result` means review materials are prepared, but the prior semantic review result is stale or invalid. A reviewer should write a fresh result for that prepared request.",
        ]
    )
    lines.extend(["", "## Tasks", ""])
    tasks = report.get("tasks", [])
    if not isinstance(tasks, list) or not tasks:
        lines.append("- No matching official outputs were found.")
        return "\n".join(lines).rstrip() + "\n"
    for task_report in tasks:
        if not isinstance(task_report, dict):
            continue
        lines.append(
            f"- `{task_report.get('task_id', '')}`: `{task_report.get('queue_status', '')}` -> `{task_report.get('next_action', '')}`"
        )
        lines.append(f"  - output: `{task_report.get('official_output_file', '')}`")
        lines.append(f"  - detail: {task_report.get('detail', '')}")
    return "\n".join(lines).rstrip() + "\n"


def _reviewer_config_or_detail(*, require_config: bool) -> tuple[Any, str]:
    try:
        config = load_reviewer_config_from_env()
    except ValueError as exc:
        return None, str(exc)
    if config is None and require_config:
        return None, (
            "semantic reviewer is required for verify but TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON is not configured. "
            "Use review-pack/review-apply for Codex or manual review."
        )
    return config, ""


def _run_semantic_review_for_candidate(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    attempt: int,
    mode: str,
    candidate_path: Path,
    candidate_code: str,
    build_summary: dict[str, Any],
    config: Any,
    allow_missing_config: bool,
) -> dict[str, Any]:
    reviewer_argv_hash = config.argv_hash if config is not None else ""
    backend_id = config.backend_id if config is not None else "missing-reviewer-config"
    context_markdown = build_semantic_review_context_markdown(task, ledger, settings, pack_dir)
    context_path = next_semantic_review_context_path(pack_dir, attempt)
    review_basis = build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind="candidate",
        review_subject_hash=_sha256_text(candidate_code),
        review_subject_file=candidate_path,
    )
    review_input = build_semantic_review_input(
        task=task,
        mode=mode,
        attempt=attempt,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        import_lines=build_import_lines(task),
        dependency_summary=_build_dependency_review_summary(task, ledger, settings),
        search_summary=_build_search_review_summary(pack_dir),
        build_summary=build_summary,
        backend_id=backend_id,
        reviewer_argv_hash=reviewer_argv_hash,
        review_basis=review_basis,
        review_basis_hash=_sha256_json(review_basis),
        review_context_file=str(context_path),
        review_context_hash=_sha256_text(context_markdown),
        review_context_markdown=context_markdown,
    )
    return run_semantic_review(
        pack_dir=pack_dir,
        attempt=attempt,
        review_input=review_input,
        config=config,
        allow_missing_config=allow_missing_config,
    )


def _semantic_review_summary(review_result: dict[str, Any]) -> dict[str, Any]:
    return {
        "verdict": review_result.get("verdict", "inconclusive"),
        "proof_class": review_result.get("proof_class", ""),
        "completion_class": review_result.get("completion_class", ""),
        "phase2_status": review_result.get("phase2_status", review_result.get("task_status", "")),
        "phase2_status_reason": review_result.get("phase2_status_reason", review_result.get("task_status_reason", "")),
        "task_status": review_result.get("task_status", ""),
        "task_status_reason": review_result.get("task_status_reason", ""),
        "needs_class_normalization": bool(review_result.get("needs_class_normalization", False)),
        "runner_status": review_result.get("runner", {}).get("status", ""),
        "summary": review_result.get("summary", ""),
        "recommended_disposition": review_result.get("recommended_disposition", ""),
        "review_result_file": review_result.get("review_result_file", ""),
        "review_input_file": review_result.get("review_input_file", ""),
        "review_prompt_file": review_result.get("review_prompt_file", ""),
        "review_report_file": review_result.get("review_report_file", ""),
        "cache_key": review_result.get("cache_key", ""),
        "cache_hit": bool(review_result.get("cache_hit", False)),
        "reviewer_backend_id": review_result.get("reviewer_backend_id", ""),
    }


def _project_semantic_review_task_status(task: dict[str, Any], review_result: dict[str, Any]) -> dict[str, Any]:
    return project_normalized_semantic_review_result(review_result, task=task).result


def _record_phase2_task_status_projection(
    task_id: str,
    task: dict[str, Any],
    ledger: LedgerManager,
    review_result: dict[str, Any],
) -> dict[str, Any]:
    decision = project_normalized_semantic_review_result(review_result, task=task)
    enriched = decision.result
    if decision.task_status_projection is None:
        return enriched
    ledger.update_runtime_metadata(
        task_id,
        phase2_review_verdict=str(enriched.get("verdict", "") or ""),
        phase2_proof_class=str(enriched.get("proof_class", "") or ""),
        phase2_completion_class=str(enriched.get("completion_class", "") or ""),
        phase2_status=str(enriched.get("phase2_status", "") or ""),
        phase2_status_reason=str(enriched.get("phase2_status_reason", "") or ""),
        phase2_status_evidence_type=str(enriched.get("phase2_status_evidence_type", "") or ""),
        phase2_task_status=str(enriched.get("task_status", "") or ""),
        phase2_task_status_reason=str(enriched.get("task_status_reason", "") or ""),
        phase2_task_status_evidence_type=str(enriched.get("task_status_evidence_type", "") or ""),
        phase2_task_role=str(enriched.get("task_role", "") or ""),
        phase2_needs_class_normalization=bool(enriched.get("needs_class_normalization", False)),
    )
    return enriched


def _review_diagnostics(review_result: dict[str, Any]) -> list[dict[str, Any]]:
    verdict = str(review_result.get("verdict", "inconclusive"))
    kind = "semantic_review_failed" if verdict == "fail" else "semantic_review_inconclusive"
    detail = str(review_result.get("summary", "") or f"Semantic reviewer verdict: {verdict}")
    return [
        {
            "stage": "semantic_review",
            "kind": kind,
            "message": detail,
            "line": None,
            "column": None,
            "blocking_symbols": [],
        }
    ]


def _run_official_module_build(task_id: str, settings) -> tuple[bool, str]:
    proc = subprocess.run(
        ["lake", "build", f"ToyApollo.Output.{task_id}"],
        cwd=str(settings.runtime_root),
        capture_output=True,
        text=True,
    )
    output = "\n".join([part for part in (proc.stdout, proc.stderr) if part])
    return proc.returncode == 0, output


def _run_lean_module_build(module_name: str, settings) -> tuple[bool, str]:
    proc = subprocess.run(
        ["lake", "build", module_name],
        cwd=str(settings.runtime_root),
        capture_output=True,
        text=True,
    )
    output = "\n".join([part for part in (proc.stdout, proc.stderr) if part])
    return proc.returncode == 0, output


def _module_name_from_lean_file(path: Path, settings) -> str:
    try:
        rel = path.resolve().relative_to(Path(settings.runtime_root).resolve())
    except ValueError:
        return ""
    if rel.suffix != ".lean":
        return ""
    return ".".join(rel.with_suffix("").parts)


def _resolve_support_landing_file(raw_path: str, *, pack_dir: Path, settings) -> Path:
    path = Path(raw_path).expanduser()
    if path.is_absolute():
        return path
    candidates = [
        Path(settings.runtime_root) / path,
        pack_dir / path,
        Path.cwd() / path,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    return (Path(settings.runtime_root) / path).resolve()


def _support_review_target_from_obligations(pack_dir: Path, settings) -> dict[str, str]:
    obligations_path = pack_dir / PROOF_OBLIGATIONS_FILE_NAME
    payload = _read_json_safely(obligations_path, {})
    obligations = payload.get("obligations", []) if isinstance(payload, dict) else []
    if not isinstance(obligations, list):
        obligations = []
    for item in obligations:
        if not isinstance(item, dict):
            continue
        landing_file_raw = str(item.get("landing_file", "") or "").strip()
        landing_source = str(item.get("landing_source", "") or "").strip()
        if not landing_file_raw and landing_source != "existing_support":
            continue
        if not landing_file_raw:
            continue
        landing_file = _resolve_support_landing_file(landing_file_raw, pack_dir=pack_dir, settings=settings)
        landing_module = str(item.get("landing_module", "") or "").strip() or _module_name_from_lean_file(landing_file, settings)
        landing_decl = str(item.get("landing_decl", "") or item.get("lean_landing", "") or "").strip()
        return {
            "file": str(landing_file),
            "module": landing_module,
            "decl": landing_decl,
            "obligation_id": str(item.get("id", "") or "").strip(),
        }
    return {}


async def write_existing_support_review_pack(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    force_new_attempt: bool = False,
) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not _path_exists(pack_dir):
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)

    target = _support_review_target_from_obligations(pack_dir, settings)
    if not target:
        return False, (
            "No existing support landing was declared. Add landing_source=existing_support "
            "and landing_file to a proof_obligations.json item first."
        )
    output_path = Path(target["file"])
    if not output_path.exists():
        return False, f"Support landing file does not exist: {output_path}"
    module_name = str(target.get("module", "") or "")
    if not module_name:
        return False, f"Could not infer Lean module name for support landing file: {output_path}"
    candidate_code = _read_file_safely(output_path)

    sanity_success, sanity_output = _run_lean_module_build(module_name, settings)
    if not sanity_success:
        _clear_current_review_metadata(task_id, ledger)
        diagnostics = _parse_diagnostics(sanity_output, "final_build_failed", "review_support_sanity_build")
        _write_review_compat_summary(
            task_id=task_id,
            ledger=ledger,
            task=task,
            settings=settings,
            pack_dir=pack_dir,
            mode="review-support",
            candidate_path=output_path,
            candidate_code=candidate_code,
            detail_text=sanity_output or f"lake build {module_name} failed before review-support.",
            diagnostics=diagnostics,
            disposition="review_support_build_failed_no_review",
            semantic_review=None,
            state_transition="none",
        )
        return False, sanity_output or f"lake build {module_name} failed before review-support."

    prepared = _prepare_existing_output_review_materials(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        output_path=output_path,
        mode="review-support",
        build_output=sanity_output,
        force_new_attempt=force_new_attempt,
        review_subject_kind="existing_support",
    )
    snapshot_path = prepared["snapshot_path"]
    ledger.update_runtime_metadata(task_id, latest_support_snapshot_file=str(snapshot_path))
    _set_current_review_metadata(
        task_id,
        ledger,
        input_file=str(prepared["input_path"]),
        prompt_file=str(prepared["prompt_path"]),
        template_file=str(prepared["template_path"]),
        context_file=str(prepared["context_path"]),
        request_file=str(prepared.get("request_path") or ""),
        backend_id="codex-handoff",
        expected_result_file=str(prepared["result_path"] if prepared["result_path"] is not None else next_semantic_review_artifact_paths(pack_dir, prepared["attempt"])["result"]),
        subject_kind="existing_support",
        subject_file=str(snapshot_path),
        subject_hash=str(prepared["candidate_hash"]),
        origin="review-support",
    )
    semantic_review = {
        "verdict": "inconclusive",
        "runner": {"status": "codex_handoff_pending"},
        "summary": "Existing support landing frozen for semantic review.",
        "recommended_disposition": "manual_review",
        "review_input_file": str(prepared["input_path"]),
        "review_prompt_file": str(prepared["prompt_path"]),
        "review_context_file": str(prepared["context_path"]),
        "review_result_template_file": str(prepared["template_path"]),
        "expected_review_result_file": str(prepared["result_path"]) if prepared["result_path"] is not None else str(next_semantic_review_artifact_paths(pack_dir, prepared["attempt"])["result"]),
        "cache_hit": False,
        "reviewer_backend_id": "codex-handoff",
    }
    _write_review_compat_summary(
        task_id=task_id,
        ledger=ledger,
        task=task,
        settings=settings,
        pack_dir=pack_dir,
        mode="review-support",
        candidate_path=snapshot_path,
        candidate_code=str(prepared["candidate_code"]),
        detail_text="Existing support landing frozen for semantic review; apply a filled semantic_review_result JSON with review-apply.",
        diagnostics=[],
        disposition="review_support_required",
        semantic_review=semantic_review,
        state_transition="none",
    )
    return True, "Existing support landing frozen for semantic review; apply a filled semantic_review_result JSON with review-apply."


def _next_quarantine_dir(pack_dir: Path) -> Path:
    existing = []
    for path in pack_dir.glob("rejected_official_v*"):
        match = re.fullmatch(r"rejected_official_v(\d+)", path.name)
        if match and path.is_dir():
            existing.append(int(match.group(1)))
    return pack_dir / f"rejected_official_v{(max(existing) if existing else 0) + 1}"


def _quarantine_official_outputs(
    *,
    task_id: str,
    source_plan: str,
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    reason: str,
    result_path: Path,
) -> Path:
    quarantine_dir = _next_quarantine_dir(pack_dir)
    quarantine_dir.mkdir(parents=True, exist_ok=False)
    manifest: dict[str, Any] = {
        "task_id": task_id,
        "created_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "reason": reason,
        "result_file": str(result_path),
        "files": [],
    }
    targets = [target for target in iter_official_output_targets(task_id, source_plan, settings) if target.exists()]
    for target in targets:
        copied = quarantine_dir / target.name
        if copied.exists():
            copied = quarantine_dir / f"{target.parent.name}_{target.name}"
        content = _read_file_safely(target)
        shutil.copyfile(target, copied)
        manifest["files"].append(
            {
                "original_path": str(target),
                "quarantine_path": str(copied),
                "sha256": hashlib.sha256(content.encode("utf-8")).hexdigest() if content else "",
            }
        )
    _write_json(quarantine_dir / "quarantine_manifest.json", manifest)
    for target in targets:
        if target.exists():
            target.unlink()
    ledger.update_runtime_metadata(task_id, latest_quarantine_dir=str(quarantine_dir))
    return quarantine_dir


def rollback_false_positive_completed_task(task_id: str, ledger: LedgerManager, settings) -> bool:
    task_id = canonicalize_block_id(task_id)
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_record = ledger.ledger.get("tasks", {}).get(task_id)
    if not isinstance(task_record, dict):
        return False

    source_plan = str(task.get("source_plan", "unknown") or "unknown")

    ledger.update_status(task_id, TaskStatus.PACKED)
    _remove_symbols_owned_by_task(task_id, ledger)
    ledger.update_runtime_metadata(
        task_id,
        output_hash=None,
        exported_symbols=[],
        latest_verify_result_file="",
        last_error="",
        last_align_error="",
    )

    for target in iter_official_output_targets(task_id, source_plan, settings):
        if target.exists():
            target.unlink()

    return True


def _remove_symbols_owned_by_task(task_id: str, ledger: LedgerManager) -> None:
    ledger.remove_symbols_owned_by_task(task_id)


def audit_completed_task_output(task_id: str, ledger: LedgerManager, settings) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    audit_original_status = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("status", ""))

    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not _path_exists(pack_dir):
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)

    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    output_path = settings.toyapollo_output_dir / f"{task_id}.lean"
    if not output_path.exists():
        existing = find_existing_task_file(task_id, source_plan, settings)
        if existing is None or not existing.exists():
            raise FileNotFoundError(f"Official output file does not exist for audit: {task_id}")
        output_path = existing

    candidate_code = _read_file_safely(output_path)
    attempt = len(_list_versioned_json_files(pack_dir, "verify_result")) + 1
    verify_result_path = _next_verify_result_path(pack_dir, attempt)
    verified_at = datetime.now(UTC).isoformat().replace("+00:00", "Z")

    def write_audit_result(
        *,
        success: bool,
        diagnostics: list[dict[str, Any]],
        detail: str,
        final_build_success: bool = True,
        final_build_output: str = "",
        semantic_review: dict[str, Any] | None = None,
        disposition: str = "",
        state_transition: str = "none",
    ) -> dict[str, Any]:
        verify_result = _build_verify_result_payload(
            task_id=task_id,
            attempt=attempt,
            candidate_path=output_path,
            candidate_code=candidate_code,
            verified_at=verified_at,
            repl_success=success,
            repl_output=detail,
            temp_build_success=success,
            temp_build_output=detail,
            final_build_success=final_build_success,
            final_build_output=final_build_output or detail,
            diagnostics=diagnostics,
        )
        verify_result["mode"] = "audit"
        verify_result["success"] = success
        verify_result["disposition"] = disposition
        verify_result["state_transition"] = state_transition
        if semantic_review is not None:
            verify_result["semantic_review"] = _semantic_review_summary(semantic_review)
        verify_result["verify_result_file"] = str(verify_result_path)
        _write_json(verify_result_path, verify_result)
        history = _append_attempt_history(pack_dir, task_id, verify_result)
        (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(
            build_failure_summary_markdown(task_id, history),
            encoding="utf-8",
        )
        (pack_dir / "build_feedback.txt").write_text("" if success else detail, encoding="utf-8")
        _append_verification_report(pack_dir, verify_result, detail)
        ledger.mark_verifying(
            task_id,
            latest_verify_result_file=str(verify_result_path),
            verify_attempts=attempt,
        )
        _set_latest_operation(task_id, ledger, kind="audit", file_path=str(verify_result_path))
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return verify_result

    def preserve_official_output_after_audit_failure(disposition: str, detail: str) -> None:
        if audit_original_status:
            try:
                ledger.update_status(task_id, TaskStatus(audit_original_status))
            except ValueError:
                pass
        ledger.update_runtime_metadata(
            task_id,
            latest_official_audit_disposition=disposition,
            latest_official_audit_result_file=str(verify_result_path),
            latest_official_audit_requires_repair=True,
            latest_official_audit_detail=detail,
            official_output_quarantine_policy="not_quarantined_by_default",
        )

    hard_ok, diagnostics, detail = validate_candidate_hard_checks(task, candidate_code, ledger)
    if not hard_ok:
        disposition = "audit_hard_check_failed"
        write_audit_result(
            success=False,
            diagnostics=diagnostics,
            detail=detail,
            final_build_success=False,
            disposition=disposition,
            state_transition="audit_failed_no_quarantine",
        )
        preserve_official_output_after_audit_failure(disposition, detail)
        return False, detail

    final_success, final_output = _run_official_module_build(task_id, settings)
    if not final_success:
        diagnostics = _parse_diagnostics(final_output, "final_build_failed", "audit_final_build")
        detail = final_output or f"lake build ToyApollo.Output.{task_id} failed during audit."
        disposition = "audit_final_build_failed"
        write_audit_result(
            success=False,
            diagnostics=diagnostics,
            detail=detail,
            final_build_success=False,
            final_build_output=final_output,
            disposition=disposition,
            state_transition="audit_failed_no_quarantine",
        )
        preserve_official_output_after_audit_failure(disposition, detail)
        return False, detail

    config, config_error = _reviewer_config_or_detail(require_config=False)
    if config_error:
        detail = config_error
        review_result = _run_semantic_review_for_candidate(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            attempt=attempt,
            mode="audit",
            candidate_path=output_path,
            candidate_code=candidate_code,
            build_summary={"final_build": {"success": final_success, "output": final_output}, "config_error": config_error},
            config=None,
            allow_missing_config=True,
        )
    else:
        review_result = _run_semantic_review_for_candidate(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            attempt=attempt,
            mode="audit",
            candidate_path=output_path,
            candidate_code=candidate_code,
            build_summary={"final_build": {"success": final_success, "output": final_output}},
            config=config,
            allow_missing_config=True,
        )
        detail = str(review_result.get("summary", ""))

    verdict = str(review_result.get("verdict", "inconclusive"))
    cache_class = str(review_result.get("cache_class", "semantic_verdict") or "semantic_verdict").strip().lower()
    if cache_class != "semantic_verdict":
        detail = detail or str(review_result.get("normalization_reason", "") or "Semantic audit reviewer output was invalid.")
        diagnostics = _hard_check_diagnostic("invalid_reviewer_output", detail)
        write_audit_result(
            success=False,
            diagnostics=diagnostics,
            detail=detail,
            final_build_success=True,
            final_build_output=final_output,
            semantic_review=review_result,
            disposition="audit_invalid_reviewer_output",
            state_transition="none",
        )
        if audit_original_status:
            try:
                ledger.update_status(task_id, TaskStatus(audit_original_status))
            except ValueError:
                pass
        return False, detail
    review_result = _record_phase2_task_status_projection(task_id, task, ledger, review_result)
    verdict = str(review_result.get("verdict", "inconclusive"))
    if verdict == "pass":
        non_clean = str(review_result.get("task_status", "") or "") != "pass"
        disposition = "audit_pass_non_clean_report" if non_clean else "audit_pass_report"
        detail_text = detail or "Semantic audit passed; report only."
        if non_clean:
            detail_text = (
                f"{detail_text} Non-clean audit: review verdict is pass, but task_status="
                f"{review_result.get('task_status', '')}; this is not textbook completion."
            )
        write_audit_result(
            success=not non_clean,
            diagnostics=[] if not non_clean else _hard_check_diagnostic("phase2_status_not_pass", str(review_result.get("task_status_reason", "") or "")),
            detail=detail_text,
            final_build_success=True,
            final_build_output=final_output,
            semantic_review=review_result,
            disposition=disposition,
            state_transition="none",
        )
        if audit_original_status:
            try:
                ledger.update_status(task_id, TaskStatus(audit_original_status))
            except ValueError:
                pass
        return not non_clean, detail_text

    diagnostics = _review_diagnostics(review_result)
    if verdict == "fail":
        detail = detail or "Semantic audit failed."
        disposition = "audit_semantic_fail"
        write_audit_result(
            success=False,
            diagnostics=diagnostics,
            detail=detail,
            final_build_success=True,
            final_build_output=final_output,
            semantic_review=review_result,
            disposition=disposition,
            state_transition="audit_failed_no_quarantine",
        )
        preserve_official_output_after_audit_failure(disposition, detail)
        return False, detail

    detail = (
        f"Semantic audit inconclusive: {detail}"
        if detail
        else "Semantic audit was inconclusive; ledger and official output were left unchanged."
    )
    write_audit_result(
        success=False,
        diagnostics=diagnostics,
        detail=detail,
        final_build_success=True,
        final_build_output=final_output,
        semantic_review=review_result,
        disposition="audit_inconclusive_no_state_change",
        state_transition="none",
    )
    if audit_original_status:
        try:
            ledger.update_status(task_id, TaskStatus(audit_original_status))
        except ValueError:
            pass
    return False, detail


def write_prompt_pack(task_id: str, ledger: LedgerManager, settings, task: dict[str, Any] | None = None) -> Path:
    if task is None:
        task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    else:
        task = canonicalize_task_dict(task)

    task_id = canonicalize_block_id(task_id)
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    output_binding = resolve_phase2_output_binding(task, ledger, settings)

    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    snapshot = current_record.get("candidate_snapshot", {})
    if not isinstance(snapshot, dict):
        snapshot = {}
    task["dependencies"] = canonicalize_id_list(task.get("dependencies", []))
    task["soft_imports"] = canonicalize_id_list(task.get("soft_imports", []) + snapshot.get("soft_imports", []))
    task["final_import_union"] = _task_final_import_union(task)
    _raise_if_hard_dependency_has_proof_debt(task, ledger)
    _make_dirs(pack_dir, exist_ok=True)
    soft_confirmed = ledger.has_confirmed_soft_imports(task_id)
    if str(task.get("type", "")).strip().lower() == "problem" and not soft_confirmed:
        raise ValueError(
            f"Problem task {task_id} does not have confirmed soft selection. "
            "Run --phase 2 --phase2-mode soft-pack/soft-apply first."
        )

    pack_round = int(current_record.get("pack_round", 0) or 0) + 1
    candidate_files = [p.name for p in list_candidate_files(pack_dir)]
    latest_candidate = current_record.get("latest_candidate_file", "")
    latest_pack_candidate = select_latest_candidate(pack_dir)
    if latest_pack_candidate is not None:
        latest_candidate = str(latest_pack_candidate)

    import_lines = build_import_lines(task)
    existing_file = find_existing_task_file(
        output_binding.output_owner_task_id,
        task.get("source_plan", "unknown"),
        settings,
    )
    existing_code = _read_file_safely(existing_file) if existing_file else ""
    fallback_stub_text = build_target_stub(task, import_lines, existing_code=existing_code)
    target_stub_text = (
        build_obligation_target_stub(existing_code, fallback_stub_text)
        if output_binding.is_obligation_task
        else fallback_stub_text
    )
    target_stub_path = pack_dir / "target_stub.lean"
    draft_path = pack_dir / DRAFT_FILE_NAME
    intent_contract = ensure_intent_contract(pack_dir, task)
    proof_obligations = maybe_ensure_proof_obligations_file(
        pack_dir,
        task,
        current_record=current_record if isinstance(current_record, dict) else {},
        tracking_level=2,
    )
    proof_obligation_summary = summarize_proof_obligations(proof_obligations) if proof_obligations is not None else {}
    search_manifest = build_search_manifest(task, ledger, settings)
    search_manifest_path = pack_dir / SEARCH_MANIFEST_FILE_NAME
    history = _ensure_attempt_history(pack_dir, task_id)
    failure_summary_text = build_failure_summary_markdown(task_id, history)
    failure_summary_path = pack_dir / FAILURE_SUMMARY_FILE_NAME
    _sync_stale_build_ready_candidate(task_id, ledger, settings, pack_dir)
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    active_official_output = _has_active_official_output(task_id, str(task.get("source_plan", "unknown") or "unknown"), ledger, settings)
    current_state = str(current_record.get("pack_candidate_state", "draft") or "draft")
    has_valid_ready = bool(str(current_record.get("latest_build_ready_candidate_file", "") or ""))
    next_pack_state = current_state if has_valid_ready and current_state in {"build_ready", "review_pending", "review_rejected"} else "draft"

    should_seed_draft = not _path_exists(draft_path)
    if output_binding.is_obligation_task and _path_exists(draft_path):
        should_seed_draft = not has_top_level_declaration(_read_file_safely(draft_path))

    if should_seed_draft:
        if latest_pack_candidate is not None:
            _shared_write_text(draft_path, _read_file_safely(latest_pack_candidate))
        elif latest_candidate and _path_exists(Path(latest_candidate)):
            _shared_write_text(draft_path, _read_file_safely(Path(latest_candidate)))
        else:
            _shared_write_text(draft_path, target_stub_text)

    task_payload = {
        "block_id": task["block_id"],
        "type": task.get("type", "Unknown"),
        "title": task.get("title", ""),
        "content": task.get("content", ""),
        "source_plan": task.get("source_plan", "unknown"),
        "dependencies": task.get("dependencies", []),
        "soft_imports": task.get("soft_imports", []),
        "soft_imports_confirmed_at": current_record.get("soft_imports_confirmed_at", ""),
        "final_import_union": _task_final_import_union(task),
    }

    metadata_payload = {
        "task_id": task_id,
        "status_before_pack": current_record.get("status", TaskStatus.DISCOVERED.value),
        "pack_generated_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "pack_round": pack_round,
        "latest_candidate_file": latest_candidate,
        "soft_imports_confirmed_at": current_record.get("soft_imports_confirmed_at", ""),
        "candidate_files": candidate_files,
        "soft_imports": task.get("soft_imports", []),
        "final_import_union": canonicalize_id_list(task.get("dependencies", []) + task.get("soft_imports", [])),
        "draft_file": str(draft_path),
        "intent_contract_file": str(_intent_contract_path(pack_dir)),
        "proof_obligations_file": str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME) if proof_obligations is not None else "",
        "proof_obligation_summary": proof_obligation_summary,
        "output_owner_task_id": output_binding.output_owner_task_id,
        "output_module": output_binding.output_module,
        "official_output_targets": [target.as_posix() for target in output_binding.official_targets],
        "proof_obligations_owner_file": output_binding.proof_obligations_file.as_posix(),
        "focus_obligation_ids": output_binding.focus_obligation_ids,
        "search_manifest_file": str(search_manifest_path),
        "attempt_history_file": str(pack_dir / ATTEMPT_HISTORY_FILE_NAME),
        "failure_summary_file": str(failure_summary_path),
        "intent_contract": intent_contract,
        "pack_candidate_state": next_pack_state,
    }

    _write_json(pack_dir / "task.json", task_payload)
    _write_json(pack_dir / "metadata.json", metadata_payload)
    _write_json(search_manifest_path, search_manifest)
    write_dependency_decision_context(pack_dir, task_payload, settings)
    _shared_write_text(failure_summary_path, failure_summary_text)
    _shared_write_text(pack_dir / "operator_prompt.md", build_operator_prompt(task))
    _shared_write_text(pack_dir / "context.md", build_context_markdown(task, ledger, settings, pack_dir))
    _shared_write_text(pack_dir / "search_notes.md", build_search_notes(task, ledger, settings, search_manifest))
    _shared_write_text(pack_dir / "imports.lean", "\n".join(import_lines).strip() + "\n")
    _shared_write_text(target_stub_path, target_stub_text)
    _shared_write_text(pack_dir / "build_feedback.txt", "")
    if not _path_exists(pack_dir / "verification_report.md"):
        _shared_write_text(pack_dir / "verification_report.md", f"# Verification Report for {task_id}\n\n")
    if not active_official_output:
        ledger.update_status(task_id, TaskStatus.PACKED)
    ledger.mark_packed(
        task_id,
        pack_round=pack_round,
        latest_candidate_file=latest_candidate,
        latest_search_manifest_file=str(search_manifest_path),
    )
    ledger.update_runtime_metadata(
        task_id,
        pack_candidate_state=next_pack_state,
        draft_file=str(draft_path),
        proof_obligations_file=str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME) if proof_obligations is not None else "",
        proof_obligation_summary=proof_obligation_summary,
    )
    _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return pack_dir


def resolve_candidate_path(pack_dir: Path, candidate_arg: str | None = None) -> Path:
    if candidate_arg:
        candidate_path = Path(candidate_arg).expanduser()
        if not candidate_path.is_absolute():
            candidate_path = (Path.cwd() / candidate_path).resolve()
        if not _path_exists(candidate_path):
            raise FileNotFoundError(f"Candidate file not found: {candidate_path}")
        return candidate_path

    draft_path = pack_dir / DRAFT_FILE_NAME
    if _path_exists(draft_path):
        return draft_path

    candidate_path = select_latest_candidate(pack_dir)
    if candidate_path is not None:
        return candidate_path
    raise FileNotFoundError(f"Neither {DRAFT_FILE_NAME} nor candidate_v*.lean exists in {pack_dir}")


def _extract_line_column(raw_line: str) -> tuple[int | None, int | None]:
    repl_match = re.search(r"Line (\d+), Col (\d+)", raw_line)
    if repl_match:
        return int(repl_match.group(1)), int(repl_match.group(2))
    build_match = re.search(r":(\d+):(\d+):", raw_line)
    if build_match:
        return int(build_match.group(1)), int(build_match.group(2))
    return None, None


def _extract_blocking_symbols(raw_line: str) -> list[str]:
    patterns = [
        r"unknown identifier '?([A-Za-z_][A-Za-z0-9_']*)'?",
        r"unknown constant '?([A-Za-z_][A-Za-z0-9_']*)'?",
        r"for '([A-Za-z_][A-Za-z0-9_']*)' first",
        r"depends on '([A-Za-z_][A-Za-z0-9_']*)'",
        r"`([A-Za-z_][A-Za-z0-9_']*)`",
    ]
    symbols: list[str] = []
    for pattern in patterns:
        for match in re.findall(pattern, raw_line):
            if match not in symbols:
                symbols.append(match)
    return symbols


def _classify_diagnostic_kind(raw_line: str, fallback_kind: str) -> str:
    lowered = raw_line.lower()
    if "unknown identifier" in lowered or "unknown constant" in lowered:
        return "unknown_identifier"
    if "noncomputable" in lowered:
        return "noncomputable_required"
    if "type mismatch" in lowered or "application type mismatch" in lowered or ("expected" in lowered and "has type" in lowered):
        return "type_mismatch"
    if "sorry" in lowered or "incomplete proof" in lowered:
        return "contains_sorry"
    if "unknown package" in lowered or "could not find module" in lowered or "object file" in lowered:
        return "missing_import"
    return fallback_kind


def _parse_diagnostics(raw_output: str, fallback_kind: str, stage: str) -> list[dict[str, Any]]:
    diagnostics: list[dict[str, Any]] = []
    seen: set[tuple[str, int | None, int | None, str]] = set()
    for raw_line in [line.strip() for line in raw_output.splitlines() if line.strip()]:
        if not any(token in raw_line.lower() for token in ("error", "failed", "sorry", "unknown", "noncomputable", "mismatch")):
            continue
        line_no, column = _extract_line_column(raw_line)
        kind = _classify_diagnostic_kind(raw_line, fallback_kind)
        blocking_symbols = _extract_blocking_symbols(raw_line)
        key = (kind, line_no, column, raw_line)
        if key in seen:
            continue
        seen.add(key)
        diagnostics.append(
            {
                "stage": stage,
                "kind": kind,
                "message": raw_line,
                "line": line_no,
                "column": column,
                "blocking_symbols": blocking_symbols,
            }
        )
    if diagnostics:
        return diagnostics
    if raw_output.strip():
        return [
            {
                "stage": stage,
                "kind": fallback_kind,
                "message": raw_output.strip().splitlines()[0],
                "line": None,
                "column": None,
                "blocking_symbols": _extract_blocking_symbols(raw_output),
            }
        ]
    return []


def _primary_failure_kind(diagnostics: list[dict[str, Any]]) -> str:
    priority = [
        "semantic_reviewer_config_missing",
        "semantic_review_failed",
        "semantic_review_inconclusive",
        "empty_candidate",
        "missing_target_declaration",
        "self_import",
        "undeclared_local_import",
        "theorem_declared_as_prop_def",
        "axiom_placeholder",
        "vacuous_candidate",
        "overspecialized_candidate",
        "reversed_example_logic",
        "example_wrapped_theorem",
        "weakened_statement",
        "missing_required_coverage",
        MISSING_LOCAL_FOUNDATION_LEMMA_KIND,
        "missing_import",
        "unknown_identifier",
        "noncomputable_required",
        "type_mismatch",
        "contains_sorry",
        "final_build_failed",
        "temp_build_failed",
        "repl_failed",
    ]
    kinds = {str(item.get("kind", "")) for item in diagnostics}
    for kind in priority:
        if kind in kinds:
            return kind
    return ""


def _collect_blocking_symbols(diagnostics: list[dict[str, Any]]) -> list[str]:
    symbols: list[str] = []
    for item in diagnostics:
        raw_symbols = item.get("blocking_symbols", [])
        if not isinstance(raw_symbols, list):
            continue
        for symbol in raw_symbols:
            if symbol not in symbols:
                symbols.append(symbol)
    return symbols


def _task_local_missing_symbols(task_id: str, symbols: list[Any]) -> list[str]:
    raw_task_id = str(task_id or "").strip()
    canonical_task_id = canonicalize_block_id(raw_task_id) if raw_task_id else ""
    prefixes = {item for item in (raw_task_id, canonical_task_id) if item}
    local_symbols: list[str] = []
    for raw_symbol in symbols:
        symbol = str(raw_symbol or "").strip()
        if not symbol:
            continue
        if any(symbol == prefix or symbol.startswith(f"{prefix}_") for prefix in prefixes):
            local_symbols.append(symbol)
    return local_symbols


def _reclassify_task_local_missing_lemmas(
    task_id: str, diagnostics: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    reclassified: list[dict[str, Any]] = []
    for item in diagnostics:
        if not isinstance(item, dict):
            continue
        if str(item.get("kind", "")) != "unknown_identifier":
            reclassified.append(item)
            continue
        local_symbols = _task_local_missing_symbols(task_id, item.get("blocking_symbols", []))
        if not local_symbols:
            reclassified.append(item)
            continue
        updated = dict(item)
        updated["kind"] = MISSING_LOCAL_FOUNDATION_LEMMA_KIND
        updated["local_missing_symbols"] = local_symbols
        updated["repair_action"] = "prove_or_split_task_local_foundation_lemma"
        reclassified.append(updated)
    return reclassified


def _compose_detail_text(repl_output: str, temp_build_output: str, final_build_output: str = "") -> str:
    sections: list[str] = []
    if repl_output.strip():
        sections.append("[REPL]\n" + repl_output.strip())
    if temp_build_output.strip():
        sections.append("[TEMP BUILD]\n" + temp_build_output.strip())
    if final_build_output.strip():
        sections.append("[FINAL BUILD]\n" + final_build_output.strip())
    return "\n\n".join(sections).strip() or "(no detail)"


def _is_repl_timeout_output(repl_output: str) -> bool:
    lowered = str(repl_output or "").lower()
    return "repl system error" in lowered and "timed out" in lowered


def _build_verify_result_payload(
    *,
    task_id: str,
    attempt: int,
    candidate_path: Path,
    candidate_code: str,
    verified_at: str,
    repl_success: bool,
    repl_output: str,
    temp_build_success: bool,
    temp_build_output: str,
    final_build_success: bool,
    final_build_output: str,
    diagnostics: list[dict[str, Any]],
) -> dict[str, Any]:
    diagnostics = _reclassify_task_local_missing_lemmas(task_id, diagnostics)
    primary_failure_kind = _primary_failure_kind(diagnostics)
    blocking_symbols = _collect_blocking_symbols(diagnostics)
    return {
        "task_id": task_id,
        "attempt": attempt,
        "candidate_file": str(candidate_path),
        "candidate_hash": _sha256_text(candidate_code) if candidate_code else "",
        "verified_at": verified_at,
        "success": repl_success and temp_build_success and final_build_success,
        "repl": {"success": repl_success, "output": repl_output},
        "temp_build": {"success": temp_build_success, "output": temp_build_output},
        "final_build": {"success": final_build_success, "output": final_build_output},
        "diagnostics": diagnostics,
        "primary_failure_kind": primary_failure_kind,
        "blocking_symbols": blocking_symbols,
        "raw_outputs": {
            "repl": repl_output,
            "temp_build": temp_build_output,
            "final_build": final_build_output,
        },
    }


def _build_build_result_payload(
    *,
    task_id: str,
    attempt: int,
    candidate_path: Path,
    candidate_code: str,
    candidate_kind: str,
    built_at: str,
    hard_checks_success: bool,
    repl_success: bool,
    repl_output: str,
    temp_build_success: bool,
    temp_build_output: str,
    final_build_success: bool,
    final_build_output: str,
    diagnostics: list[dict[str, Any]],
    disposition: str,
) -> dict[str, Any]:
    diagnostics = _reclassify_task_local_missing_lemmas(task_id, diagnostics)
    primary_failure_kind = _primary_failure_kind(diagnostics)
    blocking_symbols = _collect_blocking_symbols(diagnostics)
    return {
        "schema_version": "phase2.build_result.v1",
        "task_id": task_id,
        "attempt": attempt,
        "candidate_kind": candidate_kind,
        "candidate_file": str(candidate_path),
        "candidate_hash": _sha256_text(candidate_code) if candidate_code else "",
        "built_at": built_at,
        "hard_checks": {"success": hard_checks_success},
        "repl": {"success": repl_success, "output": repl_output},
        "temp_build": {"success": temp_build_success, "output": temp_build_output},
        "final_build": {"success": final_build_success, "output": final_build_output},
        "success": hard_checks_success and repl_success and temp_build_success and final_build_success,
        "diagnostics": diagnostics,
        "primary_failure_kind": primary_failure_kind,
        "blocking_symbols": blocking_symbols,
        "disposition": disposition,
    }


def _append_attempt_history(
    pack_dir: Path,
    task_id: str,
    payload: dict[str, Any],
    *,
    stage: str = "legacy_verify",
) -> dict[str, Any]:
    history = _load_attempt_history(pack_dir, task_id)
    attempts = history.get("attempts", [])
    if not isinstance(attempts, list):
        attempts = []
    latest_kind = str(payload.get("primary_failure_kind") or "")
    repeated_failure = False
    if attempts and latest_kind:
        previous = attempts[-1]
        if (
            isinstance(previous, dict)
            and str(previous.get("primary_failure_kind") or "") == latest_kind
            and str(previous.get("stage", "legacy_verify")) == stage
        ):
            repeated_failure = True
    result_file = (
        str(payload.get("build_result_file", "") or "")
        or str(payload.get("verify_result_file", "") or "")
        or str(payload.get("review_result_file", "") or "")
    )
    attempts.append(
        {
            "attempt": payload.get("attempt"),
            "candidate_file": payload.get("candidate_file"),
            "candidate_hash": payload.get("candidate_hash"),
            "verified_at": payload.get("verified_at") or payload.get("built_at") or _utc_now_z(),
            "success": payload.get("success", False),
            "primary_failure_kind": payload.get("primary_failure_kind", ""),
            "blocking_symbols": payload.get("blocking_symbols", []),
            "stage": stage,
            "result_file": result_file,
            "verify_result_file": str(payload.get("verify_result_file", "") or ""),
            "build_result_file": str(payload.get("build_result_file", "") or ""),
            "review_result_file": str(payload.get("review_result_file", "") or ""),
            "review_verdict": str(payload.get("review_verdict", "") or ""),
            "disposition": str(payload.get("disposition", "") or ""),
            "review_summary": str(payload.get("review_summary", "") or ""),
            "review_subject_kind": str(payload.get("review_subject_kind", "") or ""),
            "repair_request_file": str(payload.get("repair_request_file", "") or ""),
            "auto_loop_round": payload.get("auto_loop_round"),
            "auto_loop_phase": str(payload.get("auto_loop_phase", "") or ""),
            "auto_loop_entry_subject": str(payload.get("auto_loop_entry_subject", "") or ""),
            "repeated_failure": repeated_failure,
        }
    )
    history["task_id"] = task_id
    history["attempts"] = attempts
    _write_json(pack_dir / ATTEMPT_HISTORY_FILE_NAME, history)
    return history


def _record_semantic_review_attempt(
    *,
    pack_dir: Path,
    task_id: str,
    candidate_path: Path,
    candidate_code: str,
    verify_result_path: Path,
    semantic_review: dict[str, Any],
    disposition: str,
    review_subject_kind: str,
    success: bool,
    repair_ready: dict[str, Any] | None,
    auto_loop_metadata: dict[str, Any] | None = None,
) -> dict[str, Any]:
    verify_result = _read_json_safely(verify_result_path, {})
    if not isinstance(verify_result, dict):
        verify_result = {}
    review_verdict = str(semantic_review.get("verdict", "") or ("pass" if success else "inconclusive"))
    if success:
        primary_failure_kind = ""
    elif disposition.endswith("_invalid_no_promotion"):
        primary_failure_kind = "semantic_review_invalid"
    elif review_verdict == "fail":
        primary_failure_kind = "semantic_review_fail"
    elif review_verdict == "inconclusive":
        primary_failure_kind = "semantic_review_inconclusive"
    else:
        primary_failure_kind = "semantic_review_blocked"
    triage_result = {}
    if isinstance(repair_ready, dict):
        request_payload = repair_ready.get("request_payload", {})
        if isinstance(request_payload, dict):
            raw_triage = request_payload.get("semantic_fail_triage", {})
            if isinstance(raw_triage, dict):
                triage_result = raw_triage
    history = _append_attempt_history(
        pack_dir,
        task_id,
        {
            "attempt": verify_result.get("attempt"),
            "candidate_file": str(candidate_path),
            "candidate_hash": _sha256_text(candidate_code) if candidate_code else "",
            "verified_at": verify_result.get("verified_at") or _utc_now_z(),
            "success": success,
            "primary_failure_kind": primary_failure_kind,
            "verify_result_file": str(verify_result_path),
            "review_result_file": str(semantic_review.get("review_result_file", "") or ""),
            "review_verdict": review_verdict,
            "proof_class": str(semantic_review.get("proof_class", "") or ""),
            "completion_class": str(semantic_review.get("completion_class", "") or ""),
            "task_status": str(semantic_review.get("task_status", "") or ""),
            "task_status_reason": str(semantic_review.get("task_status_reason", "") or ""),
            "disposition": disposition,
            "review_summary": str(semantic_review.get("summary", "") or ""),
            "review_subject_kind": review_subject_kind,
            "repair_request_file": str(repair_ready.get("request_path", "") if repair_ready else ""),
            "semantic_fail_triage_file": str(triage_result.get("triage_path", "") or ""),
            "semantic_fail_triage_category": str(triage_result.get("category", "") or ""),
            "semantic_fail_needs_diagnoser": bool(triage_result.get("needs_diagnoser", False)),
            "diagnoser_prompt_file": str(triage_result.get("prompt_path", "") or ""),
            "diagnosis_state": str(triage_result.get("diagnosis_state", "") or ""),
            **(auto_loop_metadata or {}),
        },
        stage="semantic_review",
    )
    _shared_write_text(pack_dir / FAILURE_SUMMARY_FILE_NAME, build_failure_summary_markdown(task_id, history))
    return history


def _backfill_semantic_repair_history_from_request(
    *,
    pack_dir: Path,
    task_id: str,
    request_path: Path,
    request_payload: dict[str, Any],
    failed_review_result: dict[str, Any],
    failed_review_subject_path: Path,
) -> dict[str, Any]:
    history = _load_attempt_history(pack_dir, task_id)
    attempts = history.get("attempts", [])
    if not isinstance(attempts, list):
        attempts = []
    review_result_file = str(request_payload.get("failed_review_result_file", "") or "")
    request_file = str(request_path)
    for item in reversed(attempts):
        if not isinstance(item, dict):
            continue
        if str(item.get("stage", "") or "") != "semantic_review":
            continue
        if (
            str(item.get("review_result_file", "") or "") == review_result_file
            and str(item.get("repair_request_file", "") or "") == request_file
        ):
            return history

    review_subject_kind = str(request_payload.get("review_subject_kind", "") or "candidate")
    review_verdict = str(failed_review_result.get("verdict", "") or "inconclusive").strip().lower()
    if review_subject_kind == "official_output":
        disposition = "official_output_review_fail" if review_verdict == "fail" else "official_output_review_inconclusive"
    else:
        disposition = "codex_review_fail_no_promotion" if review_verdict == "fail" else "codex_review_inconclusive_no_promotion"
    if review_verdict == "fail":
        primary_failure_kind = "semantic_review_fail"
    else:
        primary_failure_kind = "semantic_review_inconclusive"
    candidate_code = _read_file_safely(failed_review_subject_path)
    history = _append_attempt_history(
        pack_dir,
        task_id,
        {
            "attempt": request_payload.get("origin_review_attempt") or len(attempts) + 1,
            "candidate_file": str(failed_review_subject_path),
            "candidate_hash": _sha256_text(candidate_code) if candidate_code else str(request_payload.get("failed_review_subject_hash", "") or ""),
            "verified_at": _utc_now_z(),
            "success": False,
            "primary_failure_kind": primary_failure_kind,
            "review_result_file": review_result_file,
            "review_verdict": review_verdict,
            "disposition": disposition,
            "review_summary": str(failed_review_result.get("summary", "") or ""),
            "review_subject_kind": review_subject_kind,
            "repair_request_file": request_file,
        },
        stage="semantic_review",
    )
    (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(build_failure_summary_markdown(task_id, history), encoding="utf-8")
    return history


def _append_verification_report(pack_dir: Path, verify_result: dict[str, Any], detail: str) -> None:
    report_path = pack_dir / "verification_report.md"
    stamp = datetime.now(UTC).isoformat().replace("+00:00", "Z")
    lines = [
        f"## Verification {stamp}",
        "",
        f"- Attempt: `{verify_result.get('attempt')}`",
        f"- Candidate: `{Path(str(verify_result.get('candidate_file', ''))).name}`",
        f"- Success: `{verify_result.get('success', False)}`",
        f"- Primary failure kind: `{verify_result.get('primary_failure_kind', 'none') or 'none'}`",
    ]
    blocking = verify_result.get("blocking_symbols", [])
    if isinstance(blocking, list) and blocking:
        lines.append(f"- Blocking symbols: `{', '.join(blocking)}`")
    lines.extend(
        [
            f"- Verify result file: `{Path(str(verify_result.get('verify_result_file', ''))).name}`",
            "",
            "```text",
            (detail or "(no detail)").strip(),
            "```",
            "",
        ]
    )
    _append_text(report_path, "\n".join(lines))


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _append_build_report(pack_dir: Path, build_result: dict[str, Any], detail: str) -> None:
    report_path = pack_dir / "verification_report.md"
    stamp = _utc_now_z()
    _append_text(
        report_path,
        "\n".join(
            [
                f"## Build Check {stamp}",
                "",
                f"- Attempt: `{build_result.get('attempt')}`",
                f"- Candidate: `{Path(str(build_result.get('candidate_file', ''))).name}`",
                f"- Success: `{build_result.get('success', False)}`",
                f"- Primary failure kind: `{build_result.get('primary_failure_kind', 'none') or 'none'}`",
                f"- Build result file: `{Path(str(build_result.get('build_result_file', ''))).name}`",
                "",
                "```text",
                (detail or "(no detail)").strip(),
                "```",
                "",
            ]
        ),
    )


async def build_check_prompt_pack_candidate(
    task_id: str,
    ledger: LedgerManager,
    settings,
    candidate_arg: str | None = None,
) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    output_binding = resolve_phase2_output_binding(task, ledger, settings)
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return False, proof_debt_blocker
    original_status = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("status", ""))
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)
    _sync_stale_build_ready_candidate(task_id, ledger, settings, pack_dir)
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    math_gate_reason = math_review_gate_blocker(
        task_id,
        current_record if isinstance(current_record, dict) else {},
        pack_dir=pack_dir,
    )
    if math_gate_reason:
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return False, math_gate_reason

    source_candidate_path = resolve_candidate_path(pack_dir, candidate_arg)
    candidate_code = _read_file_safely(source_candidate_path)
    candidate_kind = "external_candidate" if candidate_arg else "draft"
    candidate_hash = _sha256_text(candidate_code) if candidate_code else ""
    stale_official_message = stale_candidate_official_output_message(
        task_id=task_id,
        source_plan=source_plan,
        settings=settings,
        candidate_path=source_candidate_path,
        candidate_hash=candidate_hash,
        draft_path=pack_dir / DRAFT_FILE_NAME,
        action="build-check source",
    )
    if stale_official_message:
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return False, stale_official_message
    build_feedback_path = pack_dir / "build_feedback.txt"
    attempt, snapshot_path = _next_candidate_path(pack_dir)
    _shared_write_text(snapshot_path, candidate_code)
    build_result_path = _next_build_result_path(pack_dir, attempt)
    built_at = _utc_now_z()
    existing_completed_output = _has_active_official_output(task_id, source_plan, ledger, settings)

    def finalize(
        *,
        success: bool,
        detail_text: str,
        diagnostics: list[dict[str, Any]],
        disposition: str,
        hard_checks_success: bool,
        repl_success: bool = False,
        repl_output: str = "",
        temp_build_success: bool = False,
        temp_build_output: str = "",
        final_build_success: bool = False,
        final_build_output: str = "",
    ) -> tuple[bool, str]:
        build_result = _build_build_result_payload(
            task_id=task_id,
            attempt=attempt,
            candidate_path=snapshot_path,
            candidate_code=candidate_code,
            candidate_kind=candidate_kind,
            built_at=built_at,
            hard_checks_success=hard_checks_success,
            repl_success=repl_success,
            repl_output=repl_output,
            temp_build_success=temp_build_success,
            temp_build_output=temp_build_output,
            final_build_success=final_build_success,
            final_build_output=final_build_output,
            diagnostics=diagnostics,
            disposition=disposition,
        )
        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        build_result.update(_auto_loop_attempt_payload(current_record if isinstance(current_record, dict) else {}))
        build_result["success"] = success
        build_result["build_result_file"] = str(build_result_path)
        _write_json(build_result_path, build_result)
        history = _append_attempt_history(pack_dir, task_id, build_result, stage="build")
        failure_counters = phase2_failure_counters_from_history(history)
        _shared_write_text(pack_dir / FAILURE_SUMMARY_FILE_NAME, build_failure_summary_markdown(task_id, history))
        _shared_write_text(build_feedback_path, "" if success else detail_text)

        runtime_updates: dict[str, Any] = {
            "build_attempts": attempt,
            "phase2_build_fail_counter": failure_counters.build_fail_counter,
            "phase2_review_fail_counter": failure_counters.review_fail_counter,
            "latest_candidate_file": str(snapshot_path),
            "latest_build_result_file": str(build_result_path),
            "latest_build_candidate_kind": candidate_kind,
            "latest_build_candidate_file": str(snapshot_path),
            "latest_build_candidate_hash": build_result.get("candidate_hash", ""),
            "current_review_input_file": "",
            "current_review_prompt_file": "",
            "current_review_template_file": "",
            "current_review_context_file": "",
            "current_review_request_file": "",
            "current_review_backend_id": "",
            "current_review_expected_result_file": "",
            "current_review_subject_kind": "",
            "current_review_subject_file": "",
            "current_review_subject_hash": "",
            "current_review_origin": "",
        }
        if success:
            runtime_updates.update(
                {
                    "pack_candidate_state": "build_ready",
                    "latest_build_ready_candidate_kind": candidate_kind,
                    "latest_build_ready_candidate_file": str(snapshot_path),
                    "latest_build_ready_candidate_hash": build_result.get("candidate_hash", ""),
                }
            )
        else:
            runtime_updates["pack_candidate_state"] = "build_failed"
        ledger.update_runtime_metadata(task_id, **runtime_updates)
        _set_latest_operation(task_id, ledger, kind="build-check", file_path=str(build_result_path))
        if success:
            if existing_completed_output:
                ledger.update_status(task_id, TaskStatus(original_status))
            else:
                ledger.update_status(task_id, TaskStatus.PACKED)
        elif existing_completed_output:
            ledger.update_status(task_id, TaskStatus(original_status))
        elif failure_counters.build_fail_counter >= failure_counters.limit:
            ledger.update_status(task_id, TaskStatus.FAILED_LOCAL, error=detail_text)
        else:
            ledger.update_status(task_id, TaskStatus.PACKED)
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        _append_build_report(pack_dir, build_result, detail_text if detail_text else "build-check succeeded")
        return success, detail_text

    hard_ok, hard_diagnostics, hard_detail = validate_candidate_hard_checks(task, candidate_code, ledger)
    if not hard_ok:
        _record_undeclared_import_violations(task, hard_diagnostics, settings, source_candidate_path)
        return finalize(
            success=False,
            detail_text=hard_detail,
            diagnostics=hard_diagnostics,
            disposition="build_check_hard_check_failed",
            hard_checks_success=False,
        )

    sanitized_task_id = re.sub(r"[^A-Za-z0-9_]", "_", task_id)
    temp_module_basename = f"PackBuildCheck_{sanitized_task_id}_{attempt}"
    if len(temp_module_basename) > 96:
        digest = hashlib.sha256(task_id.encode("utf-8")).hexdigest()[:16]
        temp_module_basename = f"PackBuildCheck_{digest}_{attempt}"
    temp_module_file = settings.toyapollo_output_dir / f"{temp_module_basename}.lean"
    temp_module_name = f"ToyApollo.Output.{temp_module_basename}"
    settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
    temp_module_file.write_text(candidate_code, encoding="utf-8")

    compiler = LeanCompiler(root_dir=str(settings.runtime_root))
    try:
        repl_success, repl_output = await compiler.validate_with_repl_async(candidate_code)
        temp_build_success, temp_build_output = await compiler.build_module_async(temp_module_name)
        repl_timeout_nonblocking = (
            not repl_success
            and temp_build_success
            and _is_repl_timeout_output(repl_output)
        )
        if repl_timeout_nonblocking:
            repl_success = True
            repl_output = (
                "REPL precheck timed out and was treated as non-blocking because "
                "the temporary module build succeeded; final staged build is still required.\n\n"
                + repl_output
            )
        if not repl_success or not temp_build_success:
            diagnostics: list[dict[str, Any]] = []
            if not repl_success:
                diagnostics.extend(_parse_diagnostics(repl_output, "repl_failed", "repl"))
            if not temp_build_success:
                diagnostics.extend(_parse_diagnostics(temp_build_output, "temp_build_failed", "temp_build"))
            return finalize(
                success=False,
                detail_text=_compose_detail_text(repl_output, temp_build_output),
                diagnostics=diagnostics,
                disposition="build_check_temp_build_failed",
                hard_checks_success=True,
                repl_success=repl_success,
                repl_output=repl_output,
                temp_build_success=temp_build_success,
                temp_build_output=temp_build_output,
            )

        final_success, final_output = _run_staged_official_build(
            task_id,
            source_plan,
            settings,
            pack_dir,
            candidate_code,
            attempt=attempt,
            mode="build-check",
            restore_on_success=True,
            output_owner_task_id=output_binding.output_owner_task_id,
        )
        if not final_success:
            diagnostics = _parse_diagnostics(final_output, "final_build_failed", "final_build")
            return finalize(
                success=False,
                detail_text=_compose_detail_text(repl_output, temp_build_output, final_output),
                diagnostics=diagnostics,
                disposition="build_check_final_build_failed",
                hard_checks_success=True,
                repl_success=repl_success,
                repl_output=repl_output,
                temp_build_success=temp_build_success,
                temp_build_output=temp_build_output,
                final_build_success=False,
                final_build_output=final_output,
            )

        return finalize(
            success=True,
            detail_text="build-check passed; candidate is ready for semantic review.",
            diagnostics=[],
            disposition="build_check_passed",
            hard_checks_success=True,
            repl_success=True,
            repl_output=repl_output,
            temp_build_success=True,
            temp_build_output=temp_build_output,
            final_build_success=True,
            final_build_output=final_output,
        )
    finally:
        if temp_module_file.exists():
            try:
                temp_module_file.unlink()
            except Exception:
                pass


def _write_codex_handoff_review_artifacts(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    attempt: int,
    candidate_path: Path,
    candidate_code: str,
    build_summary: dict[str, Any],
    mode: str = "review-pack",
    review_subject_kind: str = "candidate",
    build_result_file: str = "",
    build_candidate_file: str = "",
    build_candidate_hash: str = "",
) -> dict[str, Any]:
    paths = next_semantic_review_artifact_paths(pack_dir, attempt)
    latest = latest_semantic_review_artifact_paths(pack_dir)
    context_path = next_semantic_review_context_path(pack_dir, attempt)
    request_path = _review_request_path(pack_dir, attempt)
    context_markdown = build_semantic_review_context_markdown(task, ledger, settings, pack_dir)
    _shared_write_text(context_path, context_markdown)
    review_basis = build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind=review_subject_kind,
        review_subject_hash=_sha256_text(candidate_code) if candidate_code else "",
        review_subject_file=candidate_path,
    )
    review_input = build_semantic_review_input(
        task=task,
        mode=mode,
        attempt=attempt,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        import_lines=build_import_lines(task),
        dependency_summary=_build_dependency_review_summary(task, ledger, settings),
        search_summary=_build_search_review_summary(pack_dir),
        build_summary=build_summary,
        backend_id="codex-handoff",
        reviewer_argv_hash="codex-handoff",
        review_subject_kind=review_subject_kind,
        review_basis=review_basis,
        review_basis_hash=_sha256_json(review_basis),
        build_result_file=build_result_file,
        build_candidate_file=build_candidate_file,
        build_candidate_hash=build_candidate_hash,
        sanity_build_module=f"ToyApollo.Output.{task['block_id']}" if review_subject_kind == "official_output" else "",
        sanity_build_passed=review_subject_kind == "official_output",
        review_context_file=str(context_path),
        review_context_hash=_sha256_text(context_markdown),
        review_context_markdown=context_markdown,
    )
    prompt_text = render_semantic_review_prompt(review_input)
    _write_json(paths["input"], review_input)
    _shared_write_text(paths["prompt"], prompt_text)

    template_path = _result_template_path(pack_dir, attempt)
    expected_result_path = paths["result"]
    template = {
        "schema_version": "phase2.semantic_review.result.v7",
        "task_id": task["block_id"],
        "mode": mode,
        "attempt": attempt,
        "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
        "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
        "review_input_hash": _sha256_json(review_input),
        "review_input_file": str(paths["input"]),
        "review_prompt_file": str(paths["prompt"]),
        "review_context_file": str(context_path),
        "expected_result_file": str(expected_result_path),
        "candidate_hash": review_input["candidate"]["hash"],
        "verdict": "inconclusive",
        "confidence": "",
        "summary": "",
        "proof_class": "",
        "completion_class": "",
        "reviewer_independence": {
            "role": "independent_read_only_reviewer",
            "read_only": True,
            "did_edit_candidate": False,
            "used_current_review_request": True,
            "attestation": "",
        },
        "source_claims": [],
        "claim_mapping": [],
        "route_inspection": {
            "status": "unclear",
            "source_route": "",
            "expected_answer_or_statement": "",
            "local_mathlib_search": "",
            "public_interface_check": "",
            "support_or_reassembly_decision": "",
            "stop_go_verdict": "unclear",
            "notes": "",
        },
        "spine_alignment": {
            "status": "unclear",
            "summary": "",
            "obligations_checked": [],
            "missing_obligations": [],
            "shortcut_assessment": "unclear",
        },
        "obligation_review": {
            "status": "unclear",
            "summary": "",
            "items": [],
            "open_blockers": [],
            "scaffold_assessment": [],
        },
        "evidence_review": {
            "status": "unclear",
            "summary": "",
            "items": [
                {
                    "evidence_class": evidence_class,
                    "status": "unclear",
                    "evidence": "",
                }
                for evidence_class in review_basis.get("required_evidence_classes", [])
                if isinstance(review_basis.get("required_evidence_classes", []), list)
            ],
            "blocking_issues": [],
        },
        "interface_contract": {"status": "unclear", "summary": "", "mismatches": []},
        "downstream_adequacy": {"status": "unclear", "summary": "", "consumers_checked": [], "blocking_issues": []},
        "forbidden_weakenings": [],
        "findings": [],
        "recommended_disposition": "revise",
        "reviewer_schema_hints": {
            "completion_class_contract": {
                "required_fields": ["proof_class", "completion_class"],
                "must_be_non_empty": True,
                "authority": "reviewer_classification_then_official_task_status_projection",
            },
            "reviewer_independence_shape": {
                "role": "independent_read_only_reviewer",
                "read_only": True,
                "did_edit_candidate": False,
                "used_current_review_request": True,
                "attestation": "<short statement that this was an independent read-only review>",
            },
            "section_status_values": ["covered", "partial", "missing", "violated", "unclear"],
            "route_inspection_fields": [
                "source_route",
                "expected_answer_or_statement",
                "local_mathlib_search",
                "public_interface_check",
                "support_or_reassembly_decision",
                "stop_go_verdict",
            ],
            "route_inspection_stop_go_values": [
                "go",
                "stop",
                "needs_reassembly",
                "needs_route_redesign",
                "unclear",
                "not_applicable",
            ],
            "obligation_item_status_values": [
                "covered",
                "partial",
                "missing",
                "violated",
                "unclear",
                "not_applicable",
                "accepted_as_proof_debt",
            ],
            "obligation_item_contract_fields": {
                "expected_theorem_signature": "<source-faithful theorem/lemma type expected for this obligation>",
                "lean_landing": "<Lean theorem/lemma declaration proving the obligation>",
                "landing_kind": "theorem | lemma | private_axiom | structure_field | support_predicate | support_constructor | adapter | public_premise | empty | unknown",
                "proof_contract_status": "unverified | verified | failed | not_applicable | accepted_adapter | open_math_debt | beyond_book_exception",
                "signature_match": "unverified | passed | failed | not_applicable",
                "body_reassumption_check": "unverified | passed | failed | not_applicable",
                "public_premise_check": "unverified | passed | failed | not_applicable",
                "proof_contract_notes": "<why the landing satisfies or fails the contract>",
            },
            "evidence_item_shape": {
                "evidence_class": "source_tex | lean_subject | proof_obligations | audit | classification | dependency_status | downstream | ledger_status | hashes",
                "status": "covered | partial | missing | violated | unclear | not_applicable",
                "evidence": "<what was checked and how conflicts/staleness were resolved>",
            },
            "required_evidence_classes": review_basis.get("required_evidence_classes", []),
            "downstream_consumer_entry_shape": {
                "block_id": "<direct downstream block_id>",
                "status": "covered | not_applicable | blocked",
                "evidence": "<why this exported interface is adequate or not applicable>",
            },
            "forbidden_weakening_status_values": ["not_present", "present", "not_applicable"],
            "pass_review_apply_command": (
                "python .\\run_chapter.py --phase 2 --phase2-mode review-apply "
                "--tasks <task_id> --review-result <semantic_review_result_vM.json>"
            ),
        },
    }
    _write_json(template_path, template)
    review_request = _build_semantic_review_request(
        task_id=task["block_id"],
        origin=mode,
        attempt=attempt,
        review_subject_kind=review_subject_kind,
        review_subject_file=str(candidate_path),
        review_subject_hash=review_input.get("review_subject_hash", ""),
        review_basis_hash=review_input.get("review_basis_hash", ""),
        review_input_hash=_sha256_json(review_input),
        review_input_file=str(paths["input"]),
        review_prompt_file=str(paths["prompt"]),
        review_context_file=str(context_path),
        review_result_template_file=str(template_path),
        expected_result_file=str(expected_result_path),
        reviewer_backend_id="codex-handoff",
        prompt_version=SEMANTIC_REVIEW_PROMPT_VERSION,
        rubric_version=SEMANTIC_REVIEW_RUBRIC_VERSION,
    )
    _write_json(request_path, review_request)
    _sync_current_review_aliases(
        pack_dir,
        input_path=paths["input"],
        prompt_path=paths["prompt"],
        template_path=template_path,
        context_path=context_path,
        request_path=request_path,
    )
    for key in ("input", "prompt"):
        latest_path = latest[key]
        if _path_exists(latest_path):
            _unlink_path(latest_path)
        _copy_file(paths[key], latest_path)

    return {
        "verdict": "inconclusive",
        "runner": {"status": "codex_handoff_pending"},
        "summary": "Codex semantic review is required before promotion.",
        "recommended_disposition": "manual_review",
        "review_input_file": str(paths["input"]),
        "review_prompt_file": str(paths["prompt"]),
        "review_context_file": str(context_path),
        "review_result_template_file": str(template_path),
        "review_request_file": str(request_path),
        "expected_review_result_file": str(expected_result_path),
        "cache_key": review_input.get("cache_key", ""),
        "cache_hit": False,
        "reviewer_backend_id": "codex-handoff",
    }


def _write_review_compat_summary(
    *,
    task_id: str,
    ledger: LedgerManager,
    task: dict[str, Any],
    settings,
    pack_dir: Path,
    mode: str,
    candidate_path: Path,
    candidate_code: str,
    detail_text: str,
    diagnostics: list[dict[str, Any]],
    disposition: str,
    semantic_review: dict[str, Any] | None = None,
    final_build_success: bool = False,
    final_build_output: str = "",
    success: bool = False,
    state_transition: str = "none",
) -> Path:
    attempt = len(_list_versioned_json_files(pack_dir, "verify_result")) + 1
    verify_result_path = _next_verify_result_path(pack_dir, attempt)
    verify_result = _build_verify_result_payload(
        task_id=task_id,
        attempt=attempt,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        verified_at=_utc_now_z(),
        repl_success=success,
        repl_output=detail_text,
        temp_build_success=success,
        temp_build_output=detail_text,
        final_build_success=final_build_success,
        final_build_output=final_build_output or detail_text,
        diagnostics=diagnostics,
    )
    verify_result["success"] = success
    verify_result["mode"] = mode
    verify_result["disposition"] = disposition
    verify_result["state_transition"] = state_transition
    if semantic_review is not None:
        verify_result["semantic_review"] = _semantic_review_summary(semantic_review)
    verify_result["verify_result_file"] = str(verify_result_path)
    _write_json(verify_result_path, verify_result)
    ledger.mark_verifying(
        task_id,
        latest_candidate_file=str(candidate_path),
        latest_verify_result_file=str(verify_result_path),
        verify_attempts=attempt,
    )
    _set_latest_operation(task_id, ledger, kind=mode, file_path=str(verify_result_path))
    _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    _append_verification_report(pack_dir, verify_result, detail_text)
    return verify_result_path


async def write_codex_review_pack(task_id: str, ledger: LedgerManager, settings, candidate_arg: str | None = None) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return False, proof_debt_blocker
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)
    if candidate_arg:
        candidate_path = Path(candidate_arg).expanduser()
        if not candidate_path.is_absolute():
            candidate_path = (Path.cwd() / candidate_path).resolve()
        official_targets = {
            str(path.resolve())
            for path in iter_official_output_targets(task_id, str(task.get("source_plan", "unknown") or "unknown"), settings)
        }
        if str(candidate_path.resolve()) in official_targets:
            return await write_existing_output_review_pack(task_id, ledger, settings)
        return False, "review-pack no longer accepts external candidate paths; run build-check --candidate <path> first."

    stale_ready = _sync_stale_build_ready_candidate(task_id, ledger, settings, pack_dir)
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    ready_file = str(current_record.get("latest_build_ready_candidate_file", "") or "")
    if not ready_file:
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        if stale_ready:
            return False, "The last build-ready candidate is stale; rerun build-check before review-pack."
        return False, "No build-ready candidate is available for review-pack; run build-check first."

    candidate_path = Path(ready_file)
    if not _path_exists(candidate_path):
        ledger.update_runtime_metadata(
            task_id,
            latest_build_ready_candidate_kind="",
            latest_build_ready_candidate_file="",
            latest_build_ready_candidate_hash="",
            pack_candidate_state="draft",
        )
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return False, "The last build-ready candidate is stale or missing; rerun build-check."

    candidate_code = _read_file_safely(candidate_path)
    candidate_hash = _sha256_text(candidate_code) if candidate_code else ""
    if candidate_hash != str(current_record.get("latest_build_ready_candidate_hash", "") or ""):
        ledger.update_runtime_metadata(
            task_id,
            latest_build_ready_candidate_kind="",
            latest_build_ready_candidate_file="",
            latest_build_ready_candidate_hash="",
            pack_candidate_state="draft",
        )
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return False, "The last build-ready candidate is stale; rerun build-check before review-pack."

    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    stale_official_message = stale_candidate_official_output_message(
        task_id=task_id,
        source_plan=source_plan,
        settings=settings,
        candidate_path=candidate_path,
        candidate_hash=candidate_hash,
        draft_path=pack_dir / DRAFT_FILE_NAME,
        action="candidate review",
    )
    if stale_official_message:
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return False, stale_official_message

    review_attempt = _next_review_attempt(pack_dir)
    build_result_file = str(current_record.get("latest_build_result_file", "") or "")
    build_summary = _read_json_safely(Path(build_result_file), {}) if build_result_file else {}
    semantic_review = _write_codex_handoff_review_artifacts(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        attempt=review_attempt,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        build_summary=build_summary if isinstance(build_summary, dict) else {},
        mode="review-pack",
        review_subject_kind="candidate",
        build_result_file=build_result_file,
        build_candidate_file=str(candidate_path),
        build_candidate_hash=candidate_hash,
    )
    _update_pack_candidate_state(task_id, ledger, "review_pending")
    _set_current_review_metadata(
        task_id,
        ledger,
        input_file=str(semantic_review["review_input_file"]),
        prompt_file=str(semantic_review["review_prompt_file"]),
        template_file=str(semantic_review["review_result_template_file"]),
        context_file=str(semantic_review.get("review_context_file", "") or ""),
        request_file=str(semantic_review.get("review_request_file", "") or ""),
        backend_id=str(semantic_review.get("reviewer_backend_id", "") or ""),
        expected_result_file=str(semantic_review.get("expected_review_result_file", "") or ""),
        subject_kind="candidate",
        subject_file=str(candidate_path),
        subject_hash=candidate_hash,
        origin="review-pack",
    )
    _write_review_compat_summary(
        task_id=task_id,
        ledger=ledger,
        task=task,
        settings=settings,
        pack_dir=pack_dir,
        mode="review-pack",
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        detail_text="Codex semantic review pack generated; apply a filled semantic_review_result JSON with review-apply.",
        diagnostics=[],
        disposition="codex_review_required",
        semantic_review=semantic_review,
        state_transition="none",
    )
    return True, "Codex semantic review pack generated; apply a filled semantic_review_result JSON with review-apply."


async def write_existing_output_review_pack(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    force_new_attempt: bool = False,
) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return False, proof_debt_blocker
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not _path_exists(pack_dir):
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)

    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    output_path = select_latest_existing_task_file(task_id, source_plan, settings)
    if output_path is None or not output_path.exists():
        raise FileNotFoundError(f"Official output file does not exist for review-existing: {task_id}")
    candidate_code = _read_file_safely(output_path)

    sanity_success, sanity_output = _run_official_module_build(task_id, settings)
    if not sanity_success:
        _clear_current_review_metadata(task_id, ledger)
        diagnostics = _parse_diagnostics(sanity_output, "final_build_failed", "review_existing_sanity_build")
        _write_review_compat_summary(
            task_id=task_id,
            ledger=ledger,
            task=task,
            settings=settings,
            pack_dir=pack_dir,
            mode="review-existing",
            candidate_path=output_path,
            candidate_code=candidate_code,
            detail_text=sanity_output or f"lake build ToyApollo.Output.{task_id} failed before review-existing.",
            diagnostics=diagnostics,
            disposition="review_existing_build_failed_no_review",
            semantic_review=None,
            state_transition="none",
        )
        return False, sanity_output or f"lake build ToyApollo.Output.{task_id} failed before review-existing."

    prepared = _prepare_existing_output_review_materials(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        output_path=output_path,
        mode="review-existing",
        build_output=sanity_output,
        force_new_attempt=force_new_attempt,
    )
    snapshot_path = prepared["snapshot_path"]
    ledger.update_runtime_metadata(task_id, latest_official_snapshot_file=str(snapshot_path))
    _set_current_review_metadata(
        task_id,
        ledger,
        input_file=str(prepared["input_path"]),
        prompt_file=str(prepared["prompt_path"]),
        template_file=str(prepared["template_path"]),
        context_file=str(prepared["context_path"]),
        request_file=str(prepared.get("request_path") or ""),
        backend_id="codex-handoff",
        expected_result_file=str(prepared["result_path"] if prepared["result_path"] is not None else next_semantic_review_artifact_paths(pack_dir, prepared["attempt"])["result"]),
        subject_kind="official_output",
        subject_file=str(snapshot_path),
        subject_hash=str(prepared["candidate_hash"]),
        origin="review-existing",
    )
    semantic_review = {
        "verdict": "inconclusive",
        "runner": {"status": "codex_handoff_pending"},
        "summary": "Existing runnable official output frozen for semantic review.",
        "recommended_disposition": "manual_review",
        "review_input_file": str(prepared["input_path"]),
        "review_prompt_file": str(prepared["prompt_path"]),
        "review_context_file": str(prepared["context_path"]),
        "review_result_template_file": str(prepared["template_path"]),
        "expected_review_result_file": str(prepared["result_path"]) if prepared["result_path"] is not None else str(next_semantic_review_artifact_paths(pack_dir, prepared["attempt"])["result"]),
        "cache_hit": False,
        "reviewer_backend_id": "codex-handoff",
    }
    _write_review_compat_summary(
        task_id=task_id,
        ledger=ledger,
        task=task,
        settings=settings,
        pack_dir=pack_dir,
        mode="review-existing",
        candidate_path=snapshot_path,
        candidate_code=str(prepared["candidate_code"]),
        detail_text="Existing runnable official output frozen for semantic review; apply a filled semantic_review_result JSON with review-apply.",
        diagnostics=[],
        disposition="review_existing_required",
        semantic_review=semantic_review,
        state_transition="none",
    )
    return True, "Existing runnable official output frozen for semantic review; apply a filled semantic_review_result JSON with review-apply."


async def write_existing_output_review_queue(task_ids: list[str], ledger: LedgerManager, settings) -> tuple[bool, str]:
    selected_task_ids = set(task_ids) if task_ids else None
    outputs, skipped_non_official_files = _iter_review_existing_queue_outputs(settings, selected_task_ids)
    reports_dir = _phase2_queue_reports_dir(settings)
    reports_dir.mkdir(parents=True, exist_ok=True)

    scanned_at = _utc_now_z()
    task_reports: list[dict[str, Any]] = []
    counts: Counter[str] = Counter()

    for output_path in outputs:
        task_id = canonicalize_block_id(output_path.stem)
        resolved_task = _resolve_plan_task_for_output(task_id, settings)
        source_resolution = _queue_source_resolution(task_id, resolved_task)

        sanity_success, sanity_output = _run_official_module_build(task_id, settings)
        sanity_build_status = _queue_sanity_build_status(task_id, sanity_success, sanity_output)

        task_report: dict[str, Any] = {
            "task_id": task_id,
            "official_output_file": str(output_path),
            "source_plan": str(source_resolution.get("source_plan", "") or ""),
            "source_resolution": source_resolution,
            "sanity_build_status": sanity_build_status,
            "queue_status": "",
            "official_snapshot_file": "",
            "semantic_review_input_file": "",
            "semantic_review_prompt_file": "",
            "semantic_review_context_file": "",
            "semantic_review_result_template_file": "",
            "latest_matching_review_result_file": "",
            "next_action": "",
            "detail": "",
        }

        if not sanity_success:
            if task_id in ledger.ledger.get("tasks", {}):
                _clear_current_review_metadata_for_existing_subjects(task_id, ledger)
                pack_dir = settings.phase2_prompt_packs_dir / task_id
                if pack_dir.exists() and isinstance(resolved_task, dict):
                    _refresh_pack_runtime_view(canonicalize_task_dict(resolved_task), ledger, settings, pack_dir)
            task_report["queue_status"] = "blocked_build"
            task_report["next_action"] = "fix_build"
            task_report["detail"] = sanity_output or f"lake build ToyApollo.Output.{task_id} failed."
            counts[task_report["queue_status"]] += 1
            task_reports.append(task_report)
            continue

        if resolved_task is None:
            if task_id in ledger.ledger.get("tasks", {}):
                _clear_current_review_metadata_for_existing_subjects(task_id, ledger)
                pack_dir = settings.phase2_prompt_packs_dir / task_id
                if pack_dir.exists():
                    task_for_view = canonicalize_task_dict(ledger.ledger["tasks"][task_id])
                    _refresh_pack_runtime_view(task_for_view, ledger, settings, pack_dir)
            task_report["queue_status"] = "source_missing"
            task_report["next_action"] = "restore_source"
            task_report["detail"] = f"Official output builds, but no source task was found in plans/*.json for {task_id}."
            counts[task_report["queue_status"]] += 1
            task_reports.append(task_report)
            continue

        task = ensure_task_registered(resolved_task, ledger)
        pack_dir = settings.phase2_prompt_packs_dir / task_id
        if not pack_dir.exists():
            pack_dir = _ensure_queue_pack_dir(task, ledger, settings)

        prepared = _prepare_existing_output_review_materials(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            output_path=output_path,
            mode="review-existing-queue",
            build_output=sanity_output,
        )
        snapshot_path = prepared["snapshot_path"]
        ledger.update_runtime_metadata(task_id, latest_official_snapshot_file=str(snapshot_path))
        _set_current_review_metadata(
            task_id,
            ledger,
            input_file=str(prepared["input_path"]),
            prompt_file=str(prepared["prompt_path"]),
            template_file=str(prepared["template_path"]),
            context_file=str(prepared["context_path"]),
            request_file=str(prepared.get("request_path") or ""),
            backend_id="codex-handoff",
            expected_result_file=str(prepared["result_path"] if prepared["result_path"] is not None else next_semantic_review_artifact_paths(pack_dir, prepared["attempt"])["result"]),
            subject_kind="official_output",
            subject_file=str(snapshot_path),
            subject_hash=str(prepared["candidate_hash"]),
            origin="review-existing-queue",
        )
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)

        queue_status, next_action, detail = _queue_status_for_prepared_materials(prepared)
        task_report.update(
            {
                "source_plan": str(task.get("source_plan", "unknown") or "unknown"),
                "queue_status": queue_status,
                "official_snapshot_file": str(snapshot_path),
                "semantic_review_input_file": str(prepared["input_path"]),
                "semantic_review_prompt_file": str(prepared["prompt_path"]),
                "semantic_review_context_file": str(prepared["context_path"]),
                "semantic_review_result_template_file": str(prepared["template_path"]),
                "latest_matching_review_result_file": str(prepared["latest_matching_review_result_file"]),
                "next_action": next_action,
                "detail": detail,
            }
        )
        counts[queue_status] += 1
        task_reports.append(task_report)

    queue_counts = {
        status: counts.get(status, 0)
        for status in (
            "blocked_build",
            "source_missing",
            "review_result_present",
            "stale_review_result",
            "ready_for_codex_review",
        )
    }
    review_material_summary = _review_existing_queue_material_summary(queue_counts)
    report = {
        "scanned_at": scanned_at,
        "official_outputs_scanned": len(outputs),
        "skipped_non_official_files": skipped_non_official_files,
        "counts": queue_counts,
        "review_material_summary": review_material_summary,
        "tasks": task_reports,
    }
    report_base = _queue_report_base_name()
    json_path = reports_dir / f"{report_base}.json"
    markdown_path = reports_dir / f"{report_base}.md"
    _write_json(json_path, report)
    markdown_path.write_text(_render_review_existing_queue_markdown(report), encoding="utf-8")

    summary = (
        f"Prepared review-existing queue for {len(outputs)} official outputs; "
        f"prepared_materials={review_material_summary['prepared_review_materials']}, "
        f"fresh_review_required={review_material_summary['fresh_review_required']}, "
        f"stale_or_invalid_prior={review_material_summary['stale_or_invalid_prior_results']}, "
        f"current_matching_results={review_material_summary['current_matching_review_results']}, "
        f"blocked_build={review_material_summary['blocked_build']}, "
        f"source_missing={review_material_summary['source_missing']} "
        f"(legacy counts: "
        f"ready={report['counts']['ready_for_codex_review']}, "
        f"stale={report['counts']['stale_review_result']}, "
        f"present={report['counts']['review_result_present']}, "
        f"blocked={report['counts']['blocked_build']}, "
        f"missing={report['counts']['source_missing']}). "
        f"Report: {json_path}"
    )
    return True, summary


def _resolve_codex_review_input_path(result_path: Path, raw_result: Any) -> Path | None:
    if isinstance(raw_result, dict):
        raw_input_path = str(raw_result.get("review_input_file", "") or "").strip()
        if raw_input_path:
            path = Path(raw_input_path).expanduser()
            if not path.is_absolute():
                path = (result_path.parent / path).resolve()
            return path
    match = re.fullmatch(r"semantic_review_result_v(\d+)\.json", result_path.name)
    if match:
        return result_path.parent / f"semantic_review_input_v{match.group(1)}.json"
    return None


def _resolve_review_binding_path(raw_path: str, *, pack_dir: Path) -> Path:
    path = Path(str(raw_path or "")).expanduser()
    if not path.is_absolute():
        path = (pack_dir / path).resolve()
    return path








def _count_auto_loop_build_attempts(pack_dir: Path, task_id: str, round_number: int) -> int:
    from .phase2_review_loop import _count_auto_loop_build_attempts as _owner_count_auto_loop_build_attempts

    return _owner_count_auto_loop_build_attempts(pack_dir, task_id, round_number)
    history = _load_attempt_history(pack_dir, task_id)
    attempts = history.get("attempts", [])
    if not isinstance(attempts, list):
        return 0
    count = 0
    for item in attempts:
        if not isinstance(item, dict):
            continue
        if str(item.get("stage", "") or "") != "build":
            continue
        if int(item.get("auto_loop_round") or 0) != round_number:
            continue
        count += 1
    return count


def _next_auto_loop_round(pack_dir: Path, task_id: str, current_record: dict[str, Any]) -> int:
    from .phase2_review_loop import _next_auto_loop_round as _owner_next_auto_loop_round

    return _owner_next_auto_loop_round(pack_dir, task_id, current_record)
    state = _auto_loop_state_from_record(current_record)
    max_round = max(int(state["round"] or 0), 0)
    history = _load_attempt_history(pack_dir, task_id)
    attempts = history.get("attempts", [])
    if isinstance(attempts, list):
        for item in attempts:
            if not isinstance(item, dict):
                continue
            try:
                max_round = max(max_round, int(item.get("auto_loop_round") or 0))
            except (TypeError, ValueError):
                continue
    next_round = max_round + 1 if max_round > 0 else 1
    if str(current_record.get("current_review_repair_request_file", "") or "").strip():
        next_round = max(next_round, 2)
    return next_round


def _expected_current_review_result_path(pack_dir: Path, current_record: dict[str, Any]) -> Path | None:
    raw = str(current_record.get("current_review_expected_result_file", "") or "").strip()
    if not raw:
        return None
    return _resolve_review_binding_path(raw, pack_dir=pack_dir)


def _latest_verify_result_payload(pack_dir: Path) -> tuple[Path | None, dict[str, Any]]:
    verify_path = select_latest_verify_result(pack_dir)
    if verify_path is None or not verify_path.exists():
        return None, {}
    payload = _read_json_safely(verify_path, {})
    if not isinstance(payload, dict):
        return verify_path, {}
    return verify_path, payload


def _seeded_repair_request_path(pack_dir: Path, current_record: dict[str, Any]) -> str:
    raw = str(current_record.get("current_review_repair_request_file", "") or "").strip()
    if raw:
        return str(_resolve_review_binding_path(raw, pack_dir=pack_dir))
    return ""


def _initialize_auto_loop_state(
    task_id: str,
    ledger: LedgerManager,
    *,
    pack_dir: Path,
    current_record: dict[str, Any],
    review_subject: str,
    max_auto_rounds: int,
    nonprogress_limit: int,
    max_build_attempts_per_round: int,
) -> dict[str, Any]:
    state = _auto_loop_state_from_record(current_record)
    if (
        state["enabled"]
        and state["status"] == "active"
        and state["entry_subject"] == review_subject
        and state["max_rounds"] == max_auto_rounds
        and state["nonprogress_limit"] == nonprogress_limit
        and state["max_build_attempts_per_round"] == max_build_attempts_per_round
    ):
        return state

    initial_round = _next_auto_loop_round(pack_dir, task_id, current_record)
    updates = _auto_loop_runtime_updates(
        current_auto_loop_enabled=True,
        current_auto_loop_entry_subject=review_subject,
        current_auto_loop_round=initial_round,
        current_auto_loop_max_rounds=max_auto_rounds,
        current_auto_loop_max_build_attempts_per_round=max_build_attempts_per_round,
        current_auto_loop_nonprogress_limit=nonprogress_limit,
        current_auto_loop_consecutive_nonprogress=0,
        current_auto_loop_phase="entry",
        current_auto_loop_status="active",
        current_auto_loop_stop_reason="",
        current_auto_loop_last_candidate_hash="",
        current_auto_loop_last_review_fingerprint="",
        current_auto_loop_last_repair_request_file="",
    )
    _set_current_auto_loop_metadata(task_id, ledger, **updates)
    return _auto_loop_state_from_record({**current_record, **updates})


def _stop_auto_loop(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    reason: str,
    detail: str,
) -> tuple[bool, str]:
    from .phase2_review_loop import _stop_auto_loop as _owner_stop_auto_loop

    return _owner_stop_auto_loop(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir, reason=reason, detail=detail)
    task_id = task["block_id"]
    _set_current_auto_loop_metadata(
        task_id,
        ledger,
        current_auto_loop_enabled=True,
        current_auto_loop_status="stopped",
        current_auto_loop_phase="stopped",
        current_auto_loop_stop_reason=reason,
    )
    _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return False, detail


def _complete_auto_loop(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    detail: str,
) -> tuple[bool, str]:
    from .phase2_review_loop import _complete_auto_loop as _owner_complete_auto_loop

    return _owner_complete_auto_loop(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir, detail=detail)
    task_id = task["block_id"]
    _set_current_auto_loop_metadata(
        task_id,
        ledger,
        current_auto_loop_enabled=True,
        current_auto_loop_status="completed",
        current_auto_loop_phase="completed",
        current_auto_loop_stop_reason="passed",
    )
    _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return True, detail








def _invalid_codex_review_result(review_input: dict[str, Any], reason: str, raw_result: Any | None = None) -> dict[str, Any]:
    from .phase2_review_apply import _invalid_codex_review_result as _owner_invalid_codex_review_result

    return _owner_invalid_codex_review_result(review_input, reason, raw_result)
    raw = {
        "verdict": "inconclusive",
        "confidence": "none",
        "summary": reason,
        "source_claims": [],
        "claim_mapping": [],
        "findings": [{"severity": "error", "category": "review_apply", "message": reason}],
        "recommended_disposition": "needs_review",
    }
    if raw_result is not None:
        raw["raw_result"] = raw_result
    result = normalize_reviewer_result(
        raw,
        review_input=review_input,
        runner_metadata={"status": "codex_handoff_invalid", "reason": reason},
    )
    result["normalization_reason"] = reason
    return result


def _write_normalized_codex_review_artifacts(pack_dir: Path, review_input: dict[str, Any], normalized_result: dict[str, Any]) -> dict[str, Any]:
    from .phase2_review_apply import _write_normalized_codex_review_artifacts as _owner_write_normalized_codex_review_artifacts

    return _owner_write_normalized_codex_review_artifacts(pack_dir, review_input, normalized_result)
    attempt = int(review_input.get("attempt") or 0) or len(_list_versioned_json_files(pack_dir, "semantic_review_input"))
    paths = next_semantic_review_artifact_paths(pack_dir, attempt)
    latest = latest_semantic_review_artifact_paths(pack_dir)
    normalized_result = dict(normalized_result)
    normalized_result["review_input_file"] = str(paths["input"]) if paths["input"].exists() else str(normalized_result.get("review_input_file", ""))
    normalized_result["review_prompt_file"] = str(paths["prompt"]) if paths["prompt"].exists() else str(normalized_result.get("review_prompt_file", ""))
    normalized_result["review_result_file"] = str(paths["result"])
    normalized_result["review_report_file"] = str(paths["report"])
    _write_json(paths["result"], normalized_result)
    paths["report"].write_text(render_semantic_review_report(normalized_result), encoding="utf-8")
    for key, path in paths.items():
        if not path.exists():
            continue
        if latest[key].exists():
            latest[key].unlink()
        shutil.copyfile(path, latest[key])
    return normalized_result


def _write_review_repair_artifacts(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    failed_review_input_file: Path,
    failed_review_result_file: Path,
    failed_review_report_file: Path,
    failed_review_subject_file: Path,
    next_draft_seed_file: Path,
    origin_review_mode: str,
) -> dict[str, Any]:
    from .phase2_review_apply import _write_review_repair_artifacts as _owner_write_review_repair_artifacts

    return _owner_write_review_repair_artifacts(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        review_input=review_input,
        review_result=review_result,
        failed_review_input_file=failed_review_input_file,
        failed_review_result_file=failed_review_result_file,
        failed_review_report_file=failed_review_report_file,
        failed_review_subject_file=failed_review_subject_file,
        next_draft_seed_file=next_draft_seed_file,
        origin_review_mode=origin_review_mode,
    )
    attempt = _next_review_repair_attempt(pack_dir)
    request_path = _review_repair_request_path(pack_dir, attempt)
    summary_path = _review_repair_summary_path(pack_dir, attempt)
    request_payload = _build_review_repair_contract(
        task=task,
        review_input=review_input,
        review_result=review_result,
        failed_review_input_file=failed_review_input_file,
        failed_review_result_file=failed_review_result_file,
        failed_review_report_file=failed_review_report_file,
        failed_review_subject_file=failed_review_subject_file,
        next_draft_seed_file=next_draft_seed_file,
        attempt=attempt,
        origin_review_mode=origin_review_mode,
    )
    _write_json(request_path, request_payload)
    summary_path.write_text(_render_review_repair_summary(request_payload), encoding="utf-8")
    _sync_current_review_repair_aliases(pack_dir, request_path=request_path, summary_path=summary_path)
    ledger.update_runtime_metadata(
        task["block_id"],
        latest_review_repair_request_file=str(request_path),
        latest_review_repair_summary_file=str(summary_path),
    )
    _set_current_review_repair_metadata(
        task["block_id"],
        ledger,
        request_file=str(request_path),
        summary_file=str(summary_path),
        seed_file=str(next_draft_seed_file),
        origin_result_file=str(failed_review_result_file),
    )
    return {
        "request_path": request_path,
        "summary_path": summary_path,
        "request_payload": request_payload,
    }




async def verify_prompt_pack_candidate(task_id: str, ledger: LedgerManager, settings, candidate_arg: str | None = None) -> tuple[bool, str]:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return False, proof_debt_blocker
    verify_original_status = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("status", ""))

    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)

    source_candidate_path = resolve_candidate_path(pack_dir, candidate_arg)
    candidate_code = _read_file_safely(source_candidate_path)
    build_feedback_path = pack_dir / "build_feedback.txt"
    attempt, snapshot_path = _next_candidate_path(pack_dir)
    snapshot_path.write_text(candidate_code, encoding="utf-8")
    verify_result_path = _next_verify_result_path(pack_dir, attempt)
    verified_at = datetime.now(UTC).isoformat().replace("+00:00", "Z")
    source_plan = task.get("source_plan", "unknown")
    existing_official_output = find_existing_task_file(task_id, str(source_plan), settings)
    completed_statuses = {TaskStatus.COMPLETED.value, TaskStatus.COMPLETED_WITH_PROOF_DEBT.value}
    existing_completed_output = (
        verify_original_status in completed_statuses
        and existing_official_output is not None
        and existing_official_output.exists()
    )

    ledger.update_status(task_id, TaskStatus.VERIFYING)
    ledger.mark_verifying(
        task_id,
        latest_candidate_file=str(snapshot_path),
        verify_attempts=attempt,
    )

    def finalize_failure(
        detail_text: str,
        diagnostics: list[dict[str, Any]],
        *,
        repl_success: bool = False,
        repl_output: str = "",
        temp_build_success: bool = False,
        temp_build_output: str = "",
        final_build_success: bool = False,
        final_build_output: str = "",
        semantic_review: dict[str, Any] | None = None,
        disposition: str = "",
        state_transition: str | None = None,
    ) -> tuple[bool, str]:
        transition = state_transition or ("none" if existing_completed_output else "verify_to_failed_local")
        verify_result = _build_verify_result_payload(
            task_id=task_id,
            attempt=attempt,
            candidate_path=snapshot_path,
            candidate_code=candidate_code,
            verified_at=verified_at,
            repl_success=repl_success,
            repl_output=repl_output,
            temp_build_success=temp_build_success,
            temp_build_output=temp_build_output,
            final_build_success=final_build_success,
            final_build_output=final_build_output,
            diagnostics=diagnostics,
        )
        verify_result["success"] = False
        verify_result["mode"] = "verify"
        verify_result["disposition"] = disposition or "verify_failed"
        verify_result["state_transition"] = transition
        if semantic_review is not None:
            verify_result["semantic_review"] = _semantic_review_summary(semantic_review)
        verify_result["verify_result_file"] = str(verify_result_path)
        _write_json(verify_result_path, verify_result)
        history = _append_attempt_history(pack_dir, task_id, verify_result)
        failure_summary = build_failure_summary_markdown(task_id, history)
        (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(failure_summary, encoding="utf-8")
        build_feedback_path.write_text(detail_text, encoding="utf-8")
        if existing_completed_output:
            ledger.update_status(task_id, TaskStatus(verify_original_status))
        else:
            ledger.update_status(task_id, TaskStatus.FAILED_LOCAL, error=detail_text)
        ledger.mark_verifying(
            task_id,
            latest_candidate_file=str(snapshot_path),
            latest_verify_result_file=str(verify_result_path),
            verify_attempts=attempt,
        )
        _set_latest_operation(task_id, ledger, kind="verify", file_path=str(verify_result_path))
        _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        _append_verification_report(pack_dir, verify_result, detail_text)
        return False, detail_text

    hard_ok, hard_diagnostics, hard_detail = validate_candidate_hard_checks(task, candidate_code, ledger)
    if not hard_ok:
        return finalize_failure(hard_detail, hard_diagnostics, disposition="verify_hard_check_failed")

    config, config_error = _reviewer_config_or_detail(require_config=True)
    if config_error:
        diagnostics = _hard_check_diagnostic("semantic_reviewer_config_missing", config_error)
        return finalize_failure(config_error, diagnostics, disposition="verify_reviewer_config_missing")

    temp_module_basename = f"PackVerify_{re.sub(r'[^A-Za-z0-9_]', '_', task_id)}_{attempt}"
    temp_module_file = settings.toyapollo_output_dir / f"{temp_module_basename}.lean"
    temp_module_name = f"ToyApollo.Output.{temp_module_basename}"

    settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
    temp_module_file.write_text(candidate_code, encoding="utf-8")

    compiler = LeanCompiler(root_dir=str(settings.runtime_root))
    repl_success, repl_output = await compiler.validate_with_repl_async(candidate_code)
    temp_build_success, temp_build_output = await compiler.build_module_async(temp_module_name)

    try:
        if repl_success and temp_build_success:
            review_result = _run_semantic_review_for_candidate(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                attempt=attempt,
                mode="verify",
                candidate_path=snapshot_path,
                candidate_code=candidate_code,
                build_summary={
                    "repl": {"success": repl_success, "output": repl_output},
                    "temp_build": {"success": temp_build_success, "output": temp_build_output},
                },
                config=config,
                allow_missing_config=False,
            )
            review_verdict = str(review_result.get("verdict", "inconclusive"))
            review_cache_class = str(review_result.get("cache_class", "semantic_verdict") or "semantic_verdict").strip().lower()
            if review_cache_class != "semantic_verdict":
                detail_text = str(
                    review_result.get("normalization_reason", "")
                    or review_result.get("summary", "")
                    or "Semantic reviewer output was invalid."
                )
                diagnostics = _hard_check_diagnostic("invalid_reviewer_output", detail_text)
                return finalize_failure(
                    detail_text,
                    diagnostics,
                    repl_success=repl_success,
                    repl_output=repl_output,
                    temp_build_success=temp_build_success,
                    temp_build_output=temp_build_output,
                    semantic_review=review_result,
                    disposition="verify_invalid_reviewer_output",
                )
            review_result = _record_phase2_task_status_projection(task_id, task, ledger, review_result)
            review_verdict = str(review_result.get("verdict", "inconclusive"))
            if review_verdict != "pass":
                diagnostics = _review_diagnostics(review_result)
                detail_text = str(review_result.get("summary", "") or f"Semantic reviewer verdict: {review_verdict}")
                return finalize_failure(
                    detail_text,
                    diagnostics,
                    repl_success=repl_success,
                    repl_output=repl_output,
                    temp_build_success=temp_build_success,
                    temp_build_output=temp_build_output,
                    semantic_review=review_result,
                    disposition=f"verify_semantic_{review_verdict}",
                )

            final_success, final_output = _run_staged_official_build(
                task_id,
                str(source_plan),
                settings,
                pack_dir,
                candidate_code,
                attempt=attempt,
                mode="verify",
                restore_on_success=True,
            )
            if not final_success:
                diagnostics = _parse_diagnostics(final_output, "final_build_failed", "final_build")
                detail_text = _compose_detail_text(repl_output, temp_build_output, final_output)
                return finalize_failure(
                    detail_text,
                    diagnostics,
                    repl_success=repl_success,
                    repl_output=repl_output,
                    temp_build_success=temp_build_success,
                    temp_build_output=temp_build_output,
                    final_build_success=final_success,
                    final_build_output=final_output,
                    semantic_review=review_result,
                    disposition="verify_final_build_failed",
                )

            build_feedback_path.write_text("", encoding="utf-8")
            non_clean = str(review_result.get("task_status", "") or "") != "pass"
            verify_result = _build_verify_result_payload(
                task_id=task_id,
                attempt=attempt,
                candidate_path=snapshot_path,
                candidate_code=candidate_code,
                verified_at=verified_at,
                repl_success=repl_success,
                repl_output=repl_output,
                temp_build_success=temp_build_success,
                temp_build_output=temp_build_output,
                final_build_success=final_success,
                final_build_output=final_output,
                diagnostics=[],
            )
            verify_result["mode"] = "verify"
            verify_result["success"] = not non_clean
            verify_result["disposition"] = "verify_pass_non_clean_report" if non_clean else "verify_pass_report"
            verify_result["state_transition"] = "none"
            verify_result["semantic_review"] = _semantic_review_summary(review_result)
            verify_result["verify_result_file"] = str(verify_result_path)
            _write_json(verify_result_path, verify_result)
            history = _append_attempt_history(pack_dir, task_id, verify_result)
            (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(
                build_failure_summary_markdown(task_id, history),
                encoding="utf-8",
            )
            ledger.mark_verifying(
                task_id,
                latest_candidate_file=str(snapshot_path),
                latest_verify_result_file=str(verify_result_path),
                verify_attempts=attempt,
            )
            if verify_original_status:
                try:
                    ledger.update_status(task_id, TaskStatus(verify_original_status))
                except ValueError:
                    ledger.update_status(task_id, TaskStatus.PACKED)
            else:
                ledger.update_status(task_id, TaskStatus.PACKED)
            _set_latest_operation(task_id, ledger, kind="verify", file_path=str(verify_result_path))
            _refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            success_detail = (
                "REPL, temporary build, and final build all succeeded as a report-only verify check. "
                f"Task status: {review_result.get('task_status', '')} ({review_result.get('task_status_reason', '')})."
                " Run review-apply with a fresh semantic review result to land completion."
            )
            if non_clean:
                success_detail = (
                    f"{success_detail} Non-clean verify: review verdict is pass, but task_status="
                    f"{review_result.get('task_status', '')}; this is not textbook completion."
                )
            _append_verification_report(pack_dir, verify_result, success_detail)
            return not non_clean, success_detail

        diagnostics = []
        if not repl_success:
            diagnostics.extend(_parse_diagnostics(repl_output, "repl_failed", "repl"))
        if not temp_build_success:
            diagnostics.extend(_parse_diagnostics(temp_build_output, "temp_build_failed", "temp_build"))
        detail_text = _compose_detail_text(repl_output, temp_build_output)
        return finalize_failure(
            detail_text or "Candidate verification failed.",
            diagnostics,
            repl_success=repl_success,
            repl_output=repl_output,
            temp_build_success=temp_build_success,
            temp_build_output=temp_build_output,
            disposition="verify_build_failed",
        )
    finally:
        if temp_module_file.exists():
            try:
                temp_module_file.unlink()
            except Exception:
                pass


# Final thin compatibility wrappers. Keep these at true EOF so they win over legacy definitions above.
def build_operator_prompt(task: dict[str, Any], ledger: LedgerManager | None = None, settings=None, pack_dir: Path | None = None) -> str:
    from .phase2_pack_views import build_operator_prompt as _owner_build_operator_prompt
    return _owner_build_operator_prompt(task, ledger=ledger, settings=settings, pack_dir=pack_dir)


def build_context_markdown(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> str:
    from .phase2_pack_views import build_context_markdown as _owner_build_context_markdown
    return _owner_build_context_markdown(task, ledger, settings, pack_dir)


def build_failure_summary_markdown(task_id: str, history: dict[str, Any], auto_loop_state: dict[str, Any] | None = None) -> str:
    from .phase2_pack_views import build_failure_summary_markdown as _owner_build_failure_summary_markdown
    return _owner_build_failure_summary_markdown(task_id, history, auto_loop_state)


def _refresh_pack_runtime_view(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> None:
    from .phase2_pack_views import refresh_pack_runtime_view as _owner_refresh_pack_runtime_view
    return _owner_refresh_pack_runtime_view(task, ledger, settings, pack_dir)


def build_semantic_review_basis(
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    *,
    review_subject_kind: str,
    review_subject_hash: str = "",
    review_subject_file: str | Path | None = None,
) -> dict[str, Any]:
    from .phase2_review_request import build_semantic_review_basis as _owner_build_semantic_review_basis
    return _owner_build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind=review_subject_kind,
        review_subject_hash=review_subject_hash,
        review_subject_file=review_subject_file,
    )


def _render_review_repair_summary(
    repair_request: dict[str, Any],
    *,
    warning_lines: list[str] | None = None,
    archive_file: str = "",
) -> str:
    from .phase2_pack_views import _render_review_repair_summary as _owner_render_review_repair_summary
    return _owner_render_review_repair_summary(repair_request, warning_lines=warning_lines, archive_file=archive_file)


def _resolve_current_review_request_path(pack_dir: Path, current_record: dict[str, Any]) -> Path | None:
    from .phase2_review_request import _resolve_current_review_request_path as _owner_resolve_current_review_request_path
    return _owner_resolve_current_review_request_path(pack_dir, current_record)


def _validate_review_input_freshness(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    review_input: dict[str, Any],
) -> tuple[str, dict[str, Any]]:
    from .phase2_review_request import _validate_review_input_freshness as _owner_validate_review_input_freshness
    return _owner_validate_review_input_freshness(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        review_input=review_input,
    )


def _load_current_codex_review_request(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
) -> tuple[str, dict[str, Any]]:
    from .phase2_review_request import _load_current_codex_review_request as _owner_load_current_codex_review_request
    return _owner_load_current_codex_review_request(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir)


def _resolve_current_review_repair_request_path(pack_dir: Path, current_record: dict[str, Any]) -> Path | None:
    from .phase2_review_loop import _resolve_current_review_repair_request_path as _owner_resolve_current_review_repair_request_path
    return _owner_resolve_current_review_repair_request_path(pack_dir, current_record)


def _load_current_review_repair_request(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
) -> tuple[str, dict[str, Any]]:
    from .phase2_review_loop import _load_current_review_repair_request as _owner_load_current_review_repair_request
    return _owner_load_current_review_repair_request(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir)


async def run_codex_review_now(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    review_subject: str = "current",
    auto_apply_pass: bool = False,
) -> tuple[bool, str]:
    from .phase2_review_loop import run_codex_review_now as _owner_run_codex_review_now
    return await _owner_run_codex_review_now(task_id, ledger, settings, review_subject=review_subject, auto_apply_pass=auto_apply_pass)


async def run_codex_review_fix(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    abandon_current_repair: bool = False,
) -> tuple[bool, str]:
    from .phase2_review_loop import run_codex_review_fix as _owner_run_codex_review_fix
    return await _owner_run_codex_review_fix(task_id, ledger, settings, abandon_current_repair=abandon_current_repair)


async def run_codex_auto_loop(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    review_subject: str = "current",
    max_auto_rounds: int = PHASE2_AUTO_LOOP_REVIEW_ROUNDS,
    nonprogress_limit: int = PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT,
    max_build_attempts_per_round: int = PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW,
) -> tuple[bool, str]:
    from .phase2_review_loop import run_codex_auto_loop as _owner_run_codex_auto_loop
    return await _owner_run_codex_auto_loop(
        task_id,
        ledger,
        settings,
        review_subject=review_subject,
        max_auto_rounds=max_auto_rounds,
        nonprogress_limit=nonprogress_limit,
        max_build_attempts_per_round=max_build_attempts_per_round,
    )


async def apply_codex_review_result(
    task_id: str,
    ledger: LedgerManager,
    settings,
    review_result_arg: str,
) -> tuple[bool, str]:
    from .phase2_review_loop import apply_codex_review_result_with_continuation as _owner_apply_codex_review_result_with_continuation
    return await _owner_apply_codex_review_result_with_continuation(task_id, ledger, settings, review_result_arg)
