from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id

from .core import LedgerManager
from .phase2_handoff import ReviewLoopOutcome
from .phase2_pack_shared.artifacts import (
    AUTO_LOOP_PHASES,
    AUTO_LOOP_STATUSES,
    AUTO_LOOP_STOP_REASONS,
    DRAFT_FILE_NAME,
    latest_review_repair_request_path,
    list_versioned_json_files,
    load_attempt_history,
    next_review_repair_attempt,
    next_pre_repair_draft_path,
    review_repair_request_path,
    review_repair_summary_path,
    select_latest_verify_result,
    stale_candidate_official_output_message,
)
from .phase2_pack_shared.io import read_file_safely, read_json_safely, sha256_text, write_json
from .phase2_pack_shared.runtime_state import (
    append_review_repair_summary_note,
    auto_loop_attempt_payload as _shared_auto_loop_attempt_payload,
    auto_loop_field_defaults as _shared_auto_loop_field_defaults,
    auto_loop_review_fingerprint as _shared_auto_loop_review_fingerprint,
    auto_loop_runtime_updates as _shared_auto_loop_runtime_updates,
    auto_loop_state_from_record as _shared_auto_loop_state_from_record,
    normalize_auto_loop_must_fix as _shared_normalize_auto_loop_must_fix,
)
from .phase2_pack_views import _render_review_repair_summary, refresh_pack_runtime_view
from .phase2_review_apply import (
    _clear_current_review_repair_metadata,
    _review_repair_summary_path,
    _set_current_review_repair_metadata,
    _sync_current_review_repair_aliases,
    _write_review_repair_artifacts,
    apply_codex_review_result_once,
)
from .phase2_review_request import _load_current_codex_review_request, _resolve_review_binding_path
from .phase2_review_request import _clear_current_review_metadata
from .phase2_semantic_review import SEMANTIC_REVIEW_PROMPT_VERSION, SEMANTIC_REVIEW_RUBRIC_VERSION
from .phase2_semantic_fail_triage import classify_semantic_failure, write_semantic_fail_triage_artifacts
from .phase2_failure_budget import (
    PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW,
    PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT,
    PHASE2_AUTO_LOOP_REVIEW_ROUNDS,
)
from .phase2_pack_generation import (
    backfill_semantic_repair_history_from_request,
    build_check_prompt_pack_candidate as run_build_check_cycle,
    ensure_task_registered,
    hard_dependency_proof_debt_blocker_message,
    resolve_phase2_task,
    write_codex_review_pack as prepare_candidate_review,
    write_existing_output_review_pack as prepare_existing_review,
    write_prompt_pack as prepare_prompt_dir,
)


def _auto_loop_field_defaults() -> dict[str, Any]:
    return _shared_auto_loop_field_defaults()


def _auto_loop_state_from_record(current_record: dict[str, Any] | None) -> dict[str, Any]:
    return _shared_auto_loop_state_from_record(current_record)


def _auto_loop_runtime_updates(**overrides: Any) -> dict[str, Any]:
    return _shared_auto_loop_runtime_updates(**overrides)


def _clear_current_auto_loop_metadata(task_id: str, ledger: LedgerManager) -> None:
    ledger.update_runtime_metadata(task_id, **_auto_loop_field_defaults())


def _set_current_auto_loop_metadata(task_id: str, ledger: LedgerManager, **fields: Any) -> None:
    ledger.update_runtime_metadata(task_id, **fields)


def _auto_loop_attempt_payload(current_record: dict[str, Any] | None) -> dict[str, Any]:
    return _shared_auto_loop_attempt_payload(current_record)


def _normalize_auto_loop_must_fix(values: Any) -> list[str]:
    return _shared_normalize_auto_loop_must_fix(values)


def _auto_loop_review_fingerprint(*, primary_failure_kind: str, must_fix: list[str], review_subject_kind: str) -> str:
    return _shared_auto_loop_review_fingerprint(
        primary_failure_kind=primary_failure_kind,
        must_fix=must_fix,
        review_subject_kind=review_subject_kind,
    )


def _auto_loop_stop_reason_for_detail(detail: str) -> str:
    lowered = str(detail or "").lower()
    if "stale" in lowered or "review-subject existing" in lowered:
        return "freshness_error"
    return "hard_failure"


def _count_auto_loop_build_attempts(pack_dir: Path, task_id: str, round_number: int) -> int:
    history = load_attempt_history(pack_dir, task_id)
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
    state = _auto_loop_state_from_record(current_record)
    max_round = max(int(state["round"] or 0), 0)
    history = load_attempt_history(pack_dir, task_id)
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
    from .phase2_review_request import _resolve_review_binding_path

    return _resolve_review_binding_path(raw, pack_dir=pack_dir)


def _latest_verify_result_payload(pack_dir: Path) -> tuple[Path | None, dict[str, Any]]:
    verify_path = select_latest_verify_result(pack_dir)
    if verify_path is None or not verify_path.exists():
        return None, {}
    payload = read_json_safely(verify_path, {})
    if not isinstance(payload, dict):
        return verify_path, {}
    return verify_path, payload


def _seeded_repair_request_path(pack_dir: Path, current_record: dict[str, Any]) -> str:
    raw = str(current_record.get("current_review_repair_request_file", "") or "").strip()
    if raw:
        from .phase2_review_request import _resolve_review_binding_path

        return str(_resolve_review_binding_path(raw, pack_dir=pack_dir))
    return ""


def _current_build_ready_candidate_hash(pack_dir: Path, current_record: dict[str, Any]) -> str:
    for key in ("latest_build_ready_candidate_hash", "latest_build_candidate_hash"):
        value = str(current_record.get(key, "") or "").strip()
        if value:
            return value
    raw_result = str(current_record.get("latest_build_result_file", "") or "").strip()
    if not raw_result:
        return ""
    result_path = Path(raw_result).expanduser()
    if not result_path.is_absolute():
        result_path = (pack_dir / result_path).resolve()
    payload = read_json_safely(result_path, {})
    if not isinstance(payload, dict):
        return ""
    return str(payload.get("candidate_hash", "") or "").strip()


def _semantic_failed_review_subject_hash(repair_request: dict[str, Any]) -> str:
    failed_hash = str(repair_request.get("failed_review_subject_hash", "") or "").strip()
    if not failed_hash:
        return ""
    failed_verdict = str(repair_request.get("failed_verdict", "") or "").strip().lower()
    failed_phase2_status = str(repair_request.get("failed_phase2_status", "") or "").strip().lower()
    failure_kind = str(
        repair_request.get("primary_failure_kind", "")
        or repair_request.get("failed_disposition", "")
        or repair_request.get("disposition", "")
        or ""
    ).strip().lower()
    semantic_failure_kinds = {
        "semantic_review_fail",
        "official_output_review_fail",
        "codex_review_fail_no_promotion",
        "codex_review_pass_fail_no_promotion",
    }
    if failed_verdict == "fail" or failed_phase2_status == "fail" or failure_kind in semantic_failure_kinds:
        return failed_hash
    return ""


def _same_candidate_after_semantic_failure_detail(
    *,
    task_id: str,
    pack_dir: Path,
    current_record: dict[str, Any],
    build_attempts_used: int,
    max_build_attempts_per_round: int,
) -> str:
    request_path = _resolve_current_review_repair_request_path(pack_dir, current_record)
    if request_path is None or not request_path.exists():
        return ""
    repair_request = read_json_safely(request_path, {})
    if not isinstance(repair_request, dict):
        return ""
    failed_hash = _semantic_failed_review_subject_hash(repair_request)
    if not failed_hash:
        return ""
    candidate_hash = _current_build_ready_candidate_hash(pack_dir, current_record)
    if not candidate_hash or candidate_hash != failed_hash:
        return ""
    return (
        f"Auto-loop built the same candidate after a semantic review failure for {task_id}. "
        "This is not a hard failure, but the candidate cannot be sent back to semantic review unchanged. "
        "The current Codex agent must repair `draft.lean` or the related Lean proof artifact, then continue "
        f"this same-session auto-loop. Build attempts used in this round: "
        f"{build_attempts_used}/{max_build_attempts_per_round}."
    )


def _request_path_attempt(request_path: Path) -> int:
    match = re.fullmatch(r"review_repair_request_v(\d+)\.json", request_path.name)
    if match:
        return int(match.group(1))
    return 0


def _resolve_repair_path(pack_dir: Path, raw_path: Any) -> Path | None:
    raw = str(raw_path or "").strip()
    if not raw:
        return None
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = (pack_dir / path).resolve()
    return path


def _triage_requires_diagnoser(triage: Any) -> bool:
    if not isinstance(triage, dict):
        return False
    return bool(triage.get("needs_diagnoser", False)) and not bool(triage.get("local_repair_allowed", True))


def _same_candidate_diagnoser_stop_detail(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    current_record: dict[str, Any],
) -> str:
    task_id = task["block_id"]
    request_path = _resolve_current_review_repair_request_path(pack_dir, current_record)
    if request_path is None or not request_path.exists():
        return ""
    repair_request = read_json_safely(request_path, {})
    if not isinstance(repair_request, dict):
        return ""

    triage_result = repair_request.get("semantic_fail_triage", {})
    if not _triage_requires_diagnoser(triage_result):
        review_result_path = _resolve_repair_path(pack_dir, repair_request.get("failed_review_result_file", ""))
        review_result = read_json_safely(review_result_path, {}) if review_result_path else {}
        if not isinstance(review_result, dict):
            review_result = {}
        _, _, needs_diagnoser = classify_semantic_failure(review_result)
        if not needs_diagnoser:
            return ""

        review_input_path = _resolve_repair_path(pack_dir, repair_request.get("failed_review_input_file", ""))
        review_input = read_json_safely(review_input_path, {}) if review_input_path else {}
        if not isinstance(review_input, dict):
            review_input = {}
        failed_subject_path = (
            _resolve_repair_path(pack_dir, repair_request.get("failed_review_subject_file", ""))
            or _resolve_repair_path(pack_dir, repair_request.get("next_draft_seed_file", ""))
            or (pack_dir / DRAFT_FILE_NAME)
        )
        attempt = _request_path_attempt(request_path) or next_review_repair_attempt(pack_dir)
        triage_result = write_semantic_fail_triage_artifacts(
            task=task,
            pack_dir=pack_dir,
            review_input=review_input,
            review_result=review_result,
            repair_request=repair_request,
            failed_review_subject_file=failed_subject_path,
            attempt=attempt,
        )
        repair_request["semantic_fail_triage"] = triage_result
        write_json(request_path, repair_request)

    if not _triage_requires_diagnoser(triage_result):
        return ""

    ledger.update_runtime_metadata(
        task_id,
        latest_semantic_fail_triage_file=str(triage_result.get("triage_path", "")),
        latest_semantic_fail_triage_category=str(triage_result.get("category", "")),
        latest_semantic_fail_triage_needs_diagnoser=bool(triage_result.get("needs_diagnoser", False)),
        latest_semantic_fail_triage_local_repair_allowed=bool(triage_result.get("local_repair_allowed", False)),
        latest_diagnoser_prompt_file=str(triage_result.get("prompt_path", "")),
        latest_diagnosis_state=str(triage_result.get("diagnosis_state", "")),
    )
    prompt_path = str(triage_result.get("prompt_path", "") or "").strip()
    category = str(triage_result.get("category", "") or "").strip()
    prompt_note = f" Diagnoser prompt: {prompt_path}" if prompt_path else ""
    return (
        f"Auto-loop stopped for {task_id}: the rebuilt candidate is unchanged after semantic failure, "
        f"and semantic-fail triage category `{category}` requires read-only diagnoser before ordinary repair."
        f"{prompt_note}"
    )


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
) -> tuple[dict[str, Any], bool]:
    state = _auto_loop_state_from_record(current_record)
    if (
        state["enabled"]
        and state["status"] == "active"
        and state["entry_subject"] == review_subject
        and state["max_rounds"] == max_auto_rounds
        and state["nonprogress_limit"] == nonprogress_limit
        and state["max_build_attempts_per_round"] == max_build_attempts_per_round
    ):
        return state, False

    active_repair_request = _seeded_repair_request_path(pack_dir, current_record)
    seeded_repair_request = ""
    prior_seed_marker = str(state["last_repair_request_file"] or "").strip()
    if active_repair_request and prior_seed_marker:
        resolved_seed_marker = _resolve_review_binding_path(prior_seed_marker, pack_dir=pack_dir)
        resolved_active_request = Path(active_repair_request)
        if resolved_seed_marker == resolved_active_request and resolved_active_request.exists():
            seeded_repair_request = active_repair_request

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
        current_auto_loop_last_repair_request_file=seeded_repair_request,
    )
    _set_current_auto_loop_metadata(task_id, ledger, **updates)
    return _auto_loop_state_from_record({**current_record, **updates}), bool(seeded_repair_request)


def _stop_auto_loop(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    reason: str,
    detail: str,
) -> ReviewLoopOutcome:
    task_id = task["block_id"]
    _set_current_auto_loop_metadata(
        task_id,
        ledger,
        current_auto_loop_enabled=True,
        current_auto_loop_status="stopped",
        current_auto_loop_phase="stopped",
        current_auto_loop_stop_reason=reason,
    )
    refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return ReviewLoopOutcome(
        False,
        detail,
        next_action="diagnoser_read_only" if reason == "diagnoser_required" else "stopped",
        stop_reason=reason,
    )


def _complete_auto_loop(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    detail: str,
) -> ReviewLoopOutcome:
    task_id = task["block_id"]
    _set_current_auto_loop_metadata(
        task_id,
        ledger,
        current_auto_loop_enabled=True,
        current_auto_loop_status="completed",
        current_auto_loop_phase="completed",
        current_auto_loop_stop_reason="passed",
    )
    refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return ReviewLoopOutcome(True, detail, next_action="completed", stop_reason="completed")


def _repair_ready_requires_diagnoser(repair_ready: dict[str, Any] | None) -> tuple[bool, dict[str, Any]]:
    if not isinstance(repair_ready, dict):
        return False, {}
    request_payload = repair_ready.get("request_payload", {})
    if not isinstance(request_payload, dict):
        return False, {}
    triage = request_payload.get("semantic_fail_triage", {})
    if not isinstance(triage, dict):
        return False, {}
    return (
        bool(triage.get("needs_diagnoser", False))
        and not bool(triage.get("local_repair_allowed", True)),
        triage,
    )


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
        manifest = read_json_safely(quarantine_dir / "quarantine_manifest.json", {})
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
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    repair_dispositions = {
        "official_output_review_fail",
        "official_output_review_inconclusive",
        "codex_review_fail_no_promotion",
        "codex_review_inconclusive_no_promotion",
        "codex_review_pass_fail_no_promotion",
    }
    for verify_path in reversed(list_versioned_json_files(pack_dir, "verify_result")):
        verify_payload = read_json_safely(verify_path, {})
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
        review_input = read_json_safely(review_input_path, {})
        if not isinstance(review_input, dict):
            continue
        review_result_payload = read_json_safely(review_result_path, {})
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
            stale_official_message = stale_candidate_official_output_message(
                task_id=task_id,
                source_plan=str(task.get("source_plan", "unknown") or "unknown"),
                settings=settings,
                candidate_path=subject_path,
                candidate_hash=str(review_input.get("review_subject_hash", "") or review_input.get("candidate", {}).get("hash", "") or ""),
                draft_path=pack_dir / DRAFT_FILE_NAME,
                action="review-fix backfill seed",
            )
            if stale_official_message:
                return stale_official_message, {}
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
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return "", repair_ready
    return "No failed review-apply result is available to backfill a repair cycle.", {}


def _resolve_current_review_repair_request_path(pack_dir: Path, current_record: dict[str, Any]) -> Path | None:
    raw_request = str(current_record.get("current_review_repair_request_file", "") or "").strip()
    if raw_request:
        request_path = Path(raw_request).expanduser()
        if not request_path.is_absolute():
            request_path = (pack_dir / request_path).resolve()
        return request_path
    latest_request = latest_review_repair_request_path(pack_dir)
    if latest_request.exists():
        return latest_request
    return None


def _load_current_review_repair_request(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
) -> tuple[str, dict[str, Any]]:
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    current_request_raw = str(current_record.get("current_review_repair_request_file", "") or "").strip()
    if not current_request_raw:
        backfill_error, _ = _backfill_review_repair_request_from_latest_failed_review(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
        )
        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        current_request_raw = str(current_record.get("current_review_repair_request_file", "") or "").strip()
        if not current_request_raw:
            if backfill_error:
                return f"No active review repair request is recorded in the current repair state. {backfill_error}", {}
            return "No active review repair request is recorded in the current repair state.", {}
    request_path = _resolve_current_review_repair_request_path(pack_dir, current_record if isinstance(current_record, dict) else {})
    if request_path is None or not request_path.exists():
        return "No active review repair request is available; run review-apply on a failed review first.", {}
    request_payload = read_json_safely(request_path, {})
    if not isinstance(request_payload, dict):
        return "Current review repair request is invalid JSON.", {}
    if canonicalize_block_id(str(request_payload.get("task_id", "") or "")) != task_id:
        return f"Current review repair request task id mismatch: expected {task_id}", {}
    current_request_path = Path(current_request_raw).expanduser()
    if not current_request_path.is_absolute():
        current_request_path = (pack_dir / current_request_path).resolve()
    if current_request_path != request_path:
        return "Current review repair request has been superseded by a different active repair cycle.", {}
    if str(current_record.get("current_review_request_file", "") or "").strip():
        return "Current review repair request is stale because a newer active review request already exists.", {}

    failed_review_input_path = _resolve_review_binding_path(str(request_payload.get("failed_review_input_file", "")), pack_dir=pack_dir)
    failed_review_result_path = _resolve_review_binding_path(str(request_payload.get("failed_review_result_file", "")), pack_dir=pack_dir)
    failed_review_report_path = _resolve_review_binding_path(str(request_payload.get("failed_review_report_file", "")), pack_dir=pack_dir)
    failed_review_subject_path = _resolve_review_binding_path(str(request_payload.get("failed_review_subject_file", "")), pack_dir=pack_dir)
    next_draft_seed_path = _resolve_review_binding_path(str(request_payload.get("next_draft_seed_file", "")), pack_dir=pack_dir)
    summary_path = (
        Path(str(current_record.get("current_review_repair_summary_file", "") or "")).expanduser()
        if str(current_record.get("current_review_repair_summary_file", "") or "").strip()
        else _review_repair_summary_path(
            pack_dir,
            int(re.search(r"_v(\d+)\.json$", request_path.name).group(1)) if re.search(r"_v(\d+)\.json$", request_path.name) else 1,
        )
    )
    if not summary_path.is_absolute():
        summary_path = (pack_dir / summary_path).resolve()

    for path, label in (
        (failed_review_input_path, "failed review input"),
        (failed_review_result_path, "failed review result"),
        (failed_review_report_path, "failed review report"),
        (failed_review_subject_path, "failed review subject"),
        (next_draft_seed_path, "repair seed file"),
    ):
        if not path.exists():
            return f"Current review repair request is stale because the {label} is missing.", {}

    failed_review_result = read_json_safely(failed_review_result_path, {})
    if not isinstance(failed_review_result, dict):
        return "Current review repair request is stale because the failed review result JSON is invalid.", {}
    result_verdict = str(failed_review_result.get("verdict", "") or "").strip().lower()
    result_phase2_status = str(failed_review_result.get("phase2_status", "") or "").strip().lower()
    request_phase2_status = str(request_payload.get("failed_phase2_status", "") or "").strip().lower()
    is_semantic_failure = result_verdict in {"fail", "inconclusive"} or (
        result_verdict == "pass"
        and result_phase2_status == "fail"
        and request_phase2_status == "fail"
    )
    if not is_semantic_failure:
        return (
            "Current review repair request is stale because the bound review result is no longer "
            "a semantic verdict/task-projection failure.",
            {},
        )
    current_result_hash = sha256_text(failed_review_result_path.read_text(encoding="utf-8"))
    if current_result_hash != str(request_payload.get("review_result_hash", "") or ""):
        return "Current review repair request is stale because the bound review result hash changed.", {}

    failed_review_input = read_json_safely(failed_review_input_path, {})
    if not isinstance(failed_review_input, dict):
        return "Current review repair request is stale because the bound review input JSON is invalid.", {}
    if str(failed_review_input.get("review_basis_hash", "") or "") != str(request_payload.get("review_basis_hash", "") or ""):
        return "Current review repair request is stale because the bound review basis hash changed.", {}

    backfill_semantic_repair_history_from_request(
        pack_dir=pack_dir,
        task_id=task_id,
        request_path=request_path,
        request_payload=request_payload,
        failed_review_result=failed_review_result,
        failed_review_subject_path=failed_review_subject_path,
    )

    current_subject_hash = sha256_text(read_file_safely(failed_review_subject_path))
    if current_subject_hash != str(request_payload.get("failed_review_subject_hash", "") or ""):
        return "Current review repair request is stale because the failed review subject hash changed.", {}
    if str(request_payload.get("review_subject_kind", "") or "candidate") == "candidate":
        stale_official_message = stale_candidate_official_output_message(
            task_id=task_id,
            source_plan=str(task.get("source_plan", "unknown") or "unknown"),
            settings=settings,
            candidate_path=failed_review_subject_path,
            candidate_hash=current_subject_hash,
            draft_path=pack_dir / DRAFT_FILE_NAME,
            action="review-fix repair seed",
        )
        if stale_official_message:
            return stale_official_message, {}

    warnings: list[str] = []
    if int(request_payload.get("origin_prompt_version") or 0) != SEMANTIC_REVIEW_PROMPT_VERSION:
        warnings.append(
            f"Repair request was created under semantic review prompt version {request_payload.get('origin_prompt_version')}, "
            f"but the current prompt version is {SEMANTIC_REVIEW_PROMPT_VERSION}. The next review-now will use the current standard."
        )
    if int(request_payload.get("origin_rubric_version") or 0) != SEMANTIC_REVIEW_RUBRIC_VERSION:
        warnings.append(
            f"Repair request was created under semantic review rubric version {request_payload.get('origin_rubric_version')}, "
            f"but the current rubric version is {SEMANTIC_REVIEW_RUBRIC_VERSION}. The next review-now will use the current standard."
        )
    if str(request_payload.get("origin_result_schema_version", "") or "") not in {"", "phase2.semantic_review.result.v3"}:
        warnings.append(
            f"Repair request references review result schema `{request_payload.get('origin_result_schema_version')}`; "
            "review-fix will continue, but the next review-now will re-evaluate under the current schema."
        )

    return "", {
        "request_path": request_path,
        "request_payload": request_payload,
        "failed_review_input_path": failed_review_input_path,
        "failed_review_input": failed_review_input,
        "failed_review_result_path": failed_review_result_path,
        "failed_review_result": failed_review_result,
        "failed_review_report_path": failed_review_report_path,
        "failed_review_subject_path": failed_review_subject_path,
        "next_draft_seed_path": next_draft_seed_path,
        "summary_path": summary_path,
        "warnings": warnings,
    }


async def apply_codex_review_result_with_continuation(
    task_id: str,
    ledger: LedgerManager,
    settings,
    review_result_arg: str,
) -> tuple[bool, str]:
    outcome = await apply_codex_review_result_once(task_id, ledger, settings, review_result_arg)
    if outcome.next_action != "review_fix":
        return outcome.success, outcome.detail
    repair_success, repair_detail = await run_codex_review_fix(task_id, ledger, settings)
    if repair_success:
        return False, f"{outcome.detail} Repair loop continued automatically. {repair_detail}"
    return outcome.success, f"{outcome.detail} Repair request was created, but automatic review-fix could not continue: {repair_detail}"


async def run_codex_review_now(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    review_subject: str = "current",
    auto_apply_pass: bool = False,
) -> ReviewLoopOutcome:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return ReviewLoopOutcome(False, proof_debt_blocker, next_action="resolve_blocker")
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        pack_dir = prepare_prompt_dir(task_id, ledger, settings, task=task)

    review_subject = str(review_subject or "current").strip().lower() or "current"
    if review_subject not in {"current", "existing", "candidate"}:
        return ReviewLoopOutcome(
            False,
            f"Unsupported review-now subject: {review_subject}",
            next_action="resolve_blocker",
        )

    request_info: dict[str, Any] = {}
    if review_subject == "current":
        validation_error, request_info = _load_current_codex_review_request(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
        )
        if validation_error:
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            return ReviewLoopOutcome(
                False,
                f"Current codex review request is stale or invalid: {validation_error} "
                "Prepare a fresh request with `review-now --review-subject existing` or `review-now --review-subject candidate`.",
                next_action="resolve_blocker",
            )
        if request_info.get("result_exists"):
            review_subject = "existing" if request_info.get("review_subject_kind") == "official_output" else "candidate"
            request_info = {}

    if review_subject == "existing":
        success, detail = await prepare_existing_review(task_id, ledger, settings, force_new_attempt=True)
        if not success:
            return ReviewLoopOutcome(False, detail, next_action="resolve_blocker")
        validation_error, request_info = _load_current_codex_review_request(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir)
        if validation_error:
            return ReviewLoopOutcome(False, validation_error, next_action="resolve_blocker")
    elif review_subject == "candidate":
        success, detail = await prepare_candidate_review(task_id, ledger, settings)
        if not success:
            return ReviewLoopOutcome(False, detail, next_action="resolve_blocker")
        validation_error, request_info = _load_current_codex_review_request(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir)
        if validation_error:
            return ReviewLoopOutcome(False, validation_error, next_action="resolve_blocker")

    request_path = Path(str(request_info.get("request_path", "")))
    expected_result_path = Path(str(request_info.get("expected_result_path", "")))
    detail = (
        f"Codex review request is ready for {task_id}. "
        f"Request: {request_path}. "
        f"Expected result: {expected_result_path}. "
        "In a Codex session, the orchestrating agent must use an independent read-only reviewer "
        "subagent or configured reviewer runner to write the semantic_review_result JSON."
    )
    if auto_apply_pass:
        detail += " `--auto-apply-pass` was requested; if the Codex reviewer reaches a pass verdict, run review-apply in the same Codex session."
    if review_subject == "candidate":
        _clear_current_review_repair_metadata(task_id, ledger)
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
    return ReviewLoopOutcome(
        True,
        detail,
        next_action="reviewer_write_result",
        request_path=str(request_path),
        expected_result_path=str(expected_result_path),
    )


async def run_codex_review_fix(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    abandon_current_repair: bool = False,
) -> ReviewLoopOutcome:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return ReviewLoopOutcome(False, proof_debt_blocker, next_action="resolve_blocker")
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        return ReviewLoopOutcome(
            False,
            f"Phase 2 prompt pack does not exist for review-fix: {task_id}",
            next_action="resolve_blocker",
        )

    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    if abandon_current_repair:
        request_path = _resolve_current_review_repair_request_path(pack_dir, current_record if isinstance(current_record, dict) else {})
        summary_raw = str(current_record.get("current_review_repair_summary_file", "") or "").strip()
        if request_path is None or not summary_raw:
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            return ReviewLoopOutcome(
                False,
                "No active review repair cycle is available to abandon.",
                next_action="resolve_blocker",
            )
        summary_path = Path(summary_raw).expanduser()
        if not summary_path.is_absolute():
            summary_path = (pack_dir / summary_path).resolve()
        if not summary_path.exists():
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            return ReviewLoopOutcome(
                False,
                "Active review repair summary is missing; cannot abandon the current repair cycle.",
                next_action="resolve_blocker",
            )
        append_review_repair_summary_note(summary_path, "Current repair cycle was abandoned by explicit operator request.")
        if request_path.exists():
            _sync_current_review_repair_aliases(pack_dir, request_path=request_path, summary_path=summary_path)
            _clear_current_review_repair_metadata(task_id, ledger)
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return ReviewLoopOutcome(
            True,
            f"Abandoned the active review repair cycle for {task_id}.",
            next_action="stopped",
            stop_reason="user_interruption",
        )

    validation_error, repair_info = _load_current_review_repair_request(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
    )
    if validation_error:
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        return ReviewLoopOutcome(
            False,
            f"Current review repair request is stale or invalid: {validation_error}",
            next_action="resolve_blocker",
        )

    request_payload = repair_info["request_payload"]
    seed_path = Path(str(repair_info["next_draft_seed_path"]))
    draft_path = pack_dir / DRAFT_FILE_NAME
    seed_text = read_file_safely(seed_path)
    archive_path = ""
    if not draft_path.exists():
        draft_path.write_text(seed_text, encoding="utf-8")
    else:
        draft_text = read_file_safely(draft_path)
        if draft_text != seed_text:
            archive_target = next_pre_repair_draft_path(pack_dir)
            archive_target.write_text(draft_text, encoding="utf-8")
            draft_path.write_text(seed_text, encoding="utf-8")
            archive_path = str(archive_target)

    summary_path = Path(str(repair_info["summary_path"]))
    warnings = list(repair_info.get("warnings", []))
    summary_path.write_text(
        _render_review_repair_summary(request_payload, warning_lines=warnings, archive_file=archive_path),
        encoding="utf-8",
    )
    _sync_current_review_repair_aliases(
        pack_dir,
        request_path=Path(str(repair_info["request_path"])),
        summary_path=summary_path,
    )
    _set_current_review_repair_metadata(
        task_id,
        ledger,
        request_file=str(repair_info["request_path"]),
        summary_file=str(summary_path),
        seed_file=str(seed_path),
        origin_result_file=str(request_payload.get("failed_review_result_file", "") or ""),
        archive_file=archive_path,
    )
    refresh_pack_runtime_view(task, ledger, settings, pack_dir)

    detail = (
        f"Review repair contract is active for {task_id}. "
        f"Seeded `draft.lean` from {seed_path}. "
        "Next step: edit `draft.lean` to remove the semantic defect, then run build-check."
    )
    if archive_path:
        detail += f" Archived the previous draft to {archive_path}."
    if warnings:
        detail += " Warnings: " + " ".join(warnings)
    return ReviewLoopOutcome(True, detail, next_action="author_repair")


async def run_codex_auto_loop(
    task_id: str,
    ledger: LedgerManager,
    settings,
    *,
    review_subject: str = "current",
    max_auto_rounds: int = PHASE2_AUTO_LOOP_REVIEW_ROUNDS,
    nonprogress_limit: int = PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT,
    max_build_attempts_per_round: int = PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW,
) -> ReviewLoopOutcome:
    task = ensure_task_registered(resolve_phase2_task(task_id, ledger, settings), ledger)
    task_id = task["block_id"]
    proof_debt_blocker = hard_dependency_proof_debt_blocker_message(task, ledger)
    if proof_debt_blocker:
        return ReviewLoopOutcome(False, proof_debt_blocker, next_action="resolve_blocker")
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not pack_dir.exists():
        pack_dir = prepare_prompt_dir(task_id, ledger, settings, task=task)

    review_subject = str(review_subject or "current").strip().lower() or "current"
    if review_subject not in {"current", "existing", "candidate"}:
        return ReviewLoopOutcome(
            False,
            f"Unsupported auto-loop review subject: {review_subject}",
            next_action="resolve_blocker",
        )
    if max_auto_rounds < 1:
        return ReviewLoopOutcome(False, "--max-auto-rounds must be at least 1.", next_action="resolve_blocker")
    if nonprogress_limit < 1:
        return ReviewLoopOutcome(False, "--nonprogress-limit must be at least 1.", next_action="resolve_blocker")
    if max_build_attempts_per_round < 1:
        return ReviewLoopOutcome(
            False,
            "--max-build-attempts-per-round must be at least 1.",
            next_action="resolve_blocker",
        )

    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    _, resumed_seeded_repair = _initialize_auto_loop_state(
        task_id,
        ledger,
        pack_dir=pack_dir,
        current_record=current_record if isinstance(current_record, dict) else {},
        review_subject=review_subject,
        max_auto_rounds=max_auto_rounds,
        nonprogress_limit=nonprogress_limit,
        max_build_attempts_per_round=max_build_attempts_per_round,
    )
    if resumed_seeded_repair:
        validation_error, _ = _load_current_review_repair_request(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
        )
        if validation_error:
            return _stop_auto_loop(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                reason="freshness_error",
                detail=f"Auto-loop stopped for {task_id}: active seeded repair request is stale or invalid: {validation_error}",
            )
    refresh_pack_runtime_view(task, ledger, settings, pack_dir)

    while True:
        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        current_record = current_record if isinstance(current_record, dict) else {}
        state = _auto_loop_state_from_record(current_record)
        if state["round"] > state["max_rounds"] > 0:
            return _stop_auto_loop(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                reason="max_rounds",
                detail=f"Auto-loop stopped for {task_id}: exceeded max rounds ({state['round']} > {state['max_rounds']}).",
            )

        expected_result_path = _expected_current_review_result_path(pack_dir, current_record)
        if expected_result_path is not None and expected_result_path.exists():
            _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="applying", current_auto_loop_status="active")
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            outcome = await apply_codex_review_result_once(task_id, ledger, settings, str(expected_result_path))
            verify_path, verify_payload = _latest_verify_result_payload(pack_dir)
            disposition = str(verify_payload.get("disposition", "") or outcome.disposition)
            if outcome.success:
                return _complete_auto_loop(task=task, ledger=ledger, settings=settings, pack_dir=pack_dir, detail=outcome.detail)
            if disposition == "codex_review_invalid_no_promotion":
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="freshness_error",
                    detail=f"Auto-loop stopped for {task_id}: {outcome.detail}",
                )
            requires_diagnoser, triage = _repair_ready_requires_diagnoser(outcome.repair_ready)
            if requires_diagnoser:
                prompt_path = str(triage.get("prompt_path", "") or "").strip()
                category = str(triage.get("category", "") or "").strip()
                prompt_note = f" Diagnoser prompt: {prompt_path}" if prompt_path else ""
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="diagnoser_required",
                    detail=(
                        f"Auto-loop stopped for {task_id}: semantic-fail triage category `{category}` "
                        f"requires read-only route/source diagnosis before ordinary repair.{prompt_note}"
                    ),
                )
            if outcome.next_action == "review_fix":
                repair_success, repair_detail = await run_codex_review_fix(task_id, ledger, settings)
                if not repair_success:
                    return _stop_auto_loop(
                        task=task,
                        ledger=ledger,
                        settings=settings,
                        pack_dir=pack_dir,
                        reason="freshness_error" if "stale" in repair_detail.lower() else "hard_failure",
                        detail=f"Auto-loop stopped for {task_id}: {outcome.detail} Repair continuation failed: {repair_detail}",
                    )
            repair_request_raw = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("current_review_repair_request_file", "") or "").strip()
            if not repair_request_raw:
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="hard_failure",
                    detail=f"Auto-loop stopped for {task_id}: review apply failed without an active repair request. {outcome.detail}",
                )
            repair_request_path = _resolve_review_binding_path(repair_request_raw, pack_dir=pack_dir)
            repair_request = read_json_safely(repair_request_path, {})
            if not isinstance(repair_request, dict):
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="hard_failure",
                    detail=f"Auto-loop stopped for {task_id}: repair request JSON is invalid after review apply.",
                )
            current_candidate_hash = str(repair_request.get("failed_review_subject_hash", "") or verify_payload.get("candidate_hash", "") or "")
            review_subject_kind = str(repair_request.get("review_subject_kind", "") or "candidate")
            primary_failure_kind = str(verify_payload.get("primary_failure_kind", "") or "semantic_review_fail")
            review_fingerprint = _auto_loop_review_fingerprint(
                primary_failure_kind=primary_failure_kind,
                must_fix=_normalize_auto_loop_must_fix(repair_request.get("must_fix", [])),
                review_subject_kind=review_subject_kind,
            )
            repeated_nonprogress = bool(
                (state["last_candidate_hash"] and state["last_candidate_hash"] == current_candidate_hash)
                or (state["last_review_fingerprint"] and state["last_review_fingerprint"] == review_fingerprint)
            )
            next_nonprogress = state["consecutive_nonprogress"] + 1 if repeated_nonprogress else 0
            _set_current_auto_loop_metadata(
                task_id,
                ledger,
                current_auto_loop_last_candidate_hash=current_candidate_hash,
                current_auto_loop_last_review_fingerprint=review_fingerprint,
                current_auto_loop_consecutive_nonprogress=next_nonprogress,
            )
            if next_nonprogress >= state["nonprogress_limit"]:
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="nonprogress",
                    detail=f"Auto-loop stopped for {task_id}: non-progress threshold reached after repeated semantic review failures.",
                )
            _set_current_auto_loop_metadata(
                task_id,
                ledger,
                current_auto_loop_round=state["round"] + 1,
                current_auto_loop_phase="entry",
                current_auto_loop_status="active",
            )
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            continue

        current_review_request = str(current_record.get("current_review_request_file", "") or "").strip()
        if current_review_request:
            validation_error, _request_payload = _load_current_codex_review_request(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
            )
            if validation_error:
                _clear_current_review_metadata(task_id, ledger)
                _set_current_auto_loop_metadata(
                    task_id,
                    ledger,
                    current_auto_loop_phase="entry",
                    current_auto_loop_status="active",
                )
                refresh_pack_runtime_view(task, ledger, settings, pack_dir)
                continue
            _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="reviewing", current_auto_loop_status="active")
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            expected = _expected_current_review_result_path(pack_dir, current_record)
            return ReviewLoopOutcome(
                True,
                f"Auto-loop is at the reviewer step for {task_id}. The orchestrating Codex agent must now use an independent "
                f"read-only reviewer subagent or configured reviewer runner to write the canonical semantic_review_result JSON, "
                f"then continue this same-session auto-loop now. The author must not self-review the candidate. "
                f"Request: {current_record.get('current_review_request_file', '(none)')}. "
                f"Expected result: {expected if expected is not None else '(none)'}.",
                next_action="reviewer_write_result",
                request_path=str(_request_payload.get("request_path", current_review_request)),
                expected_result_path=str(expected) if expected is not None else "",
            )

        active_repair_request = _seeded_repair_request_path(pack_dir, current_record)
        if active_repair_request and active_repair_request != state["last_repair_request_file"]:
            _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="repair_seeded", current_auto_loop_status="active")
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            success, detail = await run_codex_review_fix(task_id, ledger, settings)
            if not success:
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="freshness_error" if "stale" in detail.lower() else "hard_failure",
                    detail=f"Auto-loop stopped for {task_id}: {detail}",
                )
            _set_current_auto_loop_metadata(
                task_id,
                ledger,
                current_auto_loop_last_repair_request_file=active_repair_request,
                current_auto_loop_phase="repair_seeded",
                current_auto_loop_status="active",
            )
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        current_record = current_record if isinstance(current_record, dict) else {}
        state = _auto_loop_state_from_record(current_record)

        if state["phase"] == "entry":
            if review_subject == "existing":
                _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="review_prepared", current_auto_loop_status="active")
                success, detail = await run_codex_review_now(task_id, ledger, settings, review_subject="existing")
                if not success:
                    return _stop_auto_loop(
                        task=task,
                        ledger=ledger,
                        settings=settings,
                        pack_dir=pack_dir,
                        reason=_auto_loop_stop_reason_for_detail(detail),
                        detail=f"Auto-loop stopped for {task_id}: {detail}",
                    )
                refresh_pack_runtime_view(task, ledger, settings, pack_dir)
                continue
            if review_subject == "candidate":
                _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="review_prepared", current_auto_loop_status="active")
                success, detail = await run_codex_review_now(task_id, ledger, settings, review_subject="candidate")
                if not success:
                    return _stop_auto_loop(
                        task=task,
                        ledger=ledger,
                        settings=settings,
                        pack_dir=pack_dir,
                        reason=_auto_loop_stop_reason_for_detail(detail),
                        detail=f"Auto-loop stopped for {task_id}: {detail}",
                    )
                refresh_pack_runtime_view(task, ledger, settings, pack_dir)
                continue

        build_attempts_used = _count_auto_loop_build_attempts(pack_dir, task_id, state["round"])
        if build_attempts_used >= state["max_build_attempts_per_round"]:
            return _stop_auto_loop(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                reason="build_budget_exhausted",
                detail=f"Auto-loop stopped for {task_id}: build budget exhausted for round {state['round']} after {build_attempts_used} build-check attempt(s).",
            )

        _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="build_checking", current_auto_loop_status="active")
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        success, detail = await run_build_check_cycle(task_id, ledger, settings)
        build_attempts_used = _count_auto_loop_build_attempts(pack_dir, task_id, state["round"])
        if not success:
            if build_attempts_used >= state["max_build_attempts_per_round"]:
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="build_budget_exhausted",
                    detail=f"Auto-loop stopped for {task_id}: build budget exhausted for round {state['round']} after {build_attempts_used} build-check attempt(s).",
                )
            _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="authoring", current_auto_loop_status="active")
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            return ReviewLoopOutcome(
                True,
                f"Auto-loop build-check failed for {task_id}. The current Codex agent must now repair `draft.lean` "
                f"and continue this same-session auto-loop now. "
                f"Build attempts used in this round: {build_attempts_used}/{state['max_build_attempts_per_round']}. "
                f"Latest detail: {detail}",
                next_action="author_repair",
            )

        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        current_record = current_record if isinstance(current_record, dict) else {}
        same_candidate_detail = _same_candidate_after_semantic_failure_detail(
            task_id=task_id,
            pack_dir=pack_dir,
            current_record=current_record,
            build_attempts_used=build_attempts_used,
            max_build_attempts_per_round=state["max_build_attempts_per_round"],
        )
        if same_candidate_detail:
            diagnoser_detail = _same_candidate_diagnoser_stop_detail(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                current_record=current_record,
            )
            if diagnoser_detail:
                return _stop_auto_loop(
                    task=task,
                    ledger=ledger,
                    settings=settings,
                    pack_dir=pack_dir,
                    reason="diagnoser_required",
                    detail=diagnoser_detail,
                )
            _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="authoring", current_auto_loop_status="active")
            refresh_pack_runtime_view(task, ledger, settings, pack_dir)
            return ReviewLoopOutcome(True, same_candidate_detail, next_action="author_repair")

        _set_current_auto_loop_metadata(task_id, ledger, current_auto_loop_phase="review_prepared", current_auto_loop_status="active")
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        success, detail = await run_codex_review_now(task_id, ledger, settings, review_subject="candidate")
        if not success:
            return _stop_auto_loop(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                reason=_auto_loop_stop_reason_for_detail(detail),
                detail=f"Auto-loop stopped for {task_id}: {detail}",
            )
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
