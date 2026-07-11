from __future__ import annotations

import shutil
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, canonicalize_task_dict

from .core import LedgerManager
from .phase2_pack_shared.artifacts import (
    DRAFT_FILE_NAME,
    SEMANTIC_REVIEW_REQUEST_ALIAS,
    SEMANTIC_REVIEW_REQUEST_PREFIX,
    SEMANTIC_REVIEW_RESULT_TEMPLATE_ALIAS,
    find_existing_task_file,
    select_latest_existing_task_file,
    stale_candidate_official_output_message,
)
from .phase2_pack_shared.io import (
    copy_file,
    path_exists,
    read_file_safely,
    read_json_safely,
    sha256_json,
    sha256_text,
    unlink_path,
)
from .phase2_pack_shared.review_basis_parts import (
    review_allowed_abstractions,
    review_downstream_checklist,
    review_forbidden_weakenings,
    review_history_risks,
    review_route_inspection_gate,
    review_spine_contract,
)
from .phase2_semantic_review import (
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    _validate_review_input_internal_binding,
    latest_semantic_review_context_path,
    render_semantic_review_prompt,
)
from .phase2_output_binding import Phase2OutputBinding, resolve_phase2_output_binding
from .phase2_proof_obligations import (
    PROOF_OBLIGATIONS_FILE_NAME,
    load_existing_proof_obligations_file,
    maybe_ensure_proof_obligations_file,
    summarize_proof_obligations,
)

REQUIRED_REVIEW_EVIDENCE_CLASSES = [
    "source_tex",
    "lean_subject",
    "proof_obligations",
    "audit",
    "classification",
    "dependency_status",
    "downstream",
    "ledger_status",
    "hashes",
]

PLAN_ONLY_SOURCE_TASKS = {"thm_6_7__lemma_1"}


def _review_request_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{SEMANTIC_REVIEW_REQUEST_PREFIX}_v{attempt}.json"


def _latest_review_request_path(pack_dir: Path) -> Path:
    return pack_dir / SEMANTIC_REVIEW_REQUEST_ALIAS


def _resolve_review_binding_path(raw_path: str, *, pack_dir: Path) -> Path:
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = (pack_dir / path).resolve()
    return path


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
        if path_exists(alias):
            unlink_path(alias)
        copy_file(source, alias)


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


def _collect_direct_downstream_consumers(task_id: str, settings) -> list[dict[str, str]]:
    consumers: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    canonical_task_id = canonicalize_block_id(task_id)
    for plan_file in sorted(settings.plans_dir.glob("*_plan.json")):
        tasks = read_json_safely(plan_file, [])
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


def _hash_file(path: Path | None) -> str:
    if path is None or not path_exists(path):
        return ""
    text = read_file_safely(path)
    return sha256_text(text) if text else ""


def _subject_imports(subject_file: Path | None) -> list[str]:
    if subject_file is None or not path_exists(subject_file):
        return []
    imports: list[str] = []
    for line in read_file_safely(subject_file).splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped)
    return imports


def _latest_audit_evidence(pack_dir: Path) -> dict[str, Any]:
    latest_path: Path | None = None
    for path in sorted(pack_dir.glob("verify_result_v*.json")):
        payload = read_json_safely(path, {})
        if not isinstance(payload, dict):
            continue
        mode = str(payload.get("mode", "") or "").strip().lower()
        disposition = str(payload.get("disposition", "") or "").strip().lower()
        if mode == "audit" or disposition.startswith("audit_"):
            latest_path = path
    if latest_path is None:
        return {
            "latest_audit_result_file": "",
            "disposition": "",
            "success": None,
            "diagnostics": [],
        }
    payload = read_json_safely(latest_path, {})
    diagnostics = payload.get("diagnostics", []) if isinstance(payload, dict) else []
    return {
        "latest_audit_result_file": str(latest_path),
        "disposition": str(payload.get("disposition", "") or "") if isinstance(payload, dict) else "",
        "success": payload.get("success") if isinstance(payload, dict) else None,
        "diagnostics": diagnostics if isinstance(diagnostics, list) else [],
    }


def _classification_history(task_id: str, settings) -> dict[str, Any]:
    candidates = [
        settings.artifact_root / "docs" / "phase2_completion_classification.json",
        settings.runtime_root / "docs" / "phase2_completion_classification.json",
    ]
    seen: set[str] = set()
    for path in candidates:
        key = str(path.resolve())
        if key in seen:
            continue
        seen.add(key)
        if not path_exists(path):
            continue
        payload = read_json_safely(path, {})
        if not isinstance(payload, dict):
            continue
        tasks = payload.get("tasks", [])
        entries = [
            item
            for item in tasks
            if isinstance(item, dict) and canonicalize_block_id(str(item.get("task_id", "") or "")) == task_id
        ] if isinstance(tasks, list) else []
        return {
            "classification_file": str(path),
            "schema_version": payload.get("schema_version", ""),
            "entries": entries,
        }
    return {
        "classification_file": "",
        "schema_version": "",
        "entries": [],
    }


def _dependency_status(task: dict[str, Any], ledger: LedgerManager, settings) -> list[dict[str, Any]]:
    status: list[dict[str, Any]] = []
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    relation_by_id: dict[str, str] = {dep: "hard_dependency" for dep in hard_deps}
    for dep in soft_imports:
        relation_by_id.setdefault(dep, "soft_import")
    for dep_id in sorted(relation_by_id):
        record = ledger.ledger.get("tasks", {}).get(dep_id, {})
        record = record if isinstance(record, dict) else {}
        source_plan = str(record.get("source_plan", "unknown") or "unknown")
        output_path = find_existing_task_file(dep_id, source_plan, settings)
        output_exists = bool(output_path and path_exists(output_path))
        status.append(
            {
                "task_id": dep_id,
                "relation": relation_by_id[dep_id],
                "ledger_status": str(record.get("status", "") or ""),
                "source_plan": source_plan,
                "official_output_file": str(output_path or ""),
                "official_output_exists": output_exists,
                "official_output_hash": _hash_file(output_path) if output_path else "",
                "proof_obligation_summary": record.get("proof_obligation_summary", {}) if isinstance(record.get("proof_obligation_summary", {}), dict) else {},
                "latest_semantic_review_result_file": str(record.get("latest_semantic_review_result_file", "") or ""),
            }
        )
    return status


def _downstream_evidence(downstream: list[dict[str, str]], settings) -> dict[str, Any]:
    consumers: list[dict[str, Any]] = []
    for consumer in downstream:
        consumer_id = canonicalize_block_id(str(consumer.get("block_id", "") or ""))
        source_plan = str(consumer.get("source_plan", "unknown") or "unknown")
        output_path = find_existing_task_file(consumer_id, source_plan, settings)
        consumers.append(
            {
                **consumer,
                "official_output_file": str(output_path or ""),
                "official_output_exists": bool(output_path and path_exists(output_path)),
                "official_output_imports": _subject_imports(output_path) if output_path else [],
            }
        )
    return {
        "direct_downstream_consumers": consumers,
        "downstream_import_scan_required_before_quarantine": bool(consumers),
    }


def _ledger_status_evidence(
    *,
    task_id: str,
    output_owner_task_id: str,
    ledger: LedgerManager,
) -> dict[str, Any]:
    record = ledger.ledger.get("tasks", {}).get(task_id, {})
    record = record if isinstance(record, dict) else {}
    owner = ledger.ledger.get("tasks", {}).get(output_owner_task_id, {})
    owner = owner if isinstance(owner, dict) else {}
    return {
        "task_status": str(record.get("status", "") or ""),
        "output_owner_task_id": output_owner_task_id,
        "output_owner_status": str(owner.get("status", "") or ""),
        "latest_build_result_file": str(record.get("latest_build_result_file", "") or ""),
        "latest_build_ready_candidate_file": str(record.get("latest_build_ready_candidate_file", "") or ""),
        "latest_build_ready_candidate_hash": str(record.get("latest_build_ready_candidate_hash", "") or ""),
        # Do not include the latest review-result artifact here.  Creating a new
        # request refreshes that alias, so either its path or its presence would
        # make review-now invalidate the request it just generated.  Review
        # provenance is bound separately by the request/input/result hashes.
        "proof_obligation_summary": owner.get("proof_obligation_summary", {}) if isinstance(owner.get("proof_obligation_summary", {}), dict) else {},
    }


def _hash_evidence(
    *,
    task_id: str,
    source_plan: str,
    review_subject_hash: str,
    current_record: dict[str, Any],
    settings,
) -> dict[str, Any]:
    build_result_raw = str(current_record.get("latest_build_result_file", "") or "").strip()
    build_result_path = Path(build_result_raw) if build_result_raw else None
    if build_result_path is not None and not build_result_path.is_absolute():
        build_result_path = (settings.artifact_root / build_result_path).resolve()
    build_candidate_raw = str(current_record.get("latest_build_ready_candidate_file", "") or "").strip()
    build_candidate_path = Path(build_candidate_raw) if build_candidate_raw else None
    if build_candidate_path is not None and not build_candidate_path.is_absolute():
        build_candidate_path = (settings.artifact_root / build_candidate_path).resolve()
    official_output_path = select_latest_existing_task_file(task_id, source_plan, settings)
    return {
        "review_subject_hash": str(review_subject_hash or ""),
        "build_result_file": str(build_result_path or ""),
        "build_result_hash": _hash_file(build_result_path),
        "build_candidate_file": str(build_candidate_path or ""),
        "build_candidate_hash": str(current_record.get("latest_build_ready_candidate_hash", "") or ""),
        "build_candidate_file_hash": _hash_file(build_candidate_path),
        "official_output_file": str(official_output_path or ""),
        "official_output_hash": _hash_file(official_output_path),
    }


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
    return {
        "schema_version": "phase2.semantic_review.request.v1",
        "task_id": task_id,
        "origin": origin,
        "attempt": attempt,
        "review_subject_kind": review_subject_kind,
        "review_subject_file": review_subject_file,
        "review_subject_hash": review_subject_hash,
        "review_basis_hash": review_basis_hash,
        "review_input_hash": review_input_hash,
        "review_input_file": review_input_file,
        "review_prompt_file": review_prompt_file,
        "review_context_file": review_context_file,
        "review_result_template_file": review_result_template_file,
        "expected_result_file": expected_result_file,
        "reviewer_backend_id": reviewer_backend_id,
        "prompt_version": prompt_version,
        "rubric_version": rubric_version,
    }


def build_semantic_review_basis(
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    *,
    review_subject_kind: str,
    review_subject_hash: str = "",
    review_subject_file: str | Path | None = None,
    materialize_proof_obligations: bool = True,
) -> dict[str, Any]:
    task_id = task["block_id"]
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    output_binding = resolve_phase2_output_binding(task, ledger, settings)
    obligations_pack_dir = output_binding.owner_pack_dir if output_binding.is_obligation_task else pack_dir
    obligations_task = (
        _owner_task_for_review_basis(output_binding, task, ledger)
        if output_binding.is_obligation_task
        else task
    )
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    current_record = current_record if isinstance(current_record, dict) else {}
    obligations_record = (
        ledger.ledger.get("tasks", {}).get(output_binding.output_owner_task_id, {})
        if output_binding.is_obligation_task
        else current_record if isinstance(current_record, dict) else {}
    )
    if materialize_proof_obligations:
        proof_obligations = maybe_ensure_proof_obligations_file(
            obligations_pack_dir,
            obligations_task,
            current_record=obligations_record,
            tracking_level=2,
        )
    else:
        proof_obligations = load_existing_proof_obligations_file(obligations_pack_dir, obligations_task)
    if output_binding.is_obligation_task:
        proof_obligations_owner_file = output_binding.proof_obligations_file.as_posix()
    elif proof_obligations is not None:
        proof_obligations_owner_file = str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME)
    else:
        proof_obligations_owner_file = ""
    proof_obligations_file = (
        output_binding.proof_obligations_file.as_posix()
        if output_binding.is_obligation_task
        else str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME)
    ) if proof_obligations is not None else ""
    if output_binding.is_obligation_task:
        child_proof_obligations = load_existing_proof_obligations_file(pack_dir, task)
        if child_proof_obligations is not None:
            proof_obligations = child_proof_obligations
            proof_obligations_file = str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME)
    downstream = sorted(
        _collect_direct_downstream_consumers(output_binding.output_owner_task_id, settings),
        key=lambda item: (
            str(item.get("block_id", "")),
            str(item.get("relation", "")),
            str(item.get("source_plan", "")),
            str(item.get("type", "")),
            str(item.get("title", "")),
        ),
    )
    source_plan = str(task.get("source_plan", "") or "")
    source_tex_file = settings.runtime_root / "inputs" / f"{source_plan}.tex" if source_plan else None
    source_tex_exists = bool(source_tex_file is not None and path_exists(source_tex_file))
    source_tex_content = read_file_safely(source_tex_file) if source_tex_exists and source_tex_file is not None else ""
    source_kind = "plan_only" if task_id in PLAN_ONLY_SOURCE_TASKS and not source_tex_exists else "source_tex"
    if source_tex_exists:
        source_tex_status = "present"
    elif source_kind == "plan_only":
        source_tex_status = "not_applicable"
    else:
        source_tex_status = "missing_required"
    subject_file_path = Path(review_subject_file).expanduser() if review_subject_file else None
    if subject_file_path is not None and not subject_file_path.is_absolute():
        subject_file_path = (pack_dir / subject_file_path).resolve()
    proof_obligation_summary = summarize_proof_obligations(proof_obligations) if proof_obligations is not None else {}
    return {
        "task": {
            "block_id": task_id,
            "type": str(task.get("type", "") or ""),
            "title": str(task.get("title", "") or ""),
            "content": str(task.get("content", "") or ""),
            "source_plan": str(task.get("source_plan", "") or ""),
            "dependencies": canonicalize_id_list(task.get("dependencies", [])),
            "soft_imports": canonicalize_id_list(task.get("soft_imports", [])),
            "soft_imports_confirmed_at": str(
                task.get("soft_imports_confirmed_at", "")
                or current_record.get("soft_imports_confirmed_at", "")
                or ""
            ),
        },
        "review_subject_kind": str(review_subject_kind or ""),
        "review_subject_hash": str(review_subject_hash or ""),
        "output_owner_task_id": output_binding.output_owner_task_id,
        "output_module": output_binding.output_module,
        "focus_obligation_ids": output_binding.focus_obligation_ids,
        "required_evidence_classes": REQUIRED_REVIEW_EVIDENCE_CLASSES,
        "source_evidence": {
            "task_id": task_id,
            "source_plan": source_plan,
            "source_kind": source_kind,
            "tex_file": str(source_tex_file) if source_tex_file is not None else "",
            "tex_exists": source_tex_exists,
            "tex_status": source_tex_status,
            "tex_hash": sha256_text(source_tex_content) if source_tex_exists else "",
            "task_content_hash": sha256_text(str(task.get("content", "") or "")),
        },
        "lean_subject_evidence": {
            "review_subject_kind": str(review_subject_kind or ""),
            "review_subject_hash": str(review_subject_hash or ""),
            "subject_imports": _subject_imports(subject_file_path),
        },
        "direct_downstream_consumers": downstream,
        "route_inspection_gate": review_route_inspection_gate(task),
        "spine_review_contract": review_spine_contract(task),
        "proof_obligations_file": proof_obligations_file,
        "proof_obligations_owner_file": proof_obligations_owner_file,
        "proof_obligations": proof_obligations if proof_obligations is not None else {},
        "proof_obligation_summary": proof_obligation_summary,
        "proof_obligations_evidence": {
            "proof_obligations_file": proof_obligations_file,
            "proof_obligations_owner_file": proof_obligations_owner_file,
            "proof_obligations": proof_obligations if proof_obligations is not None else {},
            "proof_obligation_summary": proof_obligation_summary,
            "authority": "review_evidence_only",
        },
        "audit_evidence": _latest_audit_evidence(pack_dir),
        "classification_history": _classification_history(output_binding.output_owner_task_id, settings),
        "dependency_status": _dependency_status(task, ledger, settings),
        "downstream_evidence": _downstream_evidence(downstream, settings),
        "ledger_status": _ledger_status_evidence(
            task_id=task_id,
            output_owner_task_id=output_binding.output_owner_task_id,
            ledger=ledger,
        ),
        "hash_evidence": _hash_evidence(
            task_id=output_binding.output_owner_task_id,
            source_plan=source_plan,
            review_subject_hash=review_subject_hash,
            current_record=current_record,
            settings=settings,
        ),
        "subject_imports": _subject_imports(subject_file_path),
        "allowed_abstractions": review_allowed_abstractions(task),
        "forbidden_weakenings": review_forbidden_weakenings(task),
        "historical_shortcut_risks": review_history_risks(task_id),
        "downstream_acceptance_checklist": review_downstream_checklist(task_id),
    }


def _owner_task_for_review_basis(
    output_binding: Phase2OutputBinding,
    task: dict[str, Any],
    ledger: LedgerManager,
) -> dict[str, Any]:
    owner = ledger.ledger.get("tasks", {}).get(output_binding.output_owner_task_id)
    if isinstance(owner, dict):
        return canonicalize_task_dict(owner)
    fallback = dict(task)
    fallback["block_id"] = output_binding.output_owner_task_id
    return canonicalize_task_dict(fallback)


def _resolve_current_review_request_path(pack_dir: Path, current_record: dict[str, Any]) -> Path | None:
    raw_request = str(current_record.get("current_review_request_file", "") or "").strip()
    if raw_request:
        request_path = _resolve_review_binding_path(raw_request, pack_dir=pack_dir)
        if path_exists(request_path):
            return request_path
    latest_request = _latest_review_request_path(pack_dir)
    if path_exists(latest_request):
        return latest_request
    return None


def _review_version_matches(value: Any, expected: int) -> bool:
    if isinstance(value, bool):
        return False
    try:
        return int(value) == expected
    except (TypeError, ValueError):
        return False


def _validate_review_input_freshness(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    review_input: dict[str, Any],
    allow_promoted_candidate: bool = False,
) -> tuple[str, dict[str, Any]]:
    task_id = task["block_id"]
    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    if not isinstance(review_input, dict):
        return "review input must be a JSON object", {}
    task_payload = review_input.get("task", {})
    candidate_payload = review_input.get("candidate", {})
    if not isinstance(task_payload, dict):
        return "review input task must be a JSON object", {}
    if not isinstance(candidate_payload, dict):
        return "review input candidate must be a JSON object", {}
    attempt_value = review_input.get("attempt")
    if isinstance(attempt_value, bool):
        return "review input attempt must be a positive integer", {}
    try:
        attempt = int(attempt_value)
        if attempt <= 0:
            return "review input attempt must be a positive integer", {}
    except (TypeError, ValueError):
        return "review input attempt must be a positive integer", {}
    review_subject_kind = str(review_input.get("review_subject_kind", "") or "candidate")
    if review_subject_kind not in {"candidate", "official_output", "existing_support"}:
        return "review input review_subject_kind is invalid", {}
    if canonicalize_block_id(str(task_payload.get("block_id", "") or "")) != task_id:
        return f"review input task id mismatch: expected {task_id}", {}
    if not _review_version_matches(review_input.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
        return "review input prompt_version does not match current semantic review prompt version", {}
    if not _review_version_matches(review_input.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
        return "review input rubric_version does not match current semantic review rubric version", {}
    input_binding_error = _validate_review_input_internal_binding(review_input)
    if input_binding_error:
        return input_binding_error, {}

    request_path = _review_request_path(pack_dir, attempt)
    request_payload = read_json_safely(request_path, {}) if path_exists(request_path) else {}
    if not isinstance(request_payload, dict):
        return "bound semantic review request is missing or invalid", {}
    expected_review_input_hash = str(request_payload.get("review_input_hash", "") or "")
    if not expected_review_input_hash or expected_review_input_hash != sha256_json(review_input):
        return "semantic review input hash no longer matches the bound review request", {}
    if canonicalize_block_id(str(request_payload.get("task_id", "") or "")) != task_id:
        return "bound semantic review request task id does not match review input", {}
    if not _review_version_matches(request_payload.get("attempt"), attempt):
        return "bound semantic review request attempt does not match review input", {}
    request_bindings = {
        "review_subject_kind": review_subject_kind,
        "review_subject_file": str(review_input.get("review_subject_file", "") or ""),
        "review_subject_hash": str(review_input.get("review_subject_hash", "") or ""),
        "review_basis_hash": str(review_input.get("review_basis_hash", "") or ""),
    }
    for field, expected_value in request_bindings.items():
        if str(request_payload.get(field, "") or "") != expected_value:
            return f"bound semantic review request {field} does not match review input", {}

    bound_input_file = _resolve_review_binding_path(str(request_payload.get("review_input_file", "") or ""), pack_dir=pack_dir)
    bound_input_payload = read_json_safely(bound_input_file, {}) if path_exists(bound_input_file) else {}
    if not isinstance(bound_input_payload, dict) or sha256_json(bound_input_payload) != expected_review_input_hash:
        return "bound semantic review input file is missing or changed", {}

    prompt_file_raw = str(request_payload.get("review_prompt_file", "") or "").strip()
    if not prompt_file_raw:
        return "bound semantic review prompt file is missing", {}
    prompt_file_path = _resolve_review_binding_path(prompt_file_raw, pack_dir=pack_dir)
    if not path_exists(prompt_file_path):
        return "bound semantic review prompt file is missing", {}
    if read_file_safely(prompt_file_path).strip() != render_semantic_review_prompt(review_input).strip():
        return "semantic review prompt no longer matches the bound review input", {}

    subject_file_raw = str(review_input.get("review_subject_file", "") or candidate_payload.get("file", "") or "").strip()
    if not subject_file_raw:
        return "review input review_subject_file is missing", {}
    subject_file_path = _resolve_review_binding_path(subject_file_raw, pack_dir=pack_dir)
    if not path_exists(subject_file_path):
        return "review subject file is missing; regenerate semantic review materials", {}

    context_file_raw = str(review_input.get("review_context_file", "") or "").strip()
    if not context_file_raw:
        return "review input review_context_file is missing", {}
    context_file_path = _resolve_review_binding_path(context_file_raw, pack_dir=pack_dir)
    if not path_exists(context_file_path):
        return "review context file is missing; regenerate semantic review materials", {}
    context_file_text = read_file_safely(context_file_path)
    context_markdown = str(review_input.get("review_context_markdown", "") or "")
    if context_file_text.strip() != context_markdown.strip():
        return "review context file no longer matches review_context_markdown", {}

    candidate_code = read_file_safely(subject_file_path)
    recorded_subject_hash = str(review_input.get("review_subject_hash", "") or candidate_payload.get("hash", "") or "")
    if not recorded_subject_hash:
        return "review input review_subject_hash is missing; regenerate semantic review materials", {}
    current_review_subject_hash = sha256_text(candidate_code) if candidate_code else ""
    if current_review_subject_hash != recorded_subject_hash:
        return "review subject snapshot hash changed since review-pack generation", {}
    if review_subject_kind == "candidate":
        if allow_promoted_candidate:
            current_output = select_latest_existing_task_file(task_id, source_plan, settings)
            current_output_code = read_file_safely(current_output) if current_output and path_exists(current_output) else ""
            if not current_output_code:
                return "canonical official output is missing for promoted review replay", {}
            if sha256_text(current_output_code) != recorded_subject_hash:
                return "canonical official output no longer matches the promoted review subject", {}
        else:
            latest_ready_hash = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("latest_build_ready_candidate_hash", "") or "")
            if current_review_subject_hash != latest_ready_hash:
                return "candidate hash changed since build-check generation", {}
            stale_official_message = stale_candidate_official_output_message(
                task_id=task_id,
                source_plan=source_plan,
                settings=settings,
                candidate_path=subject_file_path,
                candidate_hash=current_review_subject_hash,
                draft_path=pack_dir / DRAFT_FILE_NAME,
                action="current candidate review request",
            )
            if stale_official_message:
                return stale_official_message, {}
    elif review_subject_kind == "official_output":
        current_output = select_latest_existing_task_file(task_id, source_plan, settings)
        current_output_code = read_file_safely(current_output) if current_output and path_exists(current_output) else ""
        current_output_hash = sha256_text(current_output_code) if current_output_code else ""
        if current_output_hash != recorded_subject_hash:
            return "official output changed since review-existing generation", {}

    expected_review_basis_hash = str(review_input.get("review_basis_hash", "") or "")
    if not expected_review_basis_hash:
        return "review input review_basis_hash is missing; regenerate semantic review materials", {}
    current_review_basis = build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind=review_subject_kind,
        review_subject_hash=current_review_subject_hash,
        review_subject_file=subject_file_path,
        materialize_proof_obligations=False,
    )
    recorded_review_basis = review_input.get("review_basis", {})
    if not isinstance(recorded_review_basis, dict) or sha256_json(recorded_review_basis) != expected_review_basis_hash:
        return "recorded semantic review basis does not match its bound hash", {}
    if allow_promoted_candidate:
        current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        current_record = current_record if isinstance(current_record, dict) else {}
        receipt_subject_hash = str(current_record.get("latest_applied_review_subject_hash", "") or "")
        receipt_origin_basis_hash = str(current_record.get("latest_applied_review_origin_basis_hash", "") or "")
        receipt_post_basis_hash = str(current_record.get("latest_applied_review_post_basis_hash", "") or "")
        if (
            receipt_subject_hash != recorded_subject_hash
            or receipt_origin_basis_hash != expected_review_basis_hash
            or not receipt_post_basis_hash
        ):
            return "promoted review replay receipt is missing or does not match this review input", {}
        basis_matches = sha256_json(current_review_basis) == receipt_post_basis_hash
    else:
        basis_matches = sha256_json(current_review_basis) == expected_review_basis_hash
    if not basis_matches:
        return "semantic review basis changed since review generation", {}
    return "", {
        "review_subject_kind": review_subject_kind,
        "subject_file_path": subject_file_path,
        "candidate_code": candidate_code,
        "current_review_subject_hash": current_review_subject_hash,
        "expected_review_basis_hash": expected_review_basis_hash,
    }


def _load_current_codex_review_request(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
) -> tuple[str, dict[str, Any]]:
    current_record = ledger.ledger.get("tasks", {}).get(task["block_id"], {})
    request_path = _resolve_current_review_request_path(pack_dir, current_record if isinstance(current_record, dict) else {})
    if request_path is None:
        return (
            "No current codex review request is available; prepare one with "
            "`review-now --review-subject candidate` for a build-ready candidate or "
            "`review-now --review-subject existing` for an official output."
        ), {}
    request_payload = read_json_safely(request_path, {})
    if not isinstance(request_payload, dict):
        return "Current codex review request is invalid JSON; regenerate semantic review materials.", {}
    required_fields = {
        "task_id",
        "review_subject_kind",
        "review_subject_file",
        "review_subject_hash",
        "review_basis_hash",
        "review_input_file",
        "review_prompt_file",
        "review_context_file",
        "review_result_template_file",
        "expected_result_file",
        "review_input_hash",
        "reviewer_backend_id",
        "prompt_version",
        "rubric_version",
    }
    missing = sorted(field for field in required_fields if not str(request_payload.get(field, "") or "").strip())
    if missing:
        return f"Current codex review request is missing required fields: {', '.join(missing)}", {}
    if canonicalize_block_id(str(request_payload.get("task_id", "") or "")) != task["block_id"]:
        return f"Current codex review request task id mismatch: expected {task['block_id']}", {}
    if str(request_payload.get("reviewer_backend_id", "") or "") != "codex-handoff":
        return "Current codex review request is not for the codex-handoff backend.", {}
    if not _review_version_matches(request_payload.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
        return "Current codex review request prompt_version does not match the current semantic review prompt version.", {}
    if not _review_version_matches(request_payload.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
        return "Current codex review request rubric_version does not match the current semantic review rubric version.", {}

    input_path = _resolve_review_binding_path(str(request_payload.get("review_input_file", "")), pack_dir=pack_dir)
    prompt_path = _resolve_review_binding_path(str(request_payload.get("review_prompt_file", "")), pack_dir=pack_dir)
    context_path = _resolve_review_binding_path(str(request_payload.get("review_context_file", "")), pack_dir=pack_dir)
    template_path = _resolve_review_binding_path(str(request_payload.get("review_result_template_file", "")), pack_dir=pack_dir)
    subject_file_path = _resolve_review_binding_path(str(request_payload.get("review_subject_file", "")), pack_dir=pack_dir)
    expected_result_path = _resolve_review_binding_path(str(request_payload.get("expected_result_file", "")), pack_dir=pack_dir)
    for path, label in (
        (input_path, "review input"),
        (prompt_path, "review prompt"),
        (context_path, "review context"),
        (template_path, "review template"),
        (subject_file_path, "review subject file"),
    ):
        if not path_exists(path):
            return f"Current codex review request {label} is missing; regenerate semantic review materials.", {}

    review_input = read_json_safely(input_path, {})
    if not isinstance(review_input, dict):
        return "Current codex review input JSON is invalid; regenerate semantic review materials.", {}
    if str(request_payload.get("review_input_hash", "") or "") != sha256_json(review_input):
        return "Current codex review request input hash does not match the bound review input.", {}
    if str(request_payload.get("review_subject_kind", "") or "") != str(review_input.get("review_subject_kind", "") or ""):
        return "Current codex review request subject kind does not match the bound review input.", {}
    current_subject_kind = str(current_record.get("current_review_subject_kind", "") or "")
    if current_subject_kind and str(request_payload.get("review_subject_kind", "") or "") != current_subject_kind:
        return "Current codex review request subject kind no longer matches the current review state.", {}
    request_subject_hash = str(request_payload.get("review_subject_hash", "") or "")
    input_candidate = review_input.get("candidate", {}) if isinstance(review_input.get("candidate", {}), dict) else {}
    input_subject_hash = str(review_input.get("review_subject_hash", "") or input_candidate.get("hash", "") or "")
    if request_subject_hash != input_subject_hash:
        return "Current codex review request subject hash does not match the bound review input.", {}
    if str(request_payload.get("review_basis_hash", "") or "") != str(review_input.get("review_basis_hash", "") or ""):
        return "Current codex review request basis hash does not match the bound review input.", {}

    freshness_error, freshness = _validate_review_input_freshness(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        review_input=review_input,
    )
    if freshness_error:
        return freshness_error, {}

    return "", {
        "request_path": request_path,
        "request_payload": request_payload,
        "review_input": review_input,
        "prompt_path": prompt_path,
        "context_path": context_path,
        "template_path": template_path,
        "expected_result_path": expected_result_path,
        "result_exists": path_exists(expected_result_path),
        **freshness,
    }
