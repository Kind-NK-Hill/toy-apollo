from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, canonicalize_task_dict
from src.ledger_manager import LedgerManager, TaskStatus

from .phase2_failure_budget import PHASE2_FAILURE_STREAK_LIMIT
from .phase2_pack_shared.io import read_json_safely, write_json
from .phase2_proof_obligations import (
    normalize_proof_obligations,
    needs_concrete_decomposition,
    placeholder_obligation_ids,
    proof_obligation_path,
    proof_contract_is_verified,
    summarize_proof_obligations,
)


OBLIGATION_TASK_TYPE = "Phase2ObligationTask"
OBLIGATION_TASK_ID_PREFIX = "obl"
OBLIGATION_TASK_PROMOTABLE_STATUSES = {"accepted_as_proof_debt", "open", "partial", "blocked", "in_progress"}
MAX_OBLIGATION_TASK_ID_LENGTH = 120


@dataclass(frozen=True)
class ObligationPromotionReport:
    parent_task_id: str
    created: list[str] = field(default_factory=list)
    updated: list[str] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)


def obligation_task_id(parent_task_id: str, obligation_id: str) -> str:
    parent = canonicalize_block_id(parent_task_id)
    raw_obligation = re.sub(r"[^A-Za-z0-9_]+", "_", str(obligation_id or "")).strip("_").lower()
    raw_obligation = re.sub(r"_+", "_", raw_obligation) or "obligation"
    full_id = canonicalize_block_id(f"{OBLIGATION_TASK_ID_PREFIX}_{parent}_{raw_obligation}")
    if len(full_id) <= MAX_OBLIGATION_TASK_ID_LENGTH:
        return full_id
    digest = hashlib.sha1(f"{parent}:{raw_obligation}".encode("utf-8")).hexdigest()[:12]
    parent_budget = 42
    obligation_budget = MAX_OBLIGATION_TASK_ID_LENGTH - len(OBLIGATION_TASK_ID_PREFIX) - len(digest) - 3 - parent_budget
    parent_part = parent[:parent_budget].strip("_") or "parent"
    obligation_part = raw_obligation[:max(obligation_budget, 16)].strip("_") or "obligation"
    return canonicalize_block_id(f"{OBLIGATION_TASK_ID_PREFIX}_{parent_part}_{obligation_part}_{digest}")


def is_obligation_task(task: dict[str, Any] | None) -> bool:
    return isinstance(task, dict) and str(task.get("type", "") or "") == OBLIGATION_TASK_TYPE


def promote_obligation_tasks_for_task(
    parent_task_id: str,
    ledger: LedgerManager,
    settings,
) -> ObligationPromotionReport:
    parent_task_id = canonicalize_block_id(parent_task_id)
    # Legacy quarantine: `obl` is no longer a task factory or public import
    # surface. Keep the old implementation below unreachable until historical
    # reconciliation code is deleted; new work must absorb obligations into the
    # parent file or stable non-`obl` support and pass normal parent review/apply.
    return ObligationPromotionReport(
        parent_task_id=parent_task_id,
        skipped=["obligation child promotion is disabled; absorb proof obligations into parent/support files"],
    )
    parent_task = _resolve_parent_task(parent_task_id, ledger, settings)
    parent_task = _with_runtime_soft_imports(parent_task_id, parent_task, ledger)
    pack_dir = settings.phase2_prompt_packs_dir / parent_task_id
    obligations_path = proof_obligation_path(pack_dir)
    payload = _load_obligations_payload(obligations_path, parent_task)

    parent_deps = canonicalize_id_list(parent_task.get("dependencies", []))
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    promotable_ids = {
        str(item.get("id", "") or "")
        for item in obligations
        if isinstance(item, dict) and _is_promotable_obligation(item)
    }

    created: list[str] = []
    updated: list[str] = []
    skipped: list[str] = []
    changed = False
    for obligation in obligations:
        if not isinstance(obligation, dict):
            continue
        obligation_id = str(obligation.get("id", "") or "").strip()
        if not obligation_id or not _is_promotable_obligation(obligation):
            if obligation_id:
                skipped.append(obligation_id)
            continue
        previous_child_id = canonicalize_block_id(str(obligation.get("ledger_task_id", "") or ""))
        child_id = obligation_task_id(parent_task_id, obligation_id)
        existed = child_id in ledger.ledger.get("tasks", {})
        child_deps = _child_dependencies(parent_deps, parent_task_id, obligation, promotable_ids)
        child_task = _build_child_task(
            child_id=child_id,
            parent_task=parent_task,
            obligation=obligation,
            dependencies=child_deps,
            settings=settings,
        )
        ledger.add_or_update_task(child_task)
        _update_child_metadata(
            child_id=child_id,
            parent_task_id=parent_task_id,
            parent_task=parent_task,
            obligation=obligation,
            dependencies=child_deps,
            content=str(child_task.get("content", "") or ""),
            target_file=_target_file_for_parent(parent_task_id, settings),
            ledger=ledger,
        )
        if existed:
            updated.append(child_id)
        else:
            created.append(child_id)

        if previous_child_id and previous_child_id != child_id:
            _mark_superseded_child_obligation(
                previous_child_id=previous_child_id,
                child_id=child_id,
                parent_task_id=parent_task_id,
                obligation_id=obligation_id,
                ledger=ledger,
            )
        if obligation.get("ledger_task_id") != child_id:
            obligation["ledger_task_id"] = child_id
            changed = True
        fingerprint = _obligation_fingerprint(parent_task_id, obligation)
        if obligation.get("obligation_fingerprint") != fingerprint:
            obligation["obligation_fingerprint"] = fingerprint
            changed = True

    if changed:
        write_json(obligations_path, payload)
    _update_parent_obligation_summary(parent_task_id, ledger, obligations_path, payload)
    return ObligationPromotionReport(parent_task_id=parent_task_id, created=created, updated=updated, skipped=skipped)


def _mark_superseded_child_obligation(
    *,
    previous_child_id: str,
    child_id: str,
    parent_task_id: str,
    obligation_id: str,
    ledger: LedgerManager,
) -> None:
    previous = ledger.ledger.get("tasks", {}).get(previous_child_id)
    if not isinstance(previous, dict):
        return
    if str(previous.get("parent_task_id", "") or "") != parent_task_id:
        return
    if str(previous.get("obligation_id", "") or "") != obligation_id:
        return
    ledger.update_status(
        previous_child_id,
        TaskStatus.ORPHANED,
        error=f"Superseded by shortened obligation child id {child_id}.",
    )
    ledger.update_runtime_metadata(
        previous_child_id,
        superseded_by_obligation_task_id=child_id,
        obligation_task_state="superseded_by_short_id",
    )


def promote_all_obligation_tasks(
    ledger: LedgerManager,
    settings,
    task_ids: list[str] | tuple[str, ...] | None = None,
) -> dict[str, list[str] | int]:
    if task_ids:
        parent_ids = canonicalize_id_list(task_ids)
    else:
        parent_ids = [
            canonicalize_block_id(path.parent.name)
            for path in sorted(settings.phase2_prompt_packs_dir.glob("*/proof_obligations.json"))
            if not canonicalize_block_id(path.parent.name).startswith(f"{OBLIGATION_TASK_ID_PREFIX}_")
        ]
        parent_ids = canonicalize_id_list(parent_ids)

    created: list[str] = []
    updated: list[str] = []
    skipped: list[str] = [
        f"{parent_id}:obligation child promotion is disabled; absorb proof obligations into parent/support files"
        for parent_id in parent_ids
    ]
    parents_scanned: list[str] = list(parent_ids)
    return {
        "parents_scanned": parents_scanned,
        "created": created,
        "updated": updated,
        "skipped": skipped,
        "created_count": len(created),
        "updated_count": len(updated),
    }


def reconcile_obligation_tasks_for_task(parent_task_id: str, ledger: LedgerManager, settings) -> dict[str, list[str]]:
    parent_task_id = canonicalize_block_id(parent_task_id)
    parent_task = _resolve_parent_task(parent_task_id, ledger, settings)
    pack_dir = settings.phase2_prompt_packs_dir / parent_task_id
    obligations_path = proof_obligation_path(pack_dir)
    payload = _load_obligations_payload(obligations_path, parent_task)

    proved: list[str] = []
    open_children: list[str] = []
    changed = False
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    for obligation in obligations:
        if not isinstance(obligation, dict):
            continue
        obligation_id = str(obligation.get("id", "") or "").strip()
        child_id = canonicalize_block_id(str(obligation.get("ledger_task_id", "") or ""))
        if not child_id and obligation_id:
            child_id = obligation_task_id(parent_task_id, obligation_id)
        child = ledger.ledger.get("tasks", {}).get(child_id)
        if not isinstance(child, dict) or not is_obligation_task(child):
            continue
        child_status = str(child.get("status", "") or "")
        if child_status == TaskStatus.COMPLETED.value:
            child_obligations_path = proof_obligation_path(settings.phase2_prompt_packs_dir / child_id)
            existing_child_payload = _load_existing_child_obligation_payload(child_obligations_path, child)
            child_payload = existing_child_payload or _child_completed_obligation_payload(
                child_id=child_id,
                parent_task_id=parent_task_id,
                obligation=obligation,
            )
            child_discharge = _child_concrete_discharge_obligation(child_payload, obligation)
            if existing_child_payload is None and child_obligations_path.parent.exists():
                write_json(child_obligations_path, child_payload)
            if child_discharge is None:
                open_children.append(child_id)
                ledger.update_runtime_metadata(
                    child_id,
                    obligation_task_state="needs_concrete_obligations",
                    reconciled_parent_task_id=parent_task_id,
                    proof_obligations_file=str(child_obligations_path),
                    proof_obligation_summary=summarize_proof_obligations(child_payload),
                )
                continue

            proved.append(child_id)
            changed = _absorb_child_discharge_into_parent_obligation(
                obligation=obligation,
                child_obligation=child_discharge,
                child_id=child_id,
            ) or changed
            ledger.update_runtime_metadata(
                child_id,
                obligation_task_state="closed",
                reconciled_parent_task_id=parent_task_id,
                proof_obligations_file=str(child_obligations_path),
                proof_obligation_summary=summarize_proof_obligations(child_payload),
            )
        else:
            open_children.append(child_id)

    if changed:
        write_json(obligations_path, payload)
    summary = _update_parent_obligation_summary(parent_task_id, ledger, obligations_path, payload)
    return {"proved": proved, "open": open_children}


def _resolve_parent_task(parent_task_id: str, ledger: LedgerManager, settings) -> dict[str, Any]:
    record = ledger.ledger.get("tasks", {}).get(parent_task_id)
    if isinstance(record, dict) and str(record.get("content", "") or "").strip():
        return canonicalize_task_dict(record)

    from .phase2_prompt_pack import find_task_in_plans

    plan_task = find_task_in_plans(parent_task_id, settings.plans_dir)
    if plan_task is not None:
        return canonicalize_task_dict(plan_task)
    raise FileNotFoundError(f"Phase 2 parent task {parent_task_id} could not be recovered for obligation promotion.")


def _with_runtime_soft_imports(
    parent_task_id: str,
    parent_task: dict[str, Any],
    ledger: LedgerManager,
) -> dict[str, Any]:
    plan_soft_imports = _parent_soft_imports(parent_task)
    record = ledger.ledger.get("tasks", {}).get(parent_task_id)
    if not isinstance(record, dict):
        return parent_task
    runtime_soft_imports = _parent_soft_imports(record)
    soft_imports = canonicalize_id_list([*plan_soft_imports, *runtime_soft_imports])
    if soft_imports == plan_soft_imports:
        return parent_task
    merged = dict(parent_task)
    merged["soft_imports"] = soft_imports
    return merged


def _load_obligations_payload(path: Path, parent_task: dict[str, Any]) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"proof_obligations.json does not exist for {parent_task.get('block_id')}: {path}")
    payload = normalize_proof_obligations(read_json_safely(path, {}), parent_task)
    path.parent.mkdir(parents=True, exist_ok=True)
    write_json(path, payload)
    return payload


def _is_promotable_obligation(obligation: dict[str, Any]) -> bool:
    if not bool(obligation.get("blocking", True)):
        return False
    status = str(obligation.get("status", "") or "open").strip()
    return status in OBLIGATION_TASK_PROMOTABLE_STATUSES


def _child_dependencies(
    parent_deps: list[str],
    parent_task_id: str,
    obligation: dict[str, Any],
    promotable_ids: set[str],
) -> list[str]:
    deps = list(parent_deps)
    for local_dep in obligation.get("depends_on", []) if isinstance(obligation.get("depends_on", []), list) else []:
        local_dep_id = str(local_dep or "").strip()
        if local_dep_id and local_dep_id in promotable_ids and local_dep_id != str(obligation.get("id", "") or ""):
            deps.append(obligation_task_id(parent_task_id, local_dep_id))
    return canonicalize_id_list(deps)


def _build_child_task(
    *,
    child_id: str,
    parent_task: dict[str, Any],
    obligation: dict[str, Any],
    dependencies: list[str],
    settings,
) -> dict[str, Any]:
    parent_task_id = canonicalize_block_id(str(parent_task.get("block_id", "") or ""))
    title = str(obligation.get("title", "") or obligation.get("id", "") or "Proof obligation")
    content = _render_child_content(parent_task, obligation, settings)
    return {
        "block_id": child_id,
        "type": OBLIGATION_TASK_TYPE,
        "title": f"{parent_task_id}: {title}",
        "content": content,
        "source_plan": str(parent_task.get("source_plan", "unknown") or "unknown"),
        "dependencies": dependencies,
        "soft_imports": _parent_soft_imports(parent_task),
    }


def _parent_soft_imports(parent_task: dict[str, Any]) -> list[str]:
    soft_imports = parent_task.get("soft_imports", [])
    if not soft_imports and isinstance(parent_task.get("candidate_snapshot"), dict):
        soft_imports = parent_task["candidate_snapshot"].get("soft_imports", [])
    return canonicalize_id_list(soft_imports)


def _render_child_content(parent_task: dict[str, Any], obligation: dict[str, Any], settings) -> str:
    parent_task_id = canonicalize_block_id(str(parent_task.get("block_id", "") or ""))
    lines = [
        f"Resolve proof obligation `{obligation.get('id', '')}` for parent task `{parent_task_id}`.",
        "",
        "Parent task:",
        f"- Type: {parent_task.get('type', 'Unknown')}",
        f"- Title: {parent_task.get('title', parent_task_id)}",
        f"- Target module: ToyApollo.Output.{parent_task_id}",
        f"- Target file: {_target_file_for_parent(parent_task_id, settings).as_posix()}",
        "",
        "Obligation:",
        f"- Kind: {obligation.get('kind', 'source_step')}",
        f"- Status at promotion: {obligation.get('status', 'open')}",
        f"- Source ref: {obligation.get('source_ref', '') or '(not recorded)'}",
        f"- Lean landing: {obligation.get('lean_landing', '') or '(not assigned)'}",
        f"- Depends on: {', '.join(str(dep) for dep in obligation.get('depends_on', []) if str(dep).strip()) or '(none)'}",
        f"- Notes: {obligation.get('notes', '') or '(none)'}",
        "",
        "Working rule:",
        "- Treat this like a normal Phase2 task: produce local theorem-level evidence, build it, request semantic review, and do not accept equivalent support-field assumptions as proof.",
        "- Use the textbook proof, older ToyApollo/Output files, and local interface-translation/support declarations before adding new infrastructure.",
    ]
    alignment = obligation.get("source_output_alignment", {})
    if isinstance(alignment, dict) and alignment:
        lines.extend(
            [
                "",
                "Source-output alignment:",
                f"- Audit class: {alignment.get('audit_class', '') or 'unclassified'}",
                f"- Family: {alignment.get('family', '') or 'unclassified'}",
                f"- Next action: {alignment.get('next_action', '') or '(none)'}",
            ]
        )
        missing = alignment.get("missing_landing_names", [])
        if isinstance(missing, list) and missing:
            lines.append("- Missing landing names: " + ", ".join(str(item) for item in missing if str(item).strip()))
        existing = alignment.get("existing_local_declarations", [])
        if isinstance(existing, list) and existing:
            lines.append("- Existing local declarations:")
            for decl in existing:
                if isinstance(decl, dict):
                    name = str(decl.get("name", "") or "")
                    file = str(decl.get("file", "") or "")
                    line = str(decl.get("line", "") or "")
                    if name:
                        location = f"{file}:{line}" if file and line else file
                        lines.append(f"  - {name}{f' ({location})' if location else ''}")
    scaffolds = obligation.get("scaffold_hypotheses", [])
    if isinstance(scaffolds, list) and scaffolds:
        lines.extend(["", "Scaffold hypotheses to eliminate:"])
        for scaffold in scaffolds:
            if isinstance(scaffold, dict):
                lines.append(
                    f"- {scaffold.get('name', '')}: {scaffold.get('category', '')}; "
                    f"{scaffold.get('discharge_plan', '')}"
                )
    return "\n".join(lines).rstrip() + "\n"


def _update_child_metadata(
    *,
    child_id: str,
    parent_task_id: str,
    parent_task: dict[str, Any],
    obligation: dict[str, Any],
    dependencies: list[str],
    content: str,
    target_file: Path,
    ledger: LedgerManager,
) -> None:
    current = ledger.ledger.get("tasks", {}).get(child_id, {})
    updates: dict[str, Any] = {
        "parent_block_id": parent_task_id,
        "parent_task_id": parent_task_id,
        "content": content,
        "target_task_id": parent_task_id,
        "target_file": target_file.as_posix(),
        "target_module": f"ToyApollo.Output.{parent_task_id}",
        "dependencies": canonicalize_id_list(dependencies),
        "obligation_id": str(obligation.get("id", "") or ""),
        "obligation_kind": str(obligation.get("kind", "") or "source_step"),
        "obligation_status_at_promotion": str(obligation.get("status", "") or "open"),
        "obligation_source_ref": str(obligation.get("source_ref", "") or ""),
        "obligation_lean_landing": str(obligation.get("lean_landing", "") or ""),
        "obligation_fingerprint": _obligation_fingerprint(parent_task_id, obligation),
        "decomposition_revision": _decomposition_revision(parent_task_id, obligation),
        "origin_proof_obligations_file": str(proof_obligation_path(Path("phase2_prompt_packs") / parent_task_id)),
        "phase2_failure_streak_limit": PHASE2_FAILURE_STREAK_LIMIT,
        "obligation_task_state": str(current.get("obligation_task_state", "") or "open"),
    }
    if "phase2_build_fail_counter" not in current:
        updates["phase2_build_fail_counter"] = 0
    if "phase2_review_fail_counter" not in current:
        updates["phase2_review_fail_counter"] = 0
    ledger.update_runtime_metadata(child_id, **updates)


def _target_file_for_parent(parent_task_id: str, settings) -> Path:
    return settings.toyapollo_output_dir / f"{parent_task_id}.lean"


def _obligation_fingerprint(parent_task_id: str, obligation: dict[str, Any]) -> str:
    payload = {
        "parent_task_id": parent_task_id,
        "id": obligation.get("id", ""),
        "kind": obligation.get("kind", ""),
        "source_ref": obligation.get("source_ref", ""),
        "lean_landing": obligation.get("lean_landing", ""),
        "notes": obligation.get("notes", ""),
        "depends_on": obligation.get("depends_on", []),
        "scaffold_hypotheses": obligation.get("scaffold_hypotheses", []),
        "source_output_alignment": obligation.get("source_output_alignment", {}),
    }
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _decomposition_revision(parent_task_id: str, obligation: dict[str, Any]) -> str:
    raw = json.dumps(
        {
            "parent_task_id": parent_task_id,
            "obligation_id": obligation.get("id", ""),
            "fingerprint": _obligation_fingerprint(parent_task_id, obligation),
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]


def _update_parent_obligation_summary(
    parent_task_id: str,
    ledger: LedgerManager,
    obligations_path: Path,
    payload: dict[str, Any],
) -> dict[str, Any]:
    summary = summarize_proof_obligations(payload)
    ledger.update_runtime_metadata(
        parent_task_id,
        proof_obligations_file=str(obligations_path),
        proof_obligation_summary=summary,
    )
    status_counts = summary.get("status_counts", {}) if isinstance(summary.get("status_counts", {}), dict) else {}
    try:
        accepted_debt = int(status_counts.get("accepted_as_proof_debt", 0) or 0)
    except (TypeError, ValueError):
        accepted_debt = 0
    parent_status = str(ledger.ledger.get("tasks", {}).get(parent_task_id, {}).get("status", "") or "")
    if accepted_debt > 0 and parent_status == TaskStatus.COMPLETED.value:
        ledger.update_status(parent_task_id, TaskStatus.COMPLETED_WITH_PROOF_DEBT)
    return summary


def _child_completed_obligation_payload(
    *,
    child_id: str,
    parent_task_id: str,
    obligation: dict[str, Any],
) -> dict[str, Any]:
    item = {
        "id": str(obligation.get("id", "") or "obligation"),
        "title": str(obligation.get("title", "") or obligation.get("id", "") or "Proof obligation"),
        "kind": str(obligation.get("kind", "") or "source_step"),
        "source_ref": str(obligation.get("source_ref", "") or ""),
        "depends_on": obligation.get("depends_on", []) if isinstance(obligation.get("depends_on", []), list) else [],
        "lean_landing": str(obligation.get("lean_landing", "") or ""),
        "status": "proved",
        "review_status": "accepted",
        "blocking": bool(obligation.get("blocking", True)),
        "scaffold_hypotheses": [],
        "notes": str(obligation.get("notes", "") or ""),
        "discharged_by_task": child_id,
        "last_review_evidence": f"Discharged parent task {parent_task_id} obligation.",
    }
    return {
        "schema_version": "phase2.proof_obligations.v1",
        "task_id": child_id,
        "classification": {
            "requires_decomposition": False,
            "reason": "Ledger obligation task completed and reconciled to parent proof obligation.",
            "evidence": [f"parent_task_id={parent_task_id}"],
        },
        "obligations": [item],
        "scaffold_hypotheses": [],
        "review_history": [],
    }


def _load_existing_child_obligation_payload(path: Path, child_task: dict[str, Any]) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return normalize_proof_obligations(read_json_safely(path, {}), child_task)


def _child_concrete_discharge_obligation(
    child_payload: dict[str, Any],
    parent_obligation: dict[str, Any],
) -> dict[str, Any] | None:
    if needs_concrete_decomposition(child_payload):
        return None
    if placeholder_obligation_ids(child_payload):
        return None
    obligations = child_payload.get("obligations", []) if isinstance(child_payload.get("obligations", []), list) else []
    parent_obligation_id = str(parent_obligation.get("id", "") or "").strip()
    matching = [
        item
        for item in obligations
        if isinstance(item, dict) and str(item.get("id", "") or "").strip() == parent_obligation_id
    ]
    fallback = [item for item in obligations if isinstance(item, dict) and item not in matching]
    for item in [*matching, *fallback]:
        if _is_reviewed_concrete_child_obligation(item):
            return item
    return None


def _is_reviewed_concrete_child_obligation(item: dict[str, Any]) -> bool:
    if str(item.get("status", "") or "").strip() != "proved":
        return False
    if str(item.get("review_status", "") or "").strip() != "accepted":
        return False
    if not proof_contract_is_verified(item):
        return False
    if not str(item.get("source_ref", "") or "").strip():
        return False
    if not str(item.get("lean_landing", "") or "").strip():
        return False
    if not str(item.get("expected_theorem_signature", "") or "").strip():
        return False
    landing_kind = str(item.get("landing_kind", "") or "").strip()
    return landing_kind not in {"", "empty", "unknown"}


def _set_if_changed(target: dict[str, Any], key: str, value: Any) -> bool:
    if target.get(key) == value:
        return False
    target[key] = value
    return True


def _absorb_child_discharge_into_parent_obligation(
    *,
    obligation: dict[str, Any],
    child_obligation: dict[str, Any],
    child_id: str,
) -> bool:
    changed = False
    for field in (
        "source_ref",
        "lean_landing",
        "expected_theorem_signature",
        "landing_kind",
        "proof_contract_status",
        "body_reassumption_check",
        "signature_match",
        "public_premise_check",
        "proof_contract_notes",
        "notes",
    ):
        value = child_obligation.get(field)
        if isinstance(value, str) and not value.strip():
            continue
        if value is None:
            continue
        changed = _set_if_changed(obligation, field, value) or changed
    if isinstance(child_obligation.get("source_output_alignment"), dict):
        changed = _set_if_changed(
            obligation,
            "source_output_alignment",
            child_obligation["source_output_alignment"],
        ) or changed
    changed = _set_if_changed(obligation, "status", "proved") or changed
    changed = _set_if_changed(obligation, "review_status", "accepted") or changed
    changed = _set_if_changed(obligation, "discharged_by_task", child_id) or changed
    evidence = f"Discharged by ledger obligation task {child_id} using child-local proof obligation evidence."
    changed = _set_if_changed(obligation, "last_review_evidence", evidence) or changed
    for scaffold in obligation.get("scaffold_hypotheses", []):
        if isinstance(scaffold, dict) and scaffold.get("status") != "discharged":
            scaffold["status"] = "discharged"
            changed = True
    return changed


def _parent_can_be_marked_clean(summary: dict[str, Any]) -> bool:
    status_counts = summary.get("status_counts", {}) if isinstance(summary.get("status_counts", {}), dict) else {}
    try:
        accepted_debt = int(status_counts.get("accepted_as_proof_debt", 0) or 0)
    except (TypeError, ValueError):
        accepted_debt = 0
    open_blocking = summary.get("open_blocking_ids", [])
    return (
        accepted_debt == 0
        and isinstance(open_blocking, list)
        and not open_blocking
        and not bool(summary.get("needs_concrete_decomposition", False))
    )
