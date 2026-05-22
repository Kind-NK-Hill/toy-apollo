from __future__ import annotations

import re
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list

from .phase2_pack_shared.io import read_json_safely, write_json

PROOF_OBLIGATIONS_FILE_NAME = "proof_obligations.json"
PROOF_OBLIGATIONS_SCHEMA_VERSION = "phase2.proof_obligations.v1"
PLACEHOLDER_OBLIGATION_ID = "source_proof_spine"

OBLIGATION_KINDS = {
    "source_step",
    "analytic_lemma",
    "translation",
    "proof_debt_support",
    "interface_conversion",
    "assembly",
    "scaffold_elimination",
    "dependency",
    "external_theorem_gap",
    "review_blocker",
}
OBLIGATION_STATUSES = {"open", "in_progress", "proved", "partial", "blocked", "obsolete", "accepted_as_proof_debt"}
OBLIGATION_REVIEW_STATUSES = {"unreviewed", "accepted", "rejected", "needs_review"}
REVIEW_ITEM_STATUSES = {"covered", "partial", "missing", "violated", "unclear", "not_applicable", "accepted_as_proof_debt"}
PASSING_REVIEW_ITEM_STATUSES = {"covered", "not_applicable", "accepted_as_proof_debt"}
PASSING_OBLIGATION_STATUSES = {"proved", "obsolete", "accepted_as_proof_debt"}
SCAFFOLD_CATEGORIES = {
    "interface_translation",
    "proof_debt_support",
    "proof_obligation",
    "external_theorem_gap",
    "forbidden_shortcut",
}


def utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def proof_obligation_path(pack_dir: Path) -> Path:
    return pack_dir / PROOF_OBLIGATIONS_FILE_NAME


def classify_task_complexity(task: dict[str, Any], current_record: dict[str, Any] | None = None) -> dict[str, Any]:
    content = str(task.get("content", "") or "")
    task_type = str(task.get("type", "") or "")
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    all_deps = canonicalize_id_list([*hard_deps, *soft_imports])
    source_lines = [line.strip() for line in content.splitlines() if line.strip()]
    proof_bearing = bool(re.search(r"proof|prove|show|construction|argument", task_type, re.IGNORECASE))
    proof_bearing = proof_bearing or bool(re.search(r"\\begin\{proof\}|\\textit\{proof\}|(^|\s)proof[.:]?", content, re.IGNORECASE))
    structural_ops = re.findall(
        r"\b(construct|choose|reduce|decompose|partition|split|case|suffices|deduce|derive|"
        r"approximate|limit|converge|interchange|rewrite|transform|substitute|compose)\b",
        content,
        flags=re.IGNORECASE,
    )
    evidence: list[str] = []
    if proof_bearing:
        evidence.append("source text or task type is proof-bearing")
    if len(all_deps) >= 2:
        evidence.append(f"task has {len(all_deps)} declared upstream dependencies")
    if len(content) >= 1200:
        evidence.append("source text is long enough to hide multiple obligations")
    if len(source_lines) >= 5:
        evidence.append("source text has multiple paragraphs or proof lines")
    if len(structural_ops) >= 2:
        evidence.append("source text uses multiple structural proof operations")
    record = current_record if isinstance(current_record, dict) else {}
    prior_semantic_failures = [
        item for item in record.get("attempt_history", []) if isinstance(item, dict) and item.get("stage") == "semantic_review"
    ]
    if len(prior_semantic_failures) >= 2:
        evidence.append("task has repeated semantic review failures")
    requires_decomposition = (
        (proof_bearing and (len(all_deps) >= 2 or len(content) >= 1200 or len(structural_ops) >= 2))
        or len(all_deps) >= 4
        or len(structural_ops) >= 4
        or len(prior_semantic_failures) >= 2
    )
    if requires_decomposition:
        reason = "complex proof: prove independently reviewable obligations before final assembly"
    else:
        reason = "normal proof: no structural decomposition trigger was detected"
    return {
        "requires_decomposition": bool(requires_decomposition),
        "reason": reason,
        "evidence": evidence,
        "dependency_count": len(all_deps),
        "source_length": len(content),
        "structural_operation_count": len(structural_ops),
    }


def default_proof_obligations(task: dict[str, Any], current_record: dict[str, Any] | None = None) -> dict[str, Any]:
    task_id = canonicalize_block_id(str(task.get("block_id", "") or ""))
    classification = classify_task_complexity(task, current_record)
    obligations: list[dict[str, Any]] = []
    if classification["requires_decomposition"]:
        obligations.append(
            {
                "id": PLACEHOLDER_OBLIGATION_ID,
                "title": "Source proof spine",
                "kind": "source_step",
                "source_ref": "Original task text; replace this placeholder with precise source spans.",
                "depends_on": [],
                "lean_landing": "",
                "status": "open",
                "review_status": "unreviewed",
                "blocking": True,
                "scaffold_hypotheses": [],
                "notes": "Complex tasks must split this placeholder into concrete proof obligations before semantic pass.",
            }
        )
    return {
        "schema_version": PROOF_OBLIGATIONS_SCHEMA_VERSION,
        "task_id": task_id,
        "generated_at": utc_stamp(),
        "classification": classification,
        "obligations": obligations,
        "scaffold_hypotheses": [],
        "review_history": [],
    }


def normalize_proof_obligations(payload: Any, task: dict[str, Any]) -> dict[str, Any]:
    default = default_proof_obligations(task)
    if not isinstance(payload, dict):
        return default
    task_id = canonicalize_block_id(str(task.get("block_id", "") or payload.get("task_id", "") or ""))
    normalized = dict(payload)
    normalized["schema_version"] = PROOF_OBLIGATIONS_SCHEMA_VERSION
    normalized["task_id"] = task_id
    normalized["generated_at"] = str(normalized.get("generated_at", "") or default["generated_at"])
    classification = normalized.get("classification", {})
    if not isinstance(classification, dict):
        classification = default["classification"]
    else:
        merged = dict(default["classification"])
        merged.update(classification)
        merged["requires_decomposition"] = bool(merged.get("requires_decomposition", False))
        raw_evidence = merged.get("evidence", [])
        merged["evidence"] = [str(item) for item in raw_evidence if str(item).strip()] if isinstance(raw_evidence, list) else []
        classification = merged
    normalized["classification"] = classification
    raw_obligations = normalized.get("obligations", [])
    if not isinstance(raw_obligations, list):
        raw_obligations = []
    normalized["obligations"] = [
        _normalize_obligation(item, index) for index, item in enumerate(raw_obligations, start=1) if isinstance(item, dict)
    ]
    raw_scaffolds = normalized.get("scaffold_hypotheses", [])
    normalized["scaffold_hypotheses"] = _normalize_scaffold_list(raw_scaffolds)
    raw_history = normalized.get("review_history", [])
    normalized["review_history"] = raw_history if isinstance(raw_history, list) else []
    return normalized


def ensure_proof_obligations_file(
    pack_dir: Path,
    task: dict[str, Any],
    *,
    current_record: dict[str, Any] | None = None,
) -> dict[str, Any]:
    path = proof_obligation_path(pack_dir)
    if path.exists():
        payload = normalize_proof_obligations(read_json_safely(path, {}), task)
    else:
        payload = default_proof_obligations(task, current_record)
    path.parent.mkdir(parents=True, exist_ok=True)
    write_json(path, payload)
    return payload


def load_proof_obligations(pack_dir: Path, task: dict[str, Any]) -> dict[str, Any]:
    return ensure_proof_obligations_file(pack_dir, task)


def summarize_proof_obligations(payload: dict[str, Any]) -> dict[str, Any]:
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    status_counts = Counter(str(item.get("status", "open") or "open") for item in obligations if isinstance(item, dict))
    review_counts = Counter(str(item.get("review_status", "unreviewed") or "unreviewed") for item in obligations if isinstance(item, dict))
    alignment_counts = Counter(
        str(item.get("source_output_alignment", {}).get("audit_class", "") or "unclassified")
        for item in obligations
        if isinstance(item, dict)
        and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt"
        and isinstance(item.get("source_output_alignment", {}), dict)
    )
    open_blocking_ids = [
        str(item.get("id", "") or "")
        for item in obligations
        if isinstance(item, dict)
        and bool(item.get("blocking", True))
        and str(item.get("status", "open") or "open") not in PASSING_OBLIGATION_STATUSES
    ]
    classification = payload.get("classification", {}) if isinstance(payload.get("classification", {}), dict) else {}
    scaffolds = payload.get("scaffold_hypotheses", []) if isinstance(payload.get("scaffold_hypotheses", []), list) else []
    placeholder_ids = placeholder_obligation_ids(payload)
    return {
        "schema_version": PROOF_OBLIGATIONS_SCHEMA_VERSION,
        "task_id": str(payload.get("task_id", "") or ""),
        "requires_decomposition": bool(classification.get("requires_decomposition", False)),
        "total_obligations": len(obligations),
        "status_counts": dict(status_counts),
        "review_status_counts": dict(review_counts),
        "source_output_alignment_counts": dict(alignment_counts),
        "open_blocking_ids": open_blocking_ids,
        "scaffold_hypothesis_count": len(scaffolds),
        "placeholder_obligation_ids": placeholder_ids,
        "needs_concrete_decomposition": needs_concrete_decomposition(payload),
    }


def is_placeholder_obligation(item: dict[str, Any]) -> bool:
    obligation_id = str(item.get("id", "") or "").strip()
    if obligation_id != PLACEHOLDER_OBLIGATION_ID:
        return False
    source_ref = str(item.get("source_ref", "") or "").lower()
    notes = str(item.get("notes", "") or "").lower()
    lean_landing = str(item.get("lean_landing", "") or "").strip()
    return "placeholder" in source_ref or "placeholder" in notes or not lean_landing


def placeholder_obligation_ids(payload: dict[str, Any]) -> list[str]:
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    ids: list[str] = []
    for item in obligations:
        if isinstance(item, dict) and is_placeholder_obligation(item):
            obligation_id = str(item.get("id", "") or "").strip()
            if obligation_id:
                ids.append(obligation_id)
    return ids


def needs_concrete_decomposition(payload: dict[str, Any]) -> bool:
    classification = payload.get("classification", {}) if isinstance(payload.get("classification", {}), dict) else {}
    if not bool(classification.get("requires_decomposition", False)):
        return False
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    concrete = [item for item in obligations if isinstance(item, dict) and not is_placeholder_obligation(item)]
    return not concrete or bool(placeholder_obligation_ids(payload))


def render_proof_obligations_markdown(payload: dict[str, Any], *, path: Path | None = None) -> str:
    summary = summarize_proof_obligations(payload)
    classification = payload.get("classification", {}) if isinstance(payload.get("classification", {}), dict) else {}
    lines = [
        "## Proof Obligation Ledger",
        "",
        f"- File: `{path}`" if path is not None else "- File: `(not recorded)`",
        f"- Requires decomposition: `{summary['requires_decomposition']}`",
        f"- Needs concrete decomposition: `{summary['needs_concrete_decomposition']}`",
        f"- Classification: {classification.get('reason', '(none)')}",
        f"- Open blocking obligations: `{', '.join(summary['open_blocking_ids']) if summary['open_blocking_ids'] else '(none)'}`",
    ]
    if summary["placeholder_obligation_ids"]:
        lines.append(
            "- Placeholder obligations: `"
            + ", ".join(summary["placeholder_obligation_ids"])
            + "` (not a valid completed decomposition)"
        )
    evidence = classification.get("evidence", []) if isinstance(classification.get("evidence", []), list) else []
    if evidence:
        lines.append("- Classification evidence:")
        for item in evidence:
            lines.append(f"  - {item}")
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    lines.extend(["", "### Obligations"])
    if not obligations:
        lines.append("- No explicit obligations are recorded. If the source proof has intermediate steps, add them before requesting pass review.")
    else:
        for item in obligations:
            if not isinstance(item, dict):
                continue
            deps = item.get("depends_on", []) if isinstance(item.get("depends_on", []), list) else []
            lines.append(
                f"- `{item.get('id', '')}` / `{item.get('kind', '')}` / `{item.get('status', '')}` "
                f"/ review `{item.get('review_status', '')}` / blocking `{bool(item.get('blocking', True))}`"
            )
            title = str(item.get("title", "") or "").strip()
            source_ref = str(item.get("source_ref", "") or "").strip()
            lean_landing = str(item.get("lean_landing", "") or "").strip()
            if title:
                lines.append(f"  - Title: {title}")
            if source_ref:
                lines.append(f"  - Source ref: {source_ref}")
            lines.append(f"  - Depends on: `{', '.join(str(dep) for dep in deps) if deps else '(none)'}`")
            lines.append(f"  - Lean landing: `{lean_landing or '(not assigned)'}`")
            alignment = item.get("source_output_alignment", {})
            if isinstance(alignment, dict) and alignment:
                audit_class = str(alignment.get("audit_class", "") or "unclassified")
                family = str(alignment.get("family", "") or "unclassified")
                next_action = str(alignment.get("next_action", "") or "").strip()
                existing = alignment.get("existing_local_declarations", [])
                missing = alignment.get("missing_landing_names", [])
                lines.append(f"  - Source-output alignment: `{audit_class}` / `{family}`")
                if isinstance(existing, list) and existing:
                    decls = []
                    for decl in existing:
                        if not isinstance(decl, dict):
                            continue
                        name = str(decl.get("name", "") or "")
                        kind = str(decl.get("kind", "") or "")
                        file = str(decl.get("file", "") or "")
                        line = str(decl.get("line", "") or "")
                        if name:
                            location = f"{file}:{line}" if file and line else file
                            decls.append(f"{name} ({kind}{', ' + location if location else ''})")
                    if decls:
                        lines.append(f"  - Existing local declarations: `{'; '.join(decls)}`")
                if isinstance(missing, list) and missing:
                    lines.append(f"  - Missing landing names: `{', '.join(str(name) for name in missing)}`")
                if next_action:
                    lines.append(f"  - Alignment next action: {next_action}")
    scaffolds = payload.get("scaffold_hypotheses", []) if isinstance(payload.get("scaffold_hypotheses", []), list) else []
    lines.extend(["", "### Scaffold Hypotheses"])
    if not scaffolds:
        lines.append("- None recorded.")
    else:
        for item in scaffolds:
            if isinstance(item, dict):
                lines.append(
                    f"- `{item.get('name', '(unnamed)')}` / `{item.get('category', 'proof_obligation')}` "
                    f"/ obligation `{item.get('obligation_id', '') or '(none)'}`: {item.get('discharge_plan', '')}"
                )
    return "\n".join(lines).rstrip() + "\n"


def validate_obligation_review_shape(result: dict[str, Any]) -> str:
    review = result.get("obligation_review")
    if not isinstance(review, dict):
        return "reviewer field obligation_review must be an object"
    status = str(review.get("status", "") or "").strip().lower()
    if status not in {"covered", "partial", "missing", "violated", "unclear"}:
        return "reviewer field obligation_review.status must be one of covered/partial/missing/violated/unclear"
    for field in ("items", "open_blockers", "scaffold_assessment"):
        if not isinstance(review.get(field, []), list):
            return f"reviewer field obligation_review.{field} must be a list"
    for item in review.get("items", []):
        if not isinstance(item, dict):
            return "reviewer field obligation_review.items entries must be objects"
        item_status = str(item.get("status", "") or "").strip().lower()
        if item_status not in REVIEW_ITEM_STATUSES:
            return "reviewer field obligation_review.items status must be covered/partial/missing/violated/unclear/not_applicable/accepted_as_proof_debt"
    return ""


def validate_obligation_review_for_pass(review_input: dict[str, Any], result: dict[str, Any]) -> str:
    shape_error = validate_obligation_review_shape(result)
    if shape_error:
        return shape_error
    review = result.get("obligation_review", {})
    if str(review.get("status", "") or "").strip().lower() != "covered":
        return "invalid reviewer output: pass verdict requires obligation_review.status = covered"
    open_blockers = review.get("open_blockers", [])
    if open_blockers:
        return "invalid reviewer output: pass verdict cannot include obligation_review.open_blockers"
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    payload = review_basis.get("proof_obligations", {}) if isinstance(review_basis.get("proof_obligations", {}), dict) else {}
    if needs_concrete_decomposition(payload):
        return "invalid reviewer output: complex tasks require concrete proof_obligations.json nodes before semantic pass"
    obligations = payload.get("obligations", []) if isinstance(payload.get("obligations", []), list) else []
    focus_ids = [
        str(item).strip()
        for item in review_basis.get("focus_obligation_ids", [])
        if str(item).strip()
    ] if isinstance(review_basis.get("focus_obligation_ids", []), list) else []
    if focus_ids:
        focus_set = set(focus_ids)
        required_ids = [
            str(item.get("id", "") or "")
            for item in obligations
            if isinstance(item, dict)
            and str(item.get("id", "") or "") in focus_set
            and bool(item.get("blocking", True))
            and str(item.get("status", "open") or "open") not in {"proved", "obsolete"}
        ]
    else:
        required_ids = [
            str(item.get("id", "") or "")
            for item in obligations
            if isinstance(item, dict)
            and str(item.get("id", "") or "")
            and bool(item.get("blocking", True))
            and str(item.get("status", "open") or "open") not in PASSING_OBLIGATION_STATUSES
        ]
    if not required_ids:
        return ""
    item_statuses: dict[str, str] = {}
    for item in review.get("items", []):
        if not isinstance(item, dict):
            continue
        item_id = str(item.get("obligation_id", "") or item.get("id", "") or "").strip()
        if item_id:
            item_statuses[item_id] = str(item.get("status", "") or "").strip().lower()
    missing = [item_id for item_id in required_ids if item_statuses.get(item_id) not in PASSING_REVIEW_ITEM_STATUSES]
    if missing:
        return "invalid reviewer output: pass verdict requires covered/not_applicable obligation_review.items for: " + ", ".join(missing)
    return ""


def extract_obligation_review_blockers(review_result: dict[str, Any]) -> list[dict[str, str]]:
    review = review_result.get("obligation_review", {}) if isinstance(review_result.get("obligation_review", {}), dict) else {}
    blockers: list[dict[str, str]] = []
    for item in review.get("open_blockers", []) if isinstance(review.get("open_blockers", []), list) else []:
        if not isinstance(item, dict):
            continue
        obligation_id = str(item.get("obligation_id", "") or item.get("id", "") or "").strip()
        issue = str(item.get("issue", "") or item.get("summary", "") or item.get("evidence", "") or "").strip()
        if obligation_id or issue:
            blockers.append({"obligation_id": obligation_id, "issue": issue})
    for item in review.get("items", []) if isinstance(review.get("items", []), list) else []:
        if not isinstance(item, dict):
            continue
        status = str(item.get("status", "") or "").strip().lower()
        if status in PASSING_REVIEW_ITEM_STATUSES:
            continue
        obligation_id = str(item.get("obligation_id", "") or item.get("id", "") or "").strip()
        issue = str(item.get("issue", "") or item.get("summary", "") or item.get("evidence", "") or status).strip()
        if obligation_id or issue:
            blockers.append({"obligation_id": obligation_id, "issue": issue})
    deduped: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for item in blockers:
        key = (item.get("obligation_id", ""), item.get("issue", ""))
        if key in seen:
            continue
        seen.add(key)
        deduped.append(item)
    return deduped


def apply_obligation_review(pack_dir: Path, review_result: dict[str, Any]) -> dict[str, Any]:
    return apply_obligation_review_to_file(proof_obligation_path(pack_dir), review_result)


def apply_obligation_review_to_file(path: Path, review_result: dict[str, Any]) -> dict[str, Any]:
    if not path.exists():
        return {}
    payload = read_json_safely(path, {})
    if not isinstance(payload, dict):
        return {}
    task = {"block_id": payload.get("task_id", "")}
    payload = normalize_proof_obligations(payload, task)
    review = review_result.get("obligation_review", {}) if isinstance(review_result.get("obligation_review", {}), dict) else {}
    if not review:
        return payload
    by_id = {
        str(item.get("id", "") or ""): item
        for item in payload.get("obligations", [])
        if isinstance(item, dict) and str(item.get("id", "") or "")
    }
    verdict = str(review_result.get("verdict", "") or "").strip().lower()
    for item in review.get("items", []) if isinstance(review.get("items", []), list) else []:
        if not isinstance(item, dict):
            continue
        obligation_id = str(item.get("obligation_id", "") or item.get("id", "") or "").strip()
        if obligation_id not in by_id:
            continue
        status = str(item.get("status", "") or "").strip().lower()
        target = by_id[obligation_id]
        if status == "covered":
            target["review_status"] = "accepted"
            target["status"] = "proved"
            for scaffold in target.get("scaffold_hypotheses", []):
                if isinstance(scaffold, dict):
                    scaffold["status"] = "discharged"
        elif status == "accepted_as_proof_debt":
            target["review_status"] = "accepted"
            target["status"] = "accepted_as_proof_debt"
            for scaffold in target.get("scaffold_hypotheses", []):
                if isinstance(scaffold, dict):
                    scaffold["status"] = "accepted_as_proof_debt"
        elif status in {"partial", "missing", "violated", "unclear"}:
            target["review_status"] = "rejected" if status in {"missing", "violated"} else "needs_review"
            target["status"] = "blocked" if status in {"missing", "violated"} else "partial"
        elif status == "not_applicable":
            target["review_status"] = "accepted"
            target["status"] = "obsolete"
        target["last_review_evidence"] = str(item.get("evidence", "") or item.get("summary", "") or item.get("issue", "") or "")
    history = payload.get("review_history", [])
    if not isinstance(history, list):
        history = []
    history.append(
        {
            "reviewed_at": utc_stamp(),
            "verdict": verdict,
            "status": str(review.get("status", "") or ""),
            "summary": str(review.get("summary", "") or ""),
            "open_blockers": extract_obligation_review_blockers(review_result),
        }
    )
    payload["review_history"] = history
    payload["last_reviewed_at"] = utc_stamp()
    write_json(path, payload)
    return payload


def _normalize_obligation(item: dict[str, Any], index: int) -> dict[str, Any]:
    obligation_id = str(item.get("id", "") or "").strip()
    if not obligation_id:
        obligation_id = f"obligation_{index}"
    obligation_id = re.sub(r"[^A-Za-z0-9_]+", "_", obligation_id).strip("_") or f"obligation_{index}"
    kind = str(item.get("kind", "") or "source_step").strip()
    if kind not in OBLIGATION_KINDS:
        kind = "source_step"
    status = str(item.get("status", "") or "open").strip()
    if status not in OBLIGATION_STATUSES:
        status = "open"
    review_status = str(item.get("review_status", "") or "unreviewed").strip()
    if review_status not in OBLIGATION_REVIEW_STATUSES:
        review_status = "unreviewed"
    depends_on = item.get("depends_on", [])
    if not isinstance(depends_on, list):
        depends_on = []
    normalized = dict(item)
    normalized.update(
        {
            "id": obligation_id,
            "title": str(item.get("title", "") or obligation_id),
            "kind": kind,
            "source_ref": str(item.get("source_ref", "") or ""),
            "depends_on": [str(dep).strip() for dep in depends_on if str(dep).strip()],
            "lean_landing": str(item.get("lean_landing", "") or ""),
            "status": status,
            "review_status": review_status,
            "blocking": bool(item.get("blocking", True)),
            "scaffold_hypotheses": _normalize_scaffold_list(item.get("scaffold_hypotheses", [])),
            "notes": str(item.get("notes", "") or ""),
        }
    )
    return normalized


def _normalize_scaffold_list(raw: Any) -> list[dict[str, str]]:
    if not isinstance(raw, list):
        return []
    scaffolds: list[dict[str, str]] = []
    for index, item in enumerate(raw, start=1):
        if not isinstance(item, dict):
            continue
        category = str(item.get("category", "") or "proof_obligation").strip()
        if category not in SCAFFOLD_CATEGORIES:
            category = "proof_obligation"
        scaffolds.append(
            {
                "name": str(item.get("name", "") or f"scaffold_{index}"),
                "category": category,
                "obligation_id": str(item.get("obligation_id", "") or ""),
                "discharge_plan": str(item.get("discharge_plan", "") or ""),
                "status": str(item.get("status", "") or "open"),
            }
        )
    return scaffolds
