from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id


SCHEMA_VERSION = 1

ALLOWED_KINDS = {
    "hard",
    "soft",
    "translation",
    "proof_debt_support",
    "materialized",
    "violation",
    "legacy_inferred",
}

ALLOWED_CRITERIA = {
    "operator_declared_reliance",
    "explicit_text_reference",
    "soft_minimal_sufficient",
    "interface_translation",
    "proof_debt_support",
    "final_union_materialized",
    "undeclared_candidate_import",
    "legacy_inferred_from_output",
}


@dataclass(frozen=True)
class DependencyDecision:
    task_id: str
    dep_id: str
    kind: str
    phase: str
    criterion: str
    evidence: str = ""
    source_plan: str = ""
    source_file: str = ""

    @property
    def decision_id(self) -> str:
        return "|".join([self.task_id, self.dep_id, self.kind, self.phase, self.criterion])


def _dependency_decisions_dir(settings: Any) -> Path:
    configured = getattr(settings, "dependency_decisions_dir", None)
    if configured is not None:
        return Path(configured)
    return Path(getattr(settings, "artifact_root")) / "dependency_decisions"


def _utc_stamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def _validate_decision(decision: DependencyDecision) -> DependencyDecision:
    task_id = canonicalize_block_id(decision.task_id)
    dep_id = canonicalize_block_id(decision.dep_id)
    if not task_id:
        raise ValueError("Dependency decision task_id is required.")
    if not dep_id:
        raise ValueError("Dependency decision dep_id is required.")
    if decision.kind not in ALLOWED_KINDS:
        raise ValueError(f"Invalid dependency decision kind: {decision.kind}")
    if decision.criterion not in ALLOWED_CRITERIA:
        raise ValueError(f"Invalid dependency decision criterion: {decision.criterion}")
    phase = str(decision.phase or "").strip()
    if not phase:
        raise ValueError("Dependency decision phase is required.")
    return DependencyDecision(
        task_id=task_id,
        dep_id=dep_id,
        kind=decision.kind,
        phase=phase,
        criterion=decision.criterion,
        evidence=str(decision.evidence or ""),
        source_plan=str(decision.source_plan or ""),
        source_file=str(decision.source_file or ""),
    )


def _decision_to_payload(decision: DependencyDecision) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "decision_id": decision.decision_id,
        "recorded_at": _utc_stamp(),
        "task_id": decision.task_id,
        "dep_id": decision.dep_id,
        "kind": decision.kind,
        "phase": decision.phase,
        "criterion": decision.criterion,
        "evidence": decision.evidence,
        "source_plan": decision.source_plan,
        "source_file": decision.source_file,
    }


def load_dependency_decisions(settings: Any, task_id: str) -> list[dict[str, Any]]:
    canonical_task_id = canonicalize_block_id(task_id)
    if not canonical_task_id:
        return []
    decision_file = _dependency_decisions_dir(settings) / f"{canonical_task_id}.jsonl"
    if not decision_file.exists():
        return []
    decisions: list[dict[str, Any]] = []
    for raw_line in decision_file.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        payload = json.loads(line)
        if isinstance(payload, dict):
            decisions.append(payload)
    return decisions


def record_dependency_decision(settings: Any, decision: DependencyDecision) -> bool:
    normalized = _validate_decision(decision)
    decision_dir = _dependency_decisions_dir(settings)
    decision_dir.mkdir(parents=True, exist_ok=True)
    decision_file = decision_dir / f"{normalized.task_id}.jsonl"

    existing_ids = {
        payload.get("decision_id")
        for payload in load_dependency_decisions(settings, normalized.task_id)
        if isinstance(payload, dict)
    }
    if normalized.decision_id in existing_ids:
        return False

    payload = _decision_to_payload(normalized)
    with open(decision_file, "a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, ensure_ascii=False, sort_keys=True) + "\n")
    return True
