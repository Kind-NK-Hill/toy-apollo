from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id, canonicalize_id_list


OBLIGATION_TASK_TYPE = "Phase2ObligationTask"
OBLIGATION_TASK_ID_PREFIX = "obl"
MAX_OBLIGATION_TASK_ID_LENGTH = 120
_PROMOTION_DISABLED_REASON = (
    "obligation child promotion is disabled; absorb proof obligations into parent/support files"
)


@dataclass(frozen=True)
class ObligationPromotionReport:
    parent_task_id: str
    created: list[str] = field(default_factory=list)
    updated: list[str] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)


def obligation_task_id(parent_task_id: str, obligation_id: str) -> str:
    """Legacy id helper kept only so old reports/tests remain readable."""
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
    obligation_part = raw_obligation[: max(obligation_budget, 16)].strip("_") or "obligation"
    return canonicalize_block_id(f"{OBLIGATION_TASK_ID_PREFIX}_{parent_part}_{obligation_part}_{digest}")


def is_obligation_task(task: dict[str, Any] | None) -> bool:
    return isinstance(task, dict) and str(task.get("type", "") or "") == OBLIGATION_TASK_TYPE


def promote_obligation_tasks_for_task(
    parent_task_id: str,
    ledger: Any,
    settings: Any,
) -> ObligationPromotionReport:
    del ledger, settings
    return ObligationPromotionReport(
        parent_task_id=canonicalize_block_id(parent_task_id),
        skipped=[_PROMOTION_DISABLED_REASON],
    )


def promote_all_obligation_tasks(
    ledger: Any,
    settings: Any,
    task_ids: list[str] | tuple[str, ...] | None = None,
) -> dict[str, list[str] | int]:
    del ledger, settings
    parent_ids = canonicalize_id_list(task_ids or [])
    return {
        "parents_scanned": parent_ids,
        "created": [],
        "updated": [],
        "skipped": [f"{parent_id}:{_PROMOTION_DISABLED_REASON}" for parent_id in parent_ids],
        "created_count": 0,
        "updated_count": 0,
    }


def reconcile_obligation_tasks_for_task(parent_task_id: str, ledger: Any, settings: Any) -> dict[str, list[str]]:
    del parent_task_id, ledger, settings
    return {"proved": [], "open": []}
