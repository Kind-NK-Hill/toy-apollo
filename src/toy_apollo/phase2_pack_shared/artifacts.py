from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from .io import read_file_safely, read_json_safely, sha256_text

DRAFT_FILE_NAME = "draft.lean"
SEARCH_MANIFEST_FILE_NAME = "search_manifest.json"
ATTEMPT_HISTORY_FILE_NAME = "attempt_history.json"
FAILURE_SUMMARY_FILE_NAME = "failure_summary.md"
INTENT_CONTRACT_FILE_NAME = "intent_contract.json"
PROOF_OBLIGATIONS_FILE_NAME = "proof_obligations.json"
BUILD_RESULT_PREFIX = "build_result"
OFFICIAL_SNAPSHOT_PREFIX = "official_snapshot"
SEMANTIC_REVIEW_RESULT_TEMPLATE_ALIAS = "semantic_review_result_template.json"
SEMANTIC_REVIEW_REQUEST_PREFIX = "semantic_review_request"
SEMANTIC_REVIEW_REQUEST_ALIAS = "semantic_review_request.json"
REVIEW_REPAIR_REQUEST_PREFIX = "review_repair_request"
REVIEW_REPAIR_REQUEST_ALIAS = "review_repair_request.json"
REVIEW_REPAIR_SUMMARY_PREFIX = "review_repair_summary"
REVIEW_REPAIR_SUMMARY_ALIAS = "review_repair_summary.md"
DRAFT_PRE_REPAIR_PREFIX = "draft_pre_repair"
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


def list_candidate_files(pack_dir: Path) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(r"candidate_v(\d+)\.lean", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted([p for p in pack_dir.glob("candidate_v*.lean") if p.is_file()], key=sort_key)


def select_latest_candidate(pack_dir: Path) -> Path | None:
    candidates = list_candidate_files(pack_dir)
    return candidates[-1] if candidates else None


def list_versioned_json_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.json", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted([p for p in pack_dir.glob(f"{prefix}_v*.json") if p.is_file()], key=sort_key)


def list_versioned_md_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.md", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted([p for p in pack_dir.glob(f"{prefix}_v*.md") if p.is_file()], key=sort_key)


def list_versioned_lean_files(pack_dir: Path, prefix: str) -> list[Path]:
    def sort_key(path: Path) -> tuple[int, str]:
        match = re.fullmatch(rf"{re.escape(prefix)}_v(\d+)\.lean", path.name)
        if match:
            return int(match.group(1)), path.name
        return -1, path.name

    return sorted([p for p in pack_dir.glob(f"{prefix}_v*.lean") if p.is_file()], key=sort_key)


def select_latest_verify_result(pack_dir: Path) -> Path | None:
    results = list_versioned_json_files(pack_dir, "verify_result")
    return results[-1] if results else None


def select_latest_build_result(pack_dir: Path) -> Path | None:
    results = list_versioned_json_files(pack_dir, BUILD_RESULT_PREFIX)
    return results[-1] if results else None


def select_latest_official_snapshot(pack_dir: Path) -> Path | None:
    results = list_versioned_lean_files(pack_dir, OFFICIAL_SNAPSHOT_PREFIX)
    return results[-1] if results else None


def review_request_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{SEMANTIC_REVIEW_REQUEST_PREFIX}_v{attempt}.json"


def latest_review_request_path(pack_dir: Path) -> Path:
    return pack_dir / SEMANTIC_REVIEW_REQUEST_ALIAS


def review_repair_request_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{REVIEW_REPAIR_REQUEST_PREFIX}_v{attempt}.json"


def latest_review_repair_request_path(pack_dir: Path) -> Path:
    return pack_dir / REVIEW_REPAIR_REQUEST_ALIAS


def review_repair_summary_path(pack_dir: Path, attempt: int) -> Path:
    return pack_dir / f"{REVIEW_REPAIR_SUMMARY_PREFIX}_v{attempt}.md"


def latest_review_repair_summary_path(pack_dir: Path) -> Path:
    return pack_dir / REVIEW_REPAIR_SUMMARY_ALIAS


def next_review_repair_attempt(pack_dir: Path) -> int:
    latest = 0
    for path in list_versioned_json_files(pack_dir, REVIEW_REPAIR_REQUEST_PREFIX):
        match = re.fullmatch(rf"{re.escape(REVIEW_REPAIR_REQUEST_PREFIX)}_v(\d+)\.json", path.name)
        if match:
            latest = max(latest, int(match.group(1)))
    return latest + 1 if latest else 1


def next_pre_repair_draft_path(pack_dir: Path) -> Path:
    latest = list_versioned_lean_files(pack_dir, DRAFT_PRE_REPAIR_PREFIX)
    if not latest:
        return pack_dir / f"{DRAFT_PRE_REPAIR_PREFIX}_v1.lean"
    match = re.fullmatch(rf"{re.escape(DRAFT_PRE_REPAIR_PREFIX)}_v(\d+)\.lean", latest[-1].name)
    version = int(match.group(1)) + 1 if match else 1
    return pack_dir / f"{DRAFT_PRE_REPAIR_PREFIX}_v{version}.lean"


def intent_contract_path(pack_dir: Path) -> Path:
    return pack_dir / INTENT_CONTRACT_FILE_NAME


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


def find_existing_task_file(task_id: str, source_plan: str, settings) -> Path | None:
    for candidate in iter_official_output_targets(task_id, source_plan, settings):
        if candidate.exists():
            return candidate
    return None


def select_latest_existing_task_file(task_id: str, source_plan: str, settings) -> Path | None:
    existing = [candidate for candidate in iter_official_output_targets(task_id, source_plan, settings) if candidate.exists()]
    if not existing:
        return None
    return max(existing, key=_path_mtime)


def _path_mtime(path: Path | None) -> float:
    if path is None:
        return 0.0
    try:
        return path.stat().st_mtime
    except OSError:
        return 0.0


def official_output_candidate_divergence(
    *,
    task_id: str,
    source_plan: str,
    settings,
    candidate_path: Path,
    candidate_hash: str = "",
    draft_path: Path | None = None,
) -> dict[str, Any]:
    info: dict[str, Any] = {
        "task_id": task_id,
        "has_official_output": False,
        "official_output_file": "",
        "official_output_hash": "",
        "candidate_file": str(candidate_path),
        "candidate_hash": str(candidate_hash or ""),
        "draft_file": str(draft_path) if draft_path else "",
        "draft_hash": "",
        "official_mtime": 0.0,
        "candidate_mtime": _path_mtime(candidate_path),
        "draft_mtime": _path_mtime(draft_path),
        "official_differs_from_candidate": False,
        "official_differs_from_draft": False,
        "official_newer_than_candidate": False,
        "official_newer_than_draft": False,
        "official_supersedes_candidate": False,
    }

    if candidate_path.exists() and not candidate_hash:
        candidate_text = read_file_safely(candidate_path)
        candidate_hash = sha256_text(candidate_text)
        info["candidate_hash"] = candidate_hash
    if draft_path is not None and draft_path.exists():
        draft_text = read_file_safely(draft_path)
        draft_hash = sha256_text(draft_text)
        info["draft_hash"] = draft_hash
    else:
        draft_hash = ""

    official_candidates: list[dict[str, Any]] = []
    for target in iter_official_output_targets(task_id, source_plan, settings):
        if not target.exists():
            continue
        official_text = read_file_safely(target)
        official_hash = sha256_text(official_text)
        official_candidates.append(
            {
                "path": target,
                "hash": official_hash,
                "mtime": _path_mtime(target),
            }
        )
    if not official_candidates:
        return info

    info["has_official_output"] = True
    superseding = [
        item
        for item in official_candidates
        if candidate_hash and item["hash"] != candidate_hash and item["mtime"] > info["candidate_mtime"]
    ]
    selected = max(superseding or official_candidates, key=lambda item: item["mtime"])
    official_hash = str(selected["hash"])
    info["official_output_file"] = str(selected["path"])
    info["official_output_hash"] = official_hash
    info["official_mtime"] = float(selected["mtime"])

    candidate_differs = bool(candidate_hash and official_hash != candidate_hash)
    draft_differs = bool(draft_hash and official_hash != draft_hash)
    info["official_differs_from_candidate"] = candidate_differs
    info["official_differs_from_draft"] = draft_differs
    info["official_newer_than_candidate"] = info["official_mtime"] > info["candidate_mtime"]
    info["official_newer_than_draft"] = bool(draft_path) and info["official_mtime"] > info["draft_mtime"]
    info["official_supersedes_candidate"] = bool(candidate_differs and info["official_newer_than_candidate"])
    return info


def stale_candidate_official_output_message(
    *,
    task_id: str,
    source_plan: str,
    settings,
    candidate_path: Path,
    candidate_hash: str = "",
    draft_path: Path | None = None,
    action: str = "candidate review",
) -> str:
    divergence = official_output_candidate_divergence(
        task_id=task_id,
        source_plan=source_plan,
        settings=settings,
        candidate_path=candidate_path,
        candidate_hash=candidate_hash,
        draft_path=draft_path,
    )
    if not divergence.get("official_supersedes_candidate"):
        return ""
    return (
        f"Stale {action} target for {task_id}: the official output "
        f"`{divergence.get('official_output_file')}` is newer than and differs from "
        f"`{divergence.get('candidate_file')}`. Review the already-repaired official output with "
        "`review-now --review-subject existing`, or intentionally sync the official output into "
        "`draft.lean` and rerun `build-check` before `review-now --review-subject candidate`."
    )


def load_attempt_history(pack_dir: Path, task_id: str) -> dict[str, Any]:
    default = {"task_id": task_id, "attempts": []}
    payload = read_json_safely(pack_dir / ATTEMPT_HISTORY_FILE_NAME, default)
    if not isinstance(payload, dict):
        return default
    attempts = payload.get("attempts", [])
    if not isinstance(attempts, list):
        attempts = []
    payload["task_id"] = str(payload.get("task_id") or task_id)
    payload["attempts"] = attempts
    return payload
