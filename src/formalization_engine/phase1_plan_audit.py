from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

# Per-profile canonical Phase 1 task-type tables. The default profile "mat"
# keeps the historical six MAT types and only adds `Lemma`/`Corollary`
# additively; the "cordis" profile uses the same shared set for now (Cordis
# plan v1 only uses the pre-existing five kinds, `Lemma`/`Corollary` first
# appear in paper section 3.1.3).
_PROFILE_PHASE1_TYPES: dict[str, tuple[str, ...]] = {
    "mat": (
        "Definition",
        "Theorem_Statement",
        "Theorem_with_Proof",
        "Example_Proof",
        "Problem",
        "Remark",
        "Lemma",
        "Corollary",
    ),
    "cordis": (
        "Definition",
        "Theorem_Statement",
        "Theorem_with_Proof",
        "Example_Proof",
        "Problem",
        "Remark",
        "Lemma",
        "Corollary",
    ),
}
CANONICAL_PHASE1_TYPES = _PROFILE_PHASE1_TYPES["mat"]

DEFAULT_PROFILE = "mat"

_CANONICAL_TYPE_LOOKUP = {value.lower(): value for value in CANONICAL_PHASE1_TYPES}
_PROFILE_TYPE_LOOKUP = {
    profile: {value.lower(): value for value in values}
    for profile, values in _PROFILE_PHASE1_TYPES.items()
}
_TYPE_ALIASES = {
    "exercise": "Problem",
}

_THEOREM_ENV_RE = re.compile(r"\\begin\{theorem\}", re.IGNORECASE)
_LEMMA_ENV_RE = re.compile(r"\\begin\{lemma\}", re.IGNORECASE)
_DEFINITION_ENV_RE = re.compile(r"\\begin\{definition\}", re.IGNORECASE)
_EXAMPLE_ENV_RE = re.compile(r"\\begin\{example\}", re.IGNORECASE)
_PROOF_ENV_RE = re.compile(r"\\begin\{proof\}", re.IGNORECASE)
_PROBLEMS_HEADER_RE = re.compile(r"\\subsection\*\{Problems\}", re.IGNORECASE)
_PROBLEM_ITEM_RE = re.compile(r"\\item\b")
_NUMBERED_PROBLEM_RE = re.compile(r"\\textbf\{\d+\.\d+\.\}")


def normalize_phase1_task_type(raw_type: Any, profile: str = DEFAULT_PROFILE) -> tuple[str | None, str | None]:
    original = str(raw_type or "").strip()
    if not original:
        return None, "Task type is empty."

    lowered = original.lower()
    lookup = _PROFILE_TYPE_LOOKUP.get(
        str(profile or DEFAULT_PROFILE).strip().lower() or DEFAULT_PROFILE,
        _CANONICAL_TYPE_LOOKUP,
    )
    if lowered in lookup:
        return lookup[lowered], None
    if lowered in _TYPE_ALIASES:
        canonical = _TYPE_ALIASES[lowered]
        return canonical, f"Task type {original!r} normalized to {canonical!r}."
    return None, f"Invalid Phase 1 task type: {original!r}."


def extract_phase1_tex_signals(tex_content: str) -> dict[str, Any]:
    item_count = len(_PROBLEM_ITEM_RE.findall(tex_content))
    numbered_count = len(_NUMBERED_PROBLEM_RE.findall(tex_content))
    has_problems_section = bool(_PROBLEMS_HEADER_RE.search(tex_content))
    return {
        "theorem_envs": len(_THEOREM_ENV_RE.findall(tex_content)),
        "lemma_envs": len(_LEMMA_ENV_RE.findall(tex_content)),
        "definition_envs": len(_DEFINITION_ENV_RE.findall(tex_content)),
        "example_envs": len(_EXAMPLE_ENV_RE.findall(tex_content)),
        "proof_envs": len(_PROOF_ENV_RE.findall(tex_content)),
        "has_problems_section": has_problems_section,
        "problem_items": item_count,
        "numbered_problems": numbered_count,
        "problem_markers": max(item_count if has_problems_section else 0, numbered_count),
    }


def _finding(severity: str, code: str, message: str) -> dict[str, str]:
    return {
        "severity": severity,
        "code": code,
        "message": message,
    }


def validate_phase1_plan_structure(
    *,
    source_plan: str,
    blocks: list[dict[str, Any]],
    tex_content: str,
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    signals = extract_phase1_tex_signals(tex_content)
    findings: list[dict[str, str]] = []

    nonremarks = [block for block in blocks if str(block.get("type", "")).strip() != "Remark"]
    theorem_like = [
        block
        for block in blocks
        if str(block.get("type", "")).strip()
        in {"Theorem_Statement", "Theorem_with_Proof", "Lemma", "Corollary"}
    ]
    problem_like = [block for block in blocks if str(block.get("type", "")).strip() == "Problem"]

    formal_env_total = (
        signals["theorem_envs"]
        + signals["lemma_envs"]
        + signals["definition_envs"]
        + signals["example_envs"]
        + signals["proof_envs"]
    )

    if not blocks:
        findings.append(
            _finding(
                "error",
                "empty_plan",
                f"{source_plan}: no valid blocks remain after normalization.",
            )
        )

    if formal_env_total > 0 and not nonremarks:
        findings.append(
            _finding(
                "error",
                "formal_envs_but_only_remarks",
                f"{source_plan}: input.tex contains formal theorem/definition/example/proof environments, but the plan only contains Remark blocks.",
            )
        )

    if (signals["theorem_envs"] + signals["lemma_envs"]) > 0 and not theorem_like:
        findings.append(
            _finding(
                "error",
                "theorem_envs_without_theorem_tasks",
                f"{source_plan}: input.tex contains theorem or lemma environments, but the plan contains no theorem task blocks.",
            )
        )

    if signals["problem_markers"] >= 2 and not problem_like:
        findings.append(
            _finding(
                "error",
                "problem_items_without_problem_tasks",
                f"{source_plan}: input.tex appears to contain multiple problems, but the plan contains no Problem blocks.",
            )
        )

    return signals, findings


def _load_json_file(path: Path) -> Any:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def _ledger_status_counts_for_source_plan(ledger_path: Path, source_plan: str) -> tuple[int, dict[str, int]]:
    if not ledger_path.exists():
        return 0, {}
    try:
        ledger_payload = _load_json_file(ledger_path)
    except Exception:
        return 0, {}

    tasks = ledger_payload.get("tasks", {}) if isinstance(ledger_payload, dict) else {}
    if not isinstance(tasks, dict):
        return 0, {}

    statuses = Counter(
        str(record.get("status", "<missing>"))
        for record in tasks.values()
        if isinstance(record, dict) and str(record.get("source_plan", "")) == source_plan
    )
    return sum(statuses.values()), dict(statuses)


def _report_status(findings: Iterable[dict[str, str]]) -> str:
    severities = {finding.get("severity", "ok") for finding in findings}
    if "error" in severities:
        return "error"
    if "warning" in severities:
        return "warning"
    return "ok"


def audit_phase1_plan(
    *,
    source_plan: str,
    plan_path: Path,
    input_path: Path,
    ledger_path: Path,
) -> dict[str, Any]:
    findings: list[dict[str, str]] = []
    if not plan_path.exists():
        findings.append(_finding("error", "missing_plan_file", f"{source_plan}: plan file is missing: {plan_path}"))
        return {
            "source_plan": source_plan,
            "plan_entries": 0,
            "remarks": 0,
            "nonremarks": 0,
            "type_counts": {},
            "ledger_entries": 0,
            "ledger_status_counts": {},
            "findings": findings,
            "status": "error",
        }

    if not input_path.exists():
        findings.append(_finding("error", "missing_input_file", f"{source_plan}: input file is missing: {input_path}"))
        return {
            "source_plan": source_plan,
            "plan_entries": 0,
            "remarks": 0,
            "nonremarks": 0,
            "type_counts": {},
            "ledger_entries": 0,
            "ledger_status_counts": {},
            "findings": findings,
            "status": "error",
        }

    plan_payload = _load_json_file(plan_path)
    if not isinstance(plan_payload, list):
        findings.append(_finding("error", "plan_not_list", f"{source_plan}: plan payload must be a JSON list."))
        return {
            "source_plan": source_plan,
            "plan_entries": 0,
            "remarks": 0,
            "nonremarks": 0,
            "type_counts": {},
            "ledger_entries": 0,
            "ledger_status_counts": {},
            "findings": findings,
            "status": "error",
        }

    tex_content = input_path.read_text(encoding="utf-8")
    normalized_blocks: list[dict[str, Any]] = []
    type_counts: Counter[str] = Counter()

    for index, raw_block in enumerate(plan_payload, start=1):
        if not isinstance(raw_block, dict):
            findings.append(
                _finding(
                    "error",
                    "non_object_block",
                    f"{source_plan}: plan entry {index} is not a JSON object.",
                )
            )
            continue

        raw_type = str(raw_block.get("type", "")).strip()
        type_counts[raw_type or "<missing>"] += 1
        normalized_type, note = normalize_phase1_task_type(raw_type)
        if normalized_type is None:
            findings.append(
                _finding(
                    "error",
                    "invalid_task_type",
                    f"{source_plan}: block {raw_block.get('block_id', '<missing>')} uses invalid task type {raw_type!r}.",
                )
            )
            continue
        if note:
            findings.append(
                _finding(
                    "warning",
                    "normalized_task_type",
                    f"{source_plan}: block {raw_block.get('block_id', '<missing>')} uses alias type {raw_type!r}; canonical type is {normalized_type!r}.",
                )
            )

        block = dict(raw_block)
        block["type"] = normalized_type
        normalized_blocks.append(block)

    signals, structure_findings = validate_phase1_plan_structure(
        source_plan=source_plan,
        blocks=normalized_blocks,
        tex_content=tex_content,
    )
    findings.extend(structure_findings)

    ledger_entries, ledger_status_counts = _ledger_status_counts_for_source_plan(ledger_path, source_plan)
    report = {
        "source_plan": source_plan,
        "plan_entries": len(plan_payload),
        "remarks": sum(1 for block in normalized_blocks if str(block.get("type", "")) == "Remark"),
        "nonremarks": sum(1 for block in normalized_blocks if str(block.get("type", "")) != "Remark"),
        "type_counts": dict(type_counts),
        "ledger_entries": ledger_entries,
        "ledger_status_counts": ledger_status_counts,
        "tex_signals": signals,
        "findings": findings,
    }
    report["status"] = _report_status(findings)
    return report


def audit_phase1_plans(
    *,
    plans_dir: Path,
    inputs_dir: Path,
    ledger_path: Path,
    stems: list[str] | None = None,
) -> list[dict[str, Any]]:
    if stems is None:
        stems = sorted(path.name.removesuffix("_plan.json") for path in plans_dir.glob("*_plan.json"))

    reports: list[dict[str, Any]] = []
    for stem in stems:
        reports.append(
            audit_phase1_plan(
                source_plan=stem,
                plan_path=plans_dir / f"{stem}_plan.json",
                input_path=inputs_dir / f"{stem}.tex",
                ledger_path=ledger_path,
            )
        )
    return reports
