from __future__ import annotations

import hashlib
import json
import re
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, extract_chapter

from .core import LedgerManager
from .dependency_decisions import DependencyDecision, record_dependency_decision
from .phase2_prompt_pack import find_existing_task_file

PROBLEM_TYPE = "problem"
DEFINITION_TYPE_PREFIX = "definition"
THEOREM_TYPE_PREFIX = "theorem"
KNOWN_SELECTION_SCOPE_ALIASES: dict[frozenset[str], str] = {
    frozenset(
        [
            "prob_4_2",
            "prob_4_4",
            "prob_4_8",
            "prob_4_9",
            "prob_4_10",
            "prob_4_11",
            "prob_4_13",
        ]
    ): "ch4_batch1",
    frozenset(["prob_4_1", "prob_4_5", "prob_4_12"]): "ch4_batch2",
    frozenset(["prob_4_3", "prob_4_6", "prob_4_7"]): "ch4_deferred",
}


def _utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _load_plan_tasks(plans_dir: Path) -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []
    for plan_file in sorted(plans_dir.glob("*_plan.json")):
        try:
            payload = json.loads(plan_file.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(payload, list):
            continue
        for raw in payload:
            if not isinstance(raw, dict):
                continue
            task = dict(raw)
            task["source_plan"] = task.get("source_plan") or plan_file.stem.replace("_plan", "")
            task_id = canonicalize_block_id(task.get("block_id"))
            if not task_id:
                continue
            task["block_id"] = task_id
            tasks.append(task)
    return tasks


def _plan_index(plans_dir: Path) -> dict[str, dict[str, Any]]:
    return {task["block_id"]: task for task in _load_plan_tasks(plans_dir)}


def _task_type(task: dict[str, Any]) -> str:
    return str(task.get("type", "")).strip().lower()


def _is_problem_task(task: dict[str, Any]) -> bool:
    return _task_type(task) == PROBLEM_TYPE


def _is_allowed_material_task(task: dict[str, Any]) -> bool:
    task_type = _task_type(task)
    return task_type.startswith(DEFINITION_TYPE_PREFIX) or task_type.startswith(THEOREM_TYPE_PREFIX)


def build_selection_scope_id(task_ids: list[str]) -> str:
    frozen = frozenset(task_ids)
    if frozen in KNOWN_SELECTION_SCOPE_ALIASES:
        return KNOWN_SELECTION_SCOPE_ALIASES[frozen]
    chapter = extract_chapter(task_ids[0]) if task_ids else None
    suffix = "__".join(task_ids)
    stable_suffix = int(hashlib.sha1(suffix.encode("utf-8")).hexdigest()[:12], 16) % 10_000_000
    if chapter is not None:
        return f"ch{chapter}_batch_{stable_suffix:07d}"
    return f"soft_batch_{stable_suffix:07d}"


def _fallback_material_content(material_id: str, source_plan: str, settings) -> str:
    material_path = find_existing_task_file(material_id, source_plan, settings)
    if not material_path:
        return ""
    try:
        return material_path.read_text(encoding="utf-8", errors="replace")[:1200].strip()
    except Exception:
        return ""


def _build_operator_prompt(batch_id: str, chapter: int, problem_ids: list[str]) -> str:
    problem_lines = "\n".join(f"- `{task_id}`" for task_id in problem_ids)
    return "\n".join(
        [
            f"# Soft Dependency Selection Prompt for {batch_id}",
            "",
            f"You are selecting chapter-level soft imports for chapter {chapter} problem tasks.",
            "The result will be consumed by the local operator/Codex workflow before Phase 2 prompt-pack formalization.",
            "",
            "Rules:",
            "1. Output only JSON matching `selection_schema.json`.",
            "2. Select imports only from `allowed_material_ids.json`.",
            "3. `soft imports` are externally selected but mandatory imports once chosen.",
            "4. Optimize for the smallest sufficient import set, not the absolutely smallest list.",
            "5. If a problem is about closure, measurability, or operations, prefer the direct supporting theorem together with the required definitions.",
            "6. Do not select the whole chapter by default; choose only materials that materially support formalization.",
            "7. Prefer chapter-local `def` and `thm` items that directly support the statement.",
            "8. Preserve order by likely usefulness.",
            "9. Do not include explanations inside the JSON output.",
            "",
            "Target problems in this batch:",
            problem_lines,
            "",
            "Read in this order:",
            "1. `problem_statements.md`",
            "2. `selection_hints.md`",
            "3. `chapter_materials.md`",
            "4. `allowed_material_ids.json`",
            "5. `selection_schema.json`",
        ]
    )


def _build_problem_statements(tasks: list[dict[str, Any]]) -> str:
    lines = ["# Problem Statements", ""]
    for task in tasks:
        lines.extend(
            [
                f"## `{task['block_id']}`",
                f"- Type: `{task.get('type', '')}`",
                f"- Title: {task.get('title', '').strip() or '(untitled)'}",
                f"- Source plan: `{task.get('source_plan', 'unknown')}`",
                "",
                task.get("content", "").strip() or "(no content)",
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def _build_chapter_materials(materials: list[dict[str, Any]], settings) -> str:
    lines = ["# Chapter Materials (Allowed Soft Imports)", ""]
    for material in materials:
        block_id = material["block_id"]
        content = material.get("content", "").strip()
        if not content:
            content = _fallback_material_content(block_id, material.get("source_plan", "unknown"), settings) or "(no description available)"
        lines.extend(
            [
                f"## `{block_id}`",
                f"- Type: `{material.get('type', '')}`",
                f"- Title: {material.get('title', '').strip() or '(untitled)'}",
                f"- Source plan: `{material.get('source_plan', 'unknown')}`",
                "",
                content,
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def _selection_schema(problem_ids: list[str]) -> dict[str, Any]:
    return {
        "type": "object",
        "description": "Map each problem block_id to an ordered list of selected soft imports.",
        "required_problem_ids": problem_ids,
        "value_type": "list[str]",
        "allowed_block_ids_source": "allowed_material_ids.json",
        "example": {task_id: [] for task_id in problem_ids},
    }


def _allowed_lookup(materials: list[dict[str, Any]]) -> set[str]:
    return {material["block_id"] for material in materials}


def _recommended_ids_for_problem(task: dict[str, Any], allowed_ids: set[str]) -> list[str]:
    task_id = canonicalize_block_id(task.get("block_id"))
    title = str(task.get("title", "")).lower()
    content = str(task.get("content", "")).lower()
    recommendations: list[str] = []

    def add(*ids: str) -> None:
        for raw_id in ids:
            dep_id = canonicalize_block_id(raw_id)
            if dep_id and dep_id in allowed_ids and dep_id not in recommendations:
                recommendations.append(dep_id)

    has_max_min_ops = re.search(r"(\\max\b|\\min\b|\|f\|)", content) is not None
    if task_id == "prob_4_2" or has_max_min_ops:
        add("thm_4_6", "thm_4_3")
    if task_id == "prob_4_4" or ("complex random variable" in content and "alpha" in content):
        add("def_4_4_complex_random_variable", "def_4_4_complex_operations", "thm_4_3")
    if task_id in {"prob_4_8", "prob_4_9", "prob_4_10", "prob_4_11"} or ("limsup" in content or "liminf" in content):
        add("def_4_3_limsup_liminf")
    if task_id == "prob_4_13" or ("measurable functions" in content and "algebra" in content):
        add("def_4_2", "thm_4_2", "thm_4_4")
    if "continuous" in title or "continuous" in content:
        add("thm_4_5")
    return recommendations


def _build_selection_hints(tasks: list[dict[str, Any]], materials: list[dict[str, Any]]) -> str:
    allowed_ids = _allowed_lookup(materials)
    lines = [
        "# Selection Hints",
        "",
        "These hints are deterministic guidance for the operator. They are not binding, but they are meant to prevent under-selection.",
        "",
        "Selection target:",
        "- choose a minimal but sufficient import set",
        "- prefer direct closure/measurability theorems for proof-oriented problems",
        "- do not optimize for the absolute fewest imports if that would force later local formalization to re-derive obvious chapter results",
        "",
    ]
    for task in tasks:
        task_id = canonicalize_block_id(task["block_id"])
        recommended = _recommended_ids_for_problem(task, allowed_ids)
        lines.append(f"## `{task_id}`")
        if recommended:
            lines.append(f"- Recommended imports: `{', '.join(recommended)}`")
        else:
            lines.append("- Recommended imports: `(no deterministic recommendation)`")
        content = str(task.get("content", "")).lower()
        if task_id == "prob_4_2":
            lines.append("- Reason: this is an operations-on-measurable-functions problem, so the closure theorem is more useful than definitions alone.")
        elif task_id == "prob_4_4":
            lines.append("- Reason: this is a complex-random-variable closure problem, so the complex RV definition and complex operations both matter.")
        elif task_id in {"prob_4_8", "prob_4_9", "prob_4_10", "prob_4_11"}:
            lines.append("- Reason: these are limsup/liminf sequence problems; the core chapter definition is the main reusable support.")
        elif task_id == "prob_4_13":
            lines.append("- Reason: this is about measurable functions between finite measurable spaces, so the measurable-function definition and inverse-image characterizations are the natural chapter tools.")
        elif "continuous" in content:
            lines.append("- Reason: continuity-to-measurability theorems are likely the most direct support.")
        else:
            lines.append("- Reason: no stronger deterministic hint was inferred from the task statement.")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def write_softdep_pack(task_ids: list[str], ledger: LedgerManager, settings) -> Path:
    del ledger
    task_ids = canonicalize_id_list(task_ids)
    if not task_ids:
        raise ValueError("No valid task ids provided for soft-pack.")

    plan_index = _plan_index(settings.plans_dir)
    tasks: list[dict[str, Any]] = []
    for task_id in task_ids:
        task = plan_index.get(task_id)
        if task is None:
            raise FileNotFoundError(f"Task {task_id} was not found in plans/*.json")
        if not _is_problem_task(task):
            raise ValueError(f"soft-pack only supports problem tasks: {task_id}")
        tasks.append(task)

    chapters = {extract_chapter(task['block_id']) for task in tasks}
    if len(chapters) != 1 or None in chapters:
        raise ValueError("soft-pack requires all tasks to belong to the same chapter.")
    chapter = next(iter(chapters))

    materials = [
        task
        for task in plan_index.values()
        if extract_chapter(task["block_id"]) == chapter and _is_allowed_material_task(task)
    ]
    materials.sort(key=lambda item: item["block_id"])

    batch_id = build_selection_scope_id(task_ids)
    pack_dir = settings.phase2_softdep_packs_dir / batch_id
    pack_dir.mkdir(parents=True, exist_ok=True)

    batch_payload = {
        "batch_id": batch_id,
        "chapter": chapter,
        "problem_ids": task_ids,
        "source_plans": sorted({task.get("source_plan", "unknown") for task in tasks}),
        "generated_at": _utc_stamp(),
    }
    allowed_ids = [material["block_id"] for material in materials]
    schema_payload = _selection_schema(task_ids)

    (pack_dir / "batch.json").write_text(json.dumps(batch_payload, indent=2, ensure_ascii=False), encoding="utf-8")
    (pack_dir / "operator_prompt.md").write_text(_build_operator_prompt(batch_id, chapter, task_ids), encoding="utf-8")
    (pack_dir / "problem_statements.md").write_text(_build_problem_statements(tasks), encoding="utf-8")
    (pack_dir / "selection_hints.md").write_text(_build_selection_hints(tasks, materials), encoding="utf-8")
    (pack_dir / "chapter_materials.md").write_text(_build_chapter_materials(materials, settings), encoding="utf-8")
    (pack_dir / "allowed_material_ids.json").write_text(json.dumps(allowed_ids, indent=2, ensure_ascii=False), encoding="utf-8")
    (pack_dir / "selection_schema.json").write_text(json.dumps(schema_payload, indent=2, ensure_ascii=False), encoding="utf-8")
    if not (pack_dir / "soft_imports_selection.json").exists():
        (pack_dir / "soft_imports_selection.json").write_text(
            json.dumps(schema_payload["example"], indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
    if not (pack_dir / "apply_report.md").exists():
        (pack_dir / "apply_report.md").write_text(f"# Apply Report for {batch_id}\n\n", encoding="utf-8")
    return pack_dir


def _append_apply_report(pack_dir: Path, lines: list[str]) -> None:
    report_path = pack_dir / "apply_report.md"
    with open(report_path, "a", encoding="utf-8") as f:
        f.write(f"## Apply {_utc_stamp()}\n\n")
        for line in lines:
            f.write(line.rstrip() + "\n")
        f.write("\n")


def _load_soft_import_rationales(pack_dir: Path) -> dict[str, dict[str, str]]:
    rationale_path = pack_dir / "soft_imports_rationale.json"
    if not rationale_path.exists():
        return {}
    payload = json.loads(rationale_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        return {}
    rationales: dict[str, dict[str, str]] = {}
    for raw_task_id, raw_dep_map in payload.items():
        task_id = canonicalize_block_id(str(raw_task_id))
        if not task_id or not isinstance(raw_dep_map, dict):
            continue
        dep_map: dict[str, str] = {}
        for raw_dep_id, raw_evidence in raw_dep_map.items():
            dep_id = canonicalize_block_id(str(raw_dep_id))
            if dep_id:
                dep_map[dep_id] = str(raw_evidence or "")
        rationales[task_id] = dep_map
    return rationales


def apply_softdep_selection(task_ids: list[str], ledger: LedgerManager, settings, selection_path: str) -> tuple[bool, str, Path]:
    task_ids = canonicalize_id_list(task_ids)
    if not task_ids:
        raise ValueError("No valid task ids provided for soft-apply.")

    batch_id = build_selection_scope_id(task_ids)
    pack_dir = settings.phase2_softdep_packs_dir / batch_id
    if not pack_dir.exists():
        raise FileNotFoundError(f"Soft dependency pack does not exist: {pack_dir}")

    resolved_selection_path = Path(selection_path).expanduser()
    if not resolved_selection_path.is_absolute():
        resolved_selection_path = (Path.cwd() / resolved_selection_path).resolve()
    if not resolved_selection_path.exists():
        raise FileNotFoundError(f"Selection file not found: {resolved_selection_path}")

    payload = json.loads(resolved_selection_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("Selection JSON must be an object mapping problem ids to soft import lists.")

    allowed_ids = set(json.loads((pack_dir / "allowed_material_ids.json").read_text(encoding="utf-8")))
    expected_ids = set(task_ids)
    received_ids = {canonicalize_block_id(key) for key in payload.keys()}
    if received_ids != expected_ids:
        missing = sorted(expected_ids - received_ids)
        extra = sorted(received_ids - expected_ids)
        raise ValueError(f"Selection JSON keys mismatch. missing={missing} extra={extra}")

    normalized_payload: dict[str, list[str]] = {}
    report_lines: list[str] = []
    rationales = _load_soft_import_rationales(pack_dir)
    for raw_task_id, raw_soft_imports in payload.items():
        task_id = canonicalize_block_id(raw_task_id)
        if not isinstance(raw_soft_imports, list):
            raise ValueError(f"Selection for {task_id} must be a list.")
        normalized = canonicalize_id_list(raw_soft_imports)
        invalid = [item for item in normalized if item not in allowed_ids]
        if invalid:
            raise ValueError(f"Selection for {task_id} contains invalid material ids: {invalid}")
        normalized_payload[task_id] = normalized
        ledger.update_candidate_soft_imports(task_id, normalized)
        ledger.mark_soft_imports_confirmed(task_id, normalized)
        source_plan = ""
        task_record = ledger.ledger.get("tasks", {}).get(task_id, {})
        if isinstance(task_record, dict):
            source_plan = str(task_record.get("source_plan", "") or "")
        for dep_id in normalized:
            evidence = rationales.get(task_id, {}).get(dep_id) or "Selected in soft_imports_selection.json"
            record_dependency_decision(
                settings,
                DependencyDecision(
                    task_id=task_id,
                    dep_id=dep_id,
                    kind="soft",
                    phase="phase2_soft_apply",
                    criterion="soft_minimal_sufficient",
                    evidence=evidence,
                    source_plan=source_plan,
                    source_file=str(resolved_selection_path),
                ),
            )
        report_lines.append(f"- `{task_id}` -> `{', '.join(normalized) if normalized else '(none)'}`")

    (pack_dir / "soft_imports_selection.json").write_text(
        json.dumps(normalized_payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    _append_apply_report(pack_dir, report_lines)
    return True, "Soft imports applied successfully.", pack_dir
