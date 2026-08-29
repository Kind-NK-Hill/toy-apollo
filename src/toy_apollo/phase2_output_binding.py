from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id
from src.ledger_manager import LedgerManager


@dataclass(frozen=True)
class Phase2OutputBinding:
    pack_task_id: str
    output_owner_task_id: str
    output_module: str
    pack_dir: Path
    official_targets: list[Path]
    is_obligation_task: bool = False


def resolve_phase2_output_binding(task: dict[str, Any], ledger: LedgerManager, settings) -> Phase2OutputBinding:
    pack_task_id = canonicalize_block_id(str(task.get("block_id", "") or ""))
    record = ledger.ledger.get("tasks", {}).get(pack_task_id, {})
    merged: dict[str, Any] = {}
    if isinstance(record, dict):
        merged.update(record)
    merged.update(task)

    is_obligation = str(merged.get("type", "") or "") == "Phase2ObligationTask"
    owner_raw = ""
    if is_obligation:
        owner_raw = str(
            merged.get("target_task_id", "")
            or merged.get("parent_task_id", "")
            or merged.get("parent_block_id", "")
            or ""
        )
    output_owner_task_id = canonicalize_block_id(owner_raw) if owner_raw else pack_task_id
    if not output_owner_task_id:
        output_owner_task_id = pack_task_id


    from .phase2_pack_shared.artifacts import cordis_task_host_module_name

    official_targets = _official_output_targets(output_owner_task_id, str(merged.get("source_plan", "") or ""), settings)
    output_module = cordis_task_host_module_name(output_owner_task_id, settings)
    if not output_module:
        output_module = f"{getattr(settings, 'lean_module_root', 'ToyApollo.Output')}.{output_owner_task_id}"
    return Phase2OutputBinding(
        pack_task_id=pack_task_id,
        output_owner_task_id=output_owner_task_id,
        output_module=output_module,
        pack_dir=settings.phase2_prompt_packs_dir / pack_task_id,
        official_targets=official_targets,
        is_obligation_task=is_obligation,
    )


def _official_output_targets(task_id: str, source_plan: str, settings) -> list[Path]:
    from .phase2_pack_shared.artifacts import cordis_task_host_module

    host_module = cordis_task_host_module(task_id, settings)
    if host_module is not None:
        return [host_module]
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
