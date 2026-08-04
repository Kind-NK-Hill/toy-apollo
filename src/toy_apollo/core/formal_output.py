from __future__ import annotations

from pathlib import Path
from typing import Iterable

from src.block_id_naming import canonicalize_block_id, extract_chapter


def mat_output_configured(settings) -> bool:
    """Whether this Settings instance uses MAT as the formal Lean owner.

    Directly constructed legacy Settings objects omit ``mat_repo_dir``.  That
    compatibility mode is retained for older isolated tests; ``get_settings``
    always configures MAT.
    """

    return getattr(settings, "mat_repo_dir", None) is not None


def formal_build_root(settings) -> Path:
    configured = getattr(settings, "mat_repo_dir", None)
    if configured is not None:
        return Path(configured)
    return Path(settings.runtime_root)


def formal_output_root(settings) -> Path:
    if mat_output_configured(settings):
        return formal_build_root(settings) / "ProbabilityTheory"
    return Path(settings.toyapollo_output_dir)


def formal_task_module(task_id: str, settings=None) -> str:
    canonical = canonicalize_block_id(task_id)
    if settings is None or not mat_output_configured(settings):
        if not canonical:
            raise ValueError(f"Cannot resolve formal output module for task id: {task_id!r}")
        return f"ToyApollo.Output.{canonical}"
    chapter = extract_chapter(canonical)
    if not canonical or chapter is None:
        raise ValueError(f"Cannot resolve formal output module for task id: {task_id!r}")
    stem = _case_preserved_task_path(canonical, chapter, settings).stem
    return f"ProbabilityTheory.chapter_{chapter:02d}.{stem}"


def formal_task_path(task_id: str, settings) -> Path:
    canonical = canonicalize_block_id(task_id)
    if not mat_output_configured(settings):
        if not canonical:
            raise ValueError(f"Cannot resolve formal output path for task id: {task_id!r}")
        return Path(settings.toyapollo_output_dir) / f"{canonical}.lean"
    chapter = extract_chapter(canonical)
    if not canonical or chapter is None:
        raise ValueError(f"Cannot resolve formal output path for task id: {task_id!r}")
    return _case_preserved_task_path(canonical, chapter, settings)


def official_output_targets(task_id: str, source_plan: str, settings) -> list[Path]:
    """Return formal landing targets.

    MAT-configured production runs have exactly one owner.  Legacy synthetic
    Settings retain the former mirrors so existing low-level tests can model
    historical artifacts without silently changing their fixture contract.
    """

    if mat_output_configured(settings):
        return [formal_task_path(task_id, settings)]

    targets = [
        Path(settings.toyapollo_output_dir) / f"{canonicalize_block_id(task_id)}.lean",
        Path(settings.output_lean_files_dir) / "general" / f"{canonicalize_block_id(task_id)}.lean",
    ]
    if source_plan and source_plan != "unknown":
        targets.append(
            Path(settings.output_lean_files_dir)
            / source_plan
            / f"{canonicalize_block_id(task_id)}.lean"
        )
    return _dedupe(targets)


def formal_scratch_binding(module_basename: str, settings) -> tuple[Path, str]:
    if not mat_output_configured(settings):
        return (
            Path(settings.toyapollo_output_dir) / f"{module_basename}.lean",
            f"ToyApollo.Output.{module_basename}",
        )
    configured = getattr(settings, "lean_scratch_dir", None)
    scratch_root = Path(configured) if configured is not None else formal_output_root(settings) / "Scratch"
    return scratch_root / f"{module_basename}.lean", f"ProbabilityTheory.Scratch.{module_basename}"


def iter_formal_task_files(settings) -> Iterable[Path]:
    root = formal_output_root(settings)
    if not root.exists():
        return []
    if not mat_output_configured(settings):
        return sorted(root.glob("*.lean"))
    return sorted(root.glob("chapter_[0-9][0-9]/*.lean"))


def _dedupe(paths: Iterable[Path]) -> list[Path]:
    deduped: list[Path] = []
    seen: set[Path] = set()
    for path in paths:
        if path in seen:
            continue
        seen.add(path)
        deduped.append(path)
    return deduped


def _case_preserved_task_path(canonical: str, chapter: int, settings) -> Path:
    chapter_root = formal_output_root(settings) / f"chapter_{chapter:02d}"
    if chapter_root.is_dir():
        for candidate in chapter_root.glob("*.lean"):
            if candidate.stem.casefold() == canonical.casefold():
                return candidate
    return chapter_root / f"{canonical}.lean"
