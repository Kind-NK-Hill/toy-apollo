from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Settings:
    runtime_root: Path
    artifact_root: Path
    plans_dir: Path
    reports_dir: Path
    formalized_chapters_dir: Path
    output_lean_files_dir: Path
    error_logs_dir: Path
    toyapollo_output_dir: Path
    aristotle_outbox_dir: Path
    aristotle_archives_dir: Path
    mathlib_index_file: Path
    mathlib_corpus_file: Path
    project_ledger_file: Path
    lab_notebook_file: Path
    mathlib_path: Path


def _to_path(raw: str, fallback: Path) -> Path:
    if not raw:
        return fallback
    p = Path(raw)
    return p if p.is_absolute() else (fallback / p).resolve()


def get_settings() -> Settings:
    cwd = Path(".").resolve()
    runtime_root = _to_path(os.getenv("TOY_APOLLO_RUNTIME_ROOT", ""), cwd)
    artifact_root = _to_path(os.getenv("TOY_APOLLO_ARTIFACT_ROOT", ""), runtime_root)
    return Settings(
        runtime_root=runtime_root,
        artifact_root=artifact_root,
        plans_dir=artifact_root / "plans",
        reports_dir=artifact_root / "reports",
        formalized_chapters_dir=artifact_root / "formalized_chapters",
        output_lean_files_dir=artifact_root / "output_lean_files",
        error_logs_dir=artifact_root / "error_logs",
        toyapollo_output_dir=runtime_root / "ToyApollo" / "Output",
        aristotle_outbox_dir=artifact_root / "aristotle_outbox",
        aristotle_archives_dir=artifact_root / "aristotle_archives",
        mathlib_index_file=artifact_root / "mathlib_index.faiss",
        mathlib_corpus_file=artifact_root / "mathlib_corpus.json",
        project_ledger_file=artifact_root / "project_ledger.json",
        lab_notebook_file=artifact_root / "lab_notebook.json",
        mathlib_path=runtime_root / ".lake" / "packages" / "mathlib" / "Mathlib",
    )

