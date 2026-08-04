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
    phase2_prompt_packs_dir: Path
    phase2_softdep_packs_dir: Path
    error_logs_dir: Path
    toyapollo_output_dir: Path
    aristotle_outbox_dir: Path
    aristotle_archives_dir: Path
    mathlib_index_file: Path
    mathlib_corpus_file: Path
    project_ledger_file: Path
    lab_notebook_file: Path
    mathlib_path: Path
    phase0_ingestion_packs_dir: Path | None = None
    phase1_prompt_packs_dir: Path | None = None
    dependency_decisions_dir: Path | None = None
    workspace_root: Path | None = None
    state_db_file: Path | None = None
    # The reviewed Lean source of truth.  Older tests and one-off callers that
    # construct Settings directly may leave this unset; production settings
    # always bind it to the sibling MAT repository.
    mat_repo_dir: Path | None = None
    lean_scratch_dir: Path | None = None


def _to_path(raw: str, fallback: Path) -> Path:
    if not raw:
        return fallback
    p = Path(raw)
    return p if p.is_absolute() else (fallback / p).resolve()


def get_settings() -> Settings:
    cwd = Path(".").resolve()
    runtime_root = _to_path(os.getenv("TOY_APOLLO_RUNTIME_ROOT", ""), cwd)
    artifact_root = _to_path(os.getenv("TOY_APOLLO_ARTIFACT_ROOT", ""), runtime_root)
    workspace_raw = os.getenv("TOY_APOLLO_WORKSPACE_ROOT", "").strip()
    if workspace_raw:
        workspace_path = Path(workspace_raw)
        workspace_root = (
            workspace_path
            if workspace_path.is_absolute()
            else (runtime_root / workspace_path).resolve()
        )
    else:
        workspace_root = runtime_root.parent
    mat_raw = os.getenv("TOY_APOLLO_MAT_REPO_ROOT", "").strip()
    if mat_raw:
        mat_path = Path(mat_raw)
        mat_repo_dir = mat_path if mat_path.is_absolute() else (workspace_root / mat_path).resolve()
    else:
        mat_repo_dir = workspace_root / "MAT3280-formalization-output"
    state_artifact_name = (
        "toy-apollo-artifacts"
        if runtime_root.name.lower() == "toy-apollo"
        else f"{runtime_root.name}-artifacts"
    )
    state_db_file = workspace_root / state_artifact_name / "state.sqlite3"
    return Settings(
        runtime_root=runtime_root,
        artifact_root=artifact_root,
        plans_dir=artifact_root / "plans",
        reports_dir=artifact_root / "reports",
        formalized_chapters_dir=artifact_root / "formalized_chapters",
        output_lean_files_dir=artifact_root / "output_lean_files",
        phase2_prompt_packs_dir=artifact_root / "phase2_prompt_packs",
        phase2_softdep_packs_dir=artifact_root / "phase2_softdep_packs",
        phase1_prompt_packs_dir=artifact_root / "phase1_prompt_packs",
        dependency_decisions_dir=artifact_root / "dependency_decisions",
        error_logs_dir=artifact_root / "error_logs",
        toyapollo_output_dir=runtime_root / "ToyApollo" / "Output",
        aristotle_outbox_dir=artifact_root / "aristotle_outbox",
        aristotle_archives_dir=artifact_root / "aristotle_archives",
        mathlib_index_file=artifact_root / "mathlib_index.faiss",
        mathlib_corpus_file=artifact_root / "mathlib_corpus.json",
        project_ledger_file=artifact_root / "project_ledger.json",
        lab_notebook_file=artifact_root / "lab_notebook.json",
        mathlib_path=runtime_root / ".lake" / "packages" / "mathlib" / "Mathlib",
        phase0_ingestion_packs_dir=artifact_root / "phase0_ingestion_packs",
        workspace_root=workspace_root,
        state_db_file=state_db_file,
        mat_repo_dir=mat_repo_dir,
        lean_scratch_dir=mat_repo_dir / "ProbabilityTheory" / "Scratch",
    )
