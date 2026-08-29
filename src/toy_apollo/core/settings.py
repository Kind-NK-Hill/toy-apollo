from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path


DEFAULT_RUNTIME_ROOT = Path(__file__).resolve().parents[3]

DEFAULT_PROFILE = "mat"


@dataclass(frozen=True)
class ProfileSpec:
    """Per-profile engine parameters (additive; MAT keeps its current behavior)."""

    profile: str
    lean_module_root: str
    output_subdir: str
    prompt_versions: tuple[int, ...]
    rubric_version: int
    legacy_obligation_review_prompt_versions: tuple[int, ...]


PROFILE_SPECS: dict[str, ProfileSpec] = {
    "mat": ProfileSpec(
        profile="mat",
        lean_module_root="ToyApollo.Output",
        output_subdir="ToyApollo/Output",
        prompt_versions=(9, 10, 11),
        rubric_version=9,
        legacy_obligation_review_prompt_versions=(9, 10),
    ),
    "cordis": ProfileSpec(
        profile="cordis",
        lean_module_root="Cordis.Foundations",
        output_subdir="Cordis/Foundations",
        prompt_versions=(1,),
        rubric_version=1,
        legacy_obligation_review_prompt_versions=(),
    ),
}


def resolve_profile(runtime_root: Path | None = None) -> str:
    """Resolve the active engine profile.

    The default profile is MAT (current behavior). The Cordis profile is
    selected when the runtime root is the `cordis` repository or when
    TOY_APOLLO_PROFILE=cordis is set explicitly.
    """

    override = str(os.getenv("TOY_APOLLO_PROFILE", "") or "").strip().lower()
    if override:
        return override if override in PROFILE_SPECS else DEFAULT_PROFILE
    if runtime_root is not None and str(Path(runtime_root).name).lower() == "cordis":
        return "cordis"
    return DEFAULT_PROFILE


def profile_spec(profile: str = DEFAULT_PROFILE) -> ProfileSpec:
    return PROFILE_SPECS.get(str(profile or DEFAULT_PROFILE).strip().lower() or DEFAULT_PROFILE, PROFILE_SPECS[DEFAULT_PROFILE])


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
    profile: str = DEFAULT_PROFILE
    lean_module_root: str = PROFILE_SPECS[DEFAULT_PROFILE].lean_module_root
    output_subdir: str = PROFILE_SPECS[DEFAULT_PROFILE].output_subdir
    lean_module_dir: Path | None = None
    supported_prompt_versions: tuple[int, ...] = PROFILE_SPECS[DEFAULT_PROFILE].prompt_versions
    supported_rubric_version: int = PROFILE_SPECS[DEFAULT_PROFILE].rubric_version


def _to_path(raw: str, fallback: Path) -> Path:
    if not raw:
        return fallback
    p = Path(raw)
    return p if p.is_absolute() else (fallback / p).resolve()


def get_settings() -> Settings:
    runtime_root = _to_path(
        os.getenv("TOY_APOLLO_RUNTIME_ROOT", ""), DEFAULT_RUNTIME_ROOT
    ).resolve()
    artifact_root = _to_path(os.getenv("TOY_APOLLO_ARTIFACT_ROOT", ""), runtime_root)
    workspace_root = runtime_root.parent
    state_artifact_name = (
        "toy-apollo-artifacts"
        if runtime_root.name.lower() == "toy-apollo"
        else f"{runtime_root.name}-artifacts"
    )
    state_db_file = workspace_root / state_artifact_name / "state.sqlite3"
    active_profile = resolve_profile(runtime_root)
    spec = profile_spec(active_profile)
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
        profile=active_profile,
        lean_module_root=spec.lean_module_root,
        output_subdir=spec.output_subdir,
        lean_module_dir=runtime_root / Path(spec.output_subdir),
        supported_prompt_versions=spec.prompt_versions,
        supported_rubric_version=spec.rubric_version,
    )
