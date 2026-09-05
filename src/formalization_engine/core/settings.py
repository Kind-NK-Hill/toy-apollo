from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

from .source_locator import ReviewedSourceLocator, load_reviewed_source_locator


DEFAULT_RUNTIME_ROOT = Path(__file__).resolve().parents[3]

DEFAULT_WORKSPACE_ROOT = DEFAULT_RUNTIME_ROOT.parent
DEFAULT_ARTIFACT_REPOSITORY_NAME = "ProbabilityTheoryFormalization-artifacts"
DEFAULT_CATALOG_POLICY = Path("data/task_catalog/catalog_policy_v2.json")
CORDIS_CATALOG_POLICY = Path("data/task_catalog/catalog_policy_v1.json")

RUNTIME_ROOT_ENV_VAR = "FORMALIZATION_ENGINE_RUNTIME_ROOT"
WORKSPACE_ROOT_ENV_VAR = "FORMALIZATION_ENGINE_WORKSPACE_ROOT"
ARTIFACT_ROOT_ENV_VAR = "FORMALIZATION_ENGINE_ARTIFACT_ROOT"
STATE_DB_ENV_VAR = "FORMALIZATION_ENGINE_STATE_DB"
CATALOG_POLICY_ENV_VAR = "FORMALIZATION_ENGINE_CATALOG_POLICY"
PROFILE_ENV_VAR = "FORMALIZATION_ENGINE_PROFILE"

DEFAULT_PROFILE = "mat"


@dataclass(frozen=True)
class ProfileSpec:
    """Per-profile Formalization Engine parameters."""

    profile: str
    lean_module_root: str
    output_subdir: str
    prompt_versions: tuple[int, ...]
    rubric_version: int
    legacy_obligation_review_prompt_versions: tuple[int, ...]
    artifact_repository_name: str = DEFAULT_ARTIFACT_REPOSITORY_NAME
    catalog_policy: Path = DEFAULT_CATALOG_POLICY


PROFILE_SPECS: dict[str, ProfileSpec] = {
    "mat": ProfileSpec(
        profile="mat",
        lean_module_root="ProbabilityTheory",
        output_subdir="ProbabilityTheory",
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
        artifact_repository_name="cordis-artifacts",
        catalog_policy=CORDIS_CATALOG_POLICY,
    ),
}


def resolve_profile(runtime_root: Path | None = None) -> str:
    """Resolve the active engine profile.

    The default profile is MAT (current behavior). The Cordis profile is
    selected when the runtime root is the `cordis` repository or when
    FORMALIZATION_ENGINE_PROFILE=cordis is set explicitly.
    """

    override = str(os.getenv(PROFILE_ENV_VAR, "") or "").strip().lower()
    if override:
        return profile_spec(override).profile
    if runtime_root is not None and str(Path(runtime_root).name).lower() == "cordis":
        return "cordis"
    return DEFAULT_PROFILE


def profile_spec(profile: str = DEFAULT_PROFILE) -> ProfileSpec:
    name = str(profile or DEFAULT_PROFILE).strip().lower() or DEFAULT_PROFILE
    try:
        return PROFILE_SPECS[name]
    except KeyError as exc:
        raise SettingsError(
            f"Unsupported engine profile {name!r}; expected one of {', '.join(PROFILE_SPECS)}."
        ) from exc


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
    canonical_lean_dir: Path
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
    catalog_policy_file: Path | None = None
    reviewed_source: ReviewedSourceLocator | None = None
    canonical_manifest_required: bool = True


class SettingsError(RuntimeError):
    """Raised when explicit runtime path configuration is incomplete or unsafe."""


def _resolve_path(raw: str, *, default: Path, relative_to: Path) -> Path:
    candidate = Path(raw).expanduser() if raw else default
    if not candidate.is_absolute():
        candidate = relative_to / candidate
    return candidate.resolve()


def get_settings() -> Settings:
    runtime_root = _resolve_path(
        os.getenv(RUNTIME_ROOT_ENV_VAR, ""),
        default=DEFAULT_RUNTIME_ROOT,
        relative_to=DEFAULT_WORKSPACE_ROOT,
    )
    if not runtime_root.is_dir():
        raise SettingsError(f"Configured runtime root does not exist: {runtime_root}")
    workspace_root = _resolve_path(
        os.getenv(WORKSPACE_ROOT_ENV_VAR, ""),
        default=runtime_root.parent,
        relative_to=runtime_root.parent,
    )
    if not workspace_root.is_dir():
        raise SettingsError(f"Configured workspace root does not exist: {workspace_root}")
    active_profile = resolve_profile(runtime_root)
    spec = profile_spec(active_profile)
    artifact_root = _resolve_path(
        os.getenv(ARTIFACT_ROOT_ENV_VAR, ""),
        default=workspace_root / spec.artifact_repository_name,
        relative_to=workspace_root,
    )
    state_db_file = _resolve_path(
        os.getenv(STATE_DB_ENV_VAR, ""),
        default=artifact_root / "state.sqlite3",
        relative_to=artifact_root,
    )
    if state_db_file.parent != artifact_root:
        raise SettingsError(
            f"Configured state database must be the direct state file of artifact root {artifact_root}: "
            f"{state_db_file}"
        )
    catalog_policy_file = _resolve_path(
        os.getenv(CATALOG_POLICY_ENV_VAR, ""),
        default=runtime_root / spec.catalog_policy,
        relative_to=runtime_root,
    )
    reviewed_source = None
    locator_env_present = any(
        key.startswith("FORMALIZATION_ENGINE_REVIEWED_SOURCE_") for key in os.environ
    )
    if catalog_policy_file.is_file() or locator_env_present:
        reviewed_source = load_reviewed_source_locator(
            workspace_root=workspace_root,
            policy_path=catalog_policy_file,
            profile=active_profile,
        )
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
        canonical_lean_dir=runtime_root / spec.output_subdir,
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
        catalog_policy_file=catalog_policy_file,
        reviewed_source=reviewed_source,
    )
