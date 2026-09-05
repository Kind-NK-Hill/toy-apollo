from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


REVIEWED_SOURCE_ENV_VARS = {
    "repository": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_REPO",
    "commit": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_COMMIT",
    "lean_prefix": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_LEAN_PREFIX",
    "manifest_path": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_MANIFEST",
    "layout": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_LAYOUT",
    "source_role": "FORMALIZATION_ENGINE_REVIEWED_SOURCE_ROLE",
}


class SourceLocatorError(RuntimeError):
    """Raised when reviewed-source identity cannot be proved exactly."""


def _relative_git_path(value: str, *, field: str) -> str:
    normalized = str(value or "").strip().replace("\\", "/").strip("/")
    if not normalized or normalized in {".", ".."}:
        raise SourceLocatorError(f"Reviewed-source {field} must be a non-empty repository-relative path.")
    if any(part in {"", ".", ".."} for part in normalized.split("/")):
        raise SourceLocatorError(f"Reviewed-source {field} contains an unsafe path segment: {value!r}")
    return normalized


def _git(repo: Path, *args: str) -> str:
    try:
        completed = subprocess.run(
            ["git", *args],
            cwd=str(repo),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SourceLocatorError(f"Unable to inspect reviewed source {repo}: {exc}") from exc
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise SourceLocatorError(
            f"Reviewed-source Git lookup failed in {repo}: git {' '.join(args)}: {detail}"
        )
    return completed.stdout.decode("utf-8", errors="strict").strip()


@dataclass(frozen=True)
class ReviewedSourceLocator:
    repository: Path
    commit: str
    lean_prefix: str
    manifest_path: str
    layout: str
    source_role: str
    policy_path: Path
    repository_identity: str = ""

    def validate(self) -> "ReviewedSourceLocator":
        repository = self.repository.expanduser().resolve()
        if not repository.is_dir():
            raise SourceLocatorError(f"Reviewed-source repository does not exist: {repository}")
        if not re.fullmatch(r"[0-9a-f]{40}", self.commit):
            raise SourceLocatorError(
                f"Reviewed-source commit must be a full lowercase SHA-1 object id: {self.commit!r}"
            )
        if not self.layout.strip() or not self.source_role.strip():
            raise SourceLocatorError("Reviewed-source layout and source_role are required.")
        inside = _git(repository, "rev-parse", "--is-inside-work-tree")
        if inside != "true":
            raise SourceLocatorError(f"Reviewed-source repository is not a Git worktree: {repository}")
        resolved_commit = _git(repository, "rev-parse", f"{self.commit}^{{commit}}")
        if resolved_commit != self.commit:
            raise SourceLocatorError(
                f"Reviewed-source commit resolved unexpectedly: expected {self.commit}, got {resolved_commit}"
            )
        _git(repository, "cat-file", "-e", f"{self.commit}:{self.lean_prefix}")
        _git(repository, "cat-file", "-e", f"{self.commit}:{self.manifest_path}")
        return self

    def as_dict(self) -> dict[str, str]:
        return {
            "repository": str(self.repository),
            "repository_identity": self.repository_identity,
            "commit": self.commit,
            "lean_prefix": self.lean_prefix,
            "manifest_path": self.manifest_path,
            "layout": self.layout,
            "source_role": self.source_role,
            "policy_path": str(self.policy_path),
        }


def _policy_mapping(
    policy_path: Path, *, profile: str = "mat"
) -> tuple[Mapping[str, object] | None, str]:
    try:
        payload = json.loads(policy_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SourceLocatorError(f"Unable to read catalog policy {policy_path}: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise SourceLocatorError(f"Catalog policy must be a JSON object: {policy_path}")
    declared_profile = str(payload.get("profile", "") or "").strip().lower()
    if declared_profile and declared_profile != profile:
        raise SourceLocatorError(
            f"Catalog policy profile {declared_profile!r} does not match runtime profile {profile!r}."
        )
    if profile == "cordis" and ("reviewed_source" in payload or "mat_source" in payload):
        raise SourceLocatorError(
            "Cordis native catalog cannot use MAT reviewed-source mappings."
        )
    reviewed = payload.get("reviewed_source")
    if isinstance(reviewed, Mapping):
        return reviewed, str(payload.get("schema_version", ""))

    # The v1 policy is immutable. This read-only adapter supplies fields that
    # predate the generic locator without rewriting the historical policy bytes.
    legacy = payload.get("mat_source")
    if isinstance(legacy, Mapping):
        adapted = {
            "repository_path": "MAT3280-formalization-output",
            "repository_identity": "Kind-NK-Hill/MAT3280-formalization-output",
            "commit": legacy.get("commit", ""),
            "lean_prefix": "ProbabilityTheory",
            "manifest_path": legacy.get("manifest_path", "manifest_by_chapter.csv"),
            "layout": "probability_theory_manifest_v1",
            "source_role": "legacy_mat_reviewed_source",
        }
        return adapted, str(payload.get("schema_version", ""))
    if (
        profile == "cordis"
        and declared_profile == "cordis"
        and payload.get("schema_version") == "cordis.task-catalog-policy.v1"
        and payload.get("source_kind") == "cordis_modules"
        and isinstance(payload.get("cordis_source"), Mapping)
        and isinstance(payload.get("task_module_map"), Mapping)
    ):
        # Cordis source authority is validated by the catalog loader's pinned
        # commit, paper hashes and module map. It has no MAT-style manifest;
        # do not invent a generic reviewed-source locator for that schema.
        return None, str(payload["schema_version"])
    raise SourceLocatorError(f"Catalog policy has no reviewed_source mapping: {policy_path}")


def load_reviewed_source_locator(
    *,
    workspace_root: Path,
    policy_path: Path,
    environ: Mapping[str, str] | None = None,
    profile: str = "mat",
) -> ReviewedSourceLocator | None:
    environment = os.environ if environ is None else environ
    mapping, _schema = _policy_mapping(policy_path, profile=profile)
    if mapping is None:
        if any(key.startswith("FORMALIZATION_ENGINE_REVIEWED_SOURCE_") for key in environment):
            raise SourceLocatorError(
                "Cordis native catalog source does not support reviewed-source overrides; "
                "use its pinned catalog source configuration."
            )
        return None

    raw_repository = str(
        environment.get(REVIEWED_SOURCE_ENV_VARS["repository"], "")
        or mapping.get("repository_path", "")
    ).strip()
    if not raw_repository:
        raise SourceLocatorError("Reviewed-source repository is not configured.")
    repository = Path(raw_repository).expanduser()
    if not repository.is_absolute():
        repository = workspace_root / repository

    def value(field: str, policy_key: str) -> str:
        return str(
            environment.get(REVIEWED_SOURCE_ENV_VARS[field], "")
            or mapping.get(policy_key, "")
        ).strip()

    commit = value("commit", "commit").lower()
    lean_prefix = _relative_git_path(value("lean_prefix", "lean_prefix"), field="lean_prefix")
    manifest_path = _relative_git_path(
        value("manifest_path", "manifest_path"), field="manifest_path"
    )
    locator = ReviewedSourceLocator(
        repository=repository.resolve(),
        repository_identity=str(mapping.get("repository_identity", "")).strip(),
        commit=commit,
        lean_prefix=lean_prefix,
        manifest_path=manifest_path,
        layout=value("layout", "layout"),
        source_role=value("source_role", "source_role"),
        policy_path=policy_path.resolve(),
    )
    return locator
