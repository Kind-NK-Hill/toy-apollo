"""Per-profile review-version lookup (additive parameterization).

MAT keeps its current supported review versions (prompt 9/10/11 with rubric
9). The Cordis profile starts at prompt 1 / rubric 1. SQL predicates are
generated from the same table so store/migration queries stay consistent.
"""

from __future__ import annotations

from typing import Any

from .core.settings import DEFAULT_PROFILE, profile_spec


def profile_for_catalog(catalog: Any) -> str:
    """Infer the profile from a loaded task catalog.

    Cordis catalogs carry a non-empty multi-homing ``task_module_paths`` map;
    MAT catalogs keep the historical one-to-one ownership and leave it empty.
    """

    return "cordis" if getattr(catalog, "task_module_paths", None) else DEFAULT_PROFILE


def supported_prompt_versions(profile: str = DEFAULT_PROFILE) -> tuple[int, ...]:
    return profile_spec(profile).prompt_versions


def supported_rubric_version(profile: str = DEFAULT_PROFILE) -> int:
    return profile_spec(profile).rubric_version


def prompt_version_sql_predicate(
    profile: str = DEFAULT_PROFILE, column: str = "m.prompt_version"
) -> str:
    versions = ", ".join(str(int(v)) for v in supported_prompt_versions(profile))
    return f"{column} IN ({versions})"


def rubric_version_sql_predicate(
    profile: str = DEFAULT_PROFILE, column: str = "m.rubric_version"
) -> str:
    return f"{column} = {int(supported_rubric_version(profile))}"
