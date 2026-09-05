from __future__ import annotations

import csv
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


class CanonicalResolverError(RuntimeError):
    """Raised when a canonical Lean path or module is absent or ambiguous."""


@dataclass(frozen=True)
class CanonicalLeanEntry:
    basename: str
    relative_path: str
    module_name: str
    classification: str


class CanonicalLeanResolver:
    def __init__(
        self,
        runtime_root: Path,
        entries: tuple[CanonicalLeanEntry, ...],
        *,
        fallback_relative_root: str = "",
    ):
        self.runtime_root = runtime_root.resolve()
        self.entries = entries
        self._fallback_relative_root = fallback_relative_root.strip("/")
        self._by_basename = {entry.basename.lower(): entry for entry in entries}
        self._by_module = {entry.module_name: entry for entry in entries}
        if len(self._by_basename) != len(entries):
            raise CanonicalResolverError("Canonical manifest contains duplicate basenames.")
        if len(self._by_module) != len(entries):
            raise CanonicalResolverError("Canonical manifest contains duplicate module names.")

    @classmethod
    def from_directory(
        cls,
        runtime_root: Path,
        canonical_lean_dir: Path,
    ) -> "CanonicalLeanResolver":
        """Build an unpinned resolver only for explicitly opted-in test fixtures."""

        runtime_root = runtime_root.resolve()
        canonical_lean_dir = canonical_lean_dir.resolve()
        entries: list[CanonicalLeanEntry] = []
        for path in sorted(canonical_lean_dir.rglob("*.lean")):
            relative_path = path.resolve().relative_to(runtime_root).as_posix()
            module_name = ".".join(Path(relative_path).with_suffix("").parts)
            entries.append(
                CanonicalLeanEntry(
                    path.stem,
                    relative_path,
                    module_name,
                    "test_fixture",
                )
            )
        fallback_relative_root = canonical_lean_dir.relative_to(runtime_root).as_posix()
        return cls(
            runtime_root,
            tuple(entries),
            fallback_relative_root=fallback_relative_root,
        )

    @classmethod
    def load(
        cls,
        runtime_root: Path,
        manifest_path: Path | None = None,
    ) -> "CanonicalLeanResolver":
        runtime_root = runtime_root.resolve()
        manifest_path = (manifest_path or runtime_root / "manifest_by_chapter.csv").resolve()
        try:
            with manifest_path.open("r", encoding="utf-8-sig", newline="") as handle:
                rows = list(csv.DictReader(handle))
        except OSError as exc:
            raise CanonicalResolverError(
                f"Unable to read canonical Lean manifest {manifest_path}: {exc}"
            ) from exc
        entries: list[CanonicalLeanEntry] = []
        for row in rows:
            basename = str(row.get("basename", "") or "").strip()
            relative_path = str(row.get("file_path", "") or "").strip().replace("\\", "/")
            module_name = str(row.get("module_name", "") or "").strip()
            classification = str(row.get("classification", "") or "").strip()
            if not basename or not relative_path or not module_name:
                raise CanonicalResolverError("Canonical manifest contains an incomplete row.")
            if not relative_path.startswith("ProbabilityTheory/") or not relative_path.endswith(".lean"):
                raise CanonicalResolverError(
                    f"Canonical manifest path is outside ProbabilityTheory: {relative_path}"
                )
            if not module_name.startswith("ProbabilityTheory."):
                raise CanonicalResolverError(
                    f"Canonical manifest module is outside ProbabilityTheory: {module_name}"
                )
            entries.append(
                CanonicalLeanEntry(
                    basename,
                    relative_path,
                    module_name,
                    classification,
                )
            )
        if not entries:
            raise CanonicalResolverError("Canonical manifest contains no Lean entries.")
        return cls(runtime_root, tuple(entries))

    def entry_for_basename(self, basename: str) -> CanonicalLeanEntry:
        key = str(basename or "").strip().removesuffix(".lean").lower()
        try:
            return self._by_basename[key]
        except KeyError as exc:
            if self._fallback_relative_root:
                relative_path = f"{self._fallback_relative_root}/{key}.lean"
                return CanonicalLeanEntry(
                    key,
                    relative_path,
                    ".".join(Path(relative_path).with_suffix("").parts),
                    "test_fixture",
                )
            raise CanonicalResolverError(
                f"Canonical Lean basename is not present in the manifest: {basename!r}"
            ) from exc

    def path_for_basename(self, basename: str, *, require_file: bool = True) -> Path:
        path = (self.runtime_root / self.entry_for_basename(basename).relative_path).resolve()
        if require_file and not path.is_file():
            raise CanonicalResolverError(f"Canonical Lean file is missing: {path}")
        return path

    def module_for_basename(self, basename: str) -> str:
        return self.entry_for_basename(basename).module_name

    def entry_for_module(self, module_name: str) -> CanonicalLeanEntry:
        normalized = str(module_name or "").strip()
        try:
            return self._by_module[normalized]
        except KeyError as exc:
            fallback_module_root = self._fallback_relative_root.replace("/", ".")
            if fallback_module_root and normalized.startswith(f"{fallback_module_root}."):
                relative_path = normalized.replace(".", "/") + ".lean"
                return CanonicalLeanEntry(
                    normalized.rsplit(".", 1)[-1],
                    relative_path,
                    normalized,
                    "test_fixture",
                )
            raise CanonicalResolverError(
                f"Canonical Lean module is not present in the manifest: {module_name!r}"
            ) from exc


@lru_cache(maxsize=8)
def canonical_resolver(runtime_root: str | Path) -> CanonicalLeanResolver:
    return CanonicalLeanResolver.load(Path(runtime_root))


def canonical_resolver_for_settings(settings: object) -> CanonicalLeanResolver:
    manifest_required = bool(getattr(settings, "canonical_manifest_required", True))
    raw_runtime_root = getattr(settings, "runtime_root", None)
    if raw_runtime_root is None:
        if manifest_required:
            raise CanonicalResolverError("Settings lack a required runtime_root.")
        raw_runtime_root = Path(getattr(settings, "canonical_lean_dir")).resolve().parent
    runtime_root = Path(raw_runtime_root).resolve()
    manifest_path = runtime_root / "manifest_by_chapter.csv"
    if manifest_path.is_file():
        return canonical_resolver(runtime_root)
    if manifest_required:
        raise CanonicalResolverError(
            f"Canonical manifest is required but missing: {manifest_path}"
        )
    return CanonicalLeanResolver.from_directory(
        runtime_root,
        Path(getattr(settings, "canonical_lean_dir")),
    )
