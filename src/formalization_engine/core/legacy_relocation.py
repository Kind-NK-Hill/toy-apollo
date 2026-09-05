from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Mapping


class LegacyRelocationError(RuntimeError):
    """Raised when a historical path cannot be located without guessing."""


def _normalized(value: str | Path) -> str:
    return str(value).replace("\\", "/").rstrip("/")


@dataclass(frozen=True)
class LegacyRelocationEntry:
    recorded_prefix: str
    current_prefix: Path
    role: str


@dataclass(frozen=True)
class LegacyRelocationMap:
    entries: tuple[LegacyRelocationEntry, ...]
    source_path: Path

    @classmethod
    def load(cls, path: str | Path) -> "LegacyRelocationMap":
        source = Path(path).expanduser().resolve()
        try:
            payload = json.loads(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise LegacyRelocationError(f"Unable to read relocation map {source}: {exc}") from exc
        if not isinstance(payload, Mapping):
            raise LegacyRelocationError(f"Relocation map must be a JSON object: {source}")
        if payload.get("schema_version") != "formalization-engine.legacy-evidence-relocation.v1":
            raise LegacyRelocationError(f"Unsupported relocation map schema: {source}")
        if payload.get("mode") != "read_only_existing_targets_only":
            raise LegacyRelocationError(f"Relocation map is not read-only: {source}")
        raw_entries = payload.get("entries")
        if not isinstance(raw_entries, list) or not raw_entries:
            raise LegacyRelocationError(f"Relocation map has no entries: {source}")
        entries: list[LegacyRelocationEntry] = []
        recorded_seen: set[str] = set()
        for raw in raw_entries:
            if not isinstance(raw, Mapping):
                raise LegacyRelocationError(f"Invalid relocation entry: {raw!r}")
            recorded = _normalized(str(raw.get("recorded_prefix", "")))
            current = Path(str(raw.get("current_prefix", ""))).expanduser().resolve()
            role = str(raw.get("role", "")).strip()
            if not recorded or not current.is_absolute() or not role:
                raise LegacyRelocationError(f"Incomplete relocation entry: {raw!r}")
            key = recorded.casefold()
            if key in recorded_seen:
                raise LegacyRelocationError(f"Duplicate recorded prefix: {recorded}")
            recorded_seen.add(key)
            entries.append(LegacyRelocationEntry(recorded, current, role))
        entries.sort(key=lambda entry: len(entry.recorded_prefix), reverse=True)
        return cls(tuple(entries), source)

    def locate(self, recorded_path: str | Path, *, require_exists: bool = True) -> Path:
        raw = _normalized(recorded_path)
        folded = raw.casefold()
        for entry in self.entries:
            prefix = entry.recorded_prefix
            prefix_folded = prefix.casefold()
            if folded != prefix_folded and not folded.startswith(prefix_folded + "/"):
                continue
            suffix = raw[len(prefix) :].lstrip("/")
            parts = PurePosixPath(suffix).parts if suffix else ()
            if any(part in {"", ".", ".."} for part in parts):
                raise LegacyRelocationError(f"Unsafe historical path suffix: {recorded_path}")
            target = entry.current_prefix.joinpath(*parts).resolve()
            root = entry.current_prefix.resolve()
            if target != root and root not in target.parents:
                raise LegacyRelocationError(f"Historical relocation escaped its root: {recorded_path}")
            if require_exists and not target.exists():
                raise LegacyRelocationError(
                    f"Historical path is mapped but its read-only target is missing: {recorded_path} -> {target}"
                )
            return target
        raise LegacyRelocationError(f"Historical path has no explicit relocation entry: {recorded_path}")
