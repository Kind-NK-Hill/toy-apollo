from __future__ import annotations

import json
import re
from functools import lru_cache
from pathlib import Path
from typing import Iterable

_ALIAS_PATH = Path(__file__).with_name("block_id_aliases.json")
_IDENTIFIER_RE = re.compile(r"^[a-z0-9_]+$")
_BASE_PREFIX_RE = re.compile(r"^(intro|rem|def|thm|ex|prob)_(\d+)(?:_|$)")
_BASE_PATTERNS = (
    re.compile(r"^intro_\d+(?:_\d+)?$"),
    re.compile(r"^rem_\d+_\d+_[a-z0-9]+(?:_[a-z0-9]+)*$"),
    re.compile(r"^def_\d+_\d+(?:_[a-z0-9]+(?:_[a-z0-9]+)*)?$"),
    re.compile(r"^thm_\d+_\d+$"),
    re.compile(r"^ex_\d+_\d+_(?:\d+|[a-z0-9]+(?:_[a-z0-9]+)*)$"),
    re.compile(r"^prob_\d+_\d+$"),
)
_DERIVED_SEGMENT_RE = re.compile(r"__(lemma_(\d+)|main)")
_TOKEN_SEGMENT_RE = re.compile(r"(lemma_(\d+)|main)")
_RESERVED_SUFFIX_TOKENS = {"lemma", "main", "proof", "task", "parent", "after", "before", "step"}


def _normalize_identifier(block_id: str) -> str:
    normalized = str(block_id or "").strip().lower().replace("-", "_").replace(" ", "_")
    if "__" not in normalized:
        normalized = re.sub(r"_+", "_", normalized)
        return normalized.strip("_")

    parts = [re.sub(r"_+", "_", part).strip("_") for part in normalized.split("__")]
    return "__".join([part for part in parts if part])


@lru_cache(maxsize=1)
def alias_map() -> dict[str, str]:
    if not _ALIAS_PATH.exists():
        return {}
    with open(_ALIAS_PATH, "r", encoding="utf-8") as f:
        data = json.load(f)
    aliases: dict[str, str] = {}
    if isinstance(data, dict):
        for raw_key, raw_value in data.items():
            key = _normalize_identifier(raw_key)
            value = _normalize_identifier(raw_value)
            if key and value:
                aliases[key] = value
    return aliases


@lru_cache(maxsize=1)
def inverse_alias_map() -> dict[str, tuple[str, ...]]:
    inverted: dict[str, list[str]] = {}
    for legacy, canonical in alias_map().items():
        inverted.setdefault(canonical, []).append(legacy)
    return {canonical: tuple(sorted(values)) for canonical, values in inverted.items()}


def legacy_ids_for(block_id: str) -> tuple[str, ...]:
    canonical = resolve_alias(block_id)
    return inverse_alias_map().get(canonical, ())


def normalize_legacy_id_list(raw_ids: Iterable[str] | object) -> list[str]:
    if not isinstance(raw_ids, Iterable) or isinstance(raw_ids, (str, bytes, dict)):
        return []
    ordered: list[str] = []
    seen: set[str] = set()
    for raw_id in raw_ids:
        if not isinstance(raw_id, str):
            continue
        normalized = _normalize_identifier(raw_id)
        if not normalized or normalized in seen:
            continue
        seen.add(normalized)
        ordered.append(normalized)
    return ordered


def resolve_alias(block_id: str) -> str:
    resolved = _normalize_identifier(block_id)
    if not resolved:
        return ""
    seen: set[str] = set()
    aliases = alias_map()
    while resolved in aliases and resolved not in seen:
        seen.add(resolved)
        resolved = aliases[resolved]
    return resolved


def is_canonical_base_id(block_id: str) -> bool:
    normalized = _normalize_identifier(block_id)
    if not normalized or not _IDENTIFIER_RE.match(normalized):
        return False
    if re.search(r"(?:^|_)(?:lemma|main|proof|task|parent|after|before|step)(?:_|$)", normalized):
        return False
    return any(pattern.match(normalized) for pattern in _BASE_PATTERNS)


def _split_canonical_derived(block_id: str) -> tuple[str, list[str]] | None:
    normalized = _normalize_identifier(block_id)
    if "__" not in normalized:
        return None
    base, _, remainder = normalized.partition("__")
    if not is_canonical_base_id(base):
        return None
    suffixes: list[str] = []
    cursor = "__" + remainder
    pos = 0
    while pos < len(cursor):
        match = _DERIVED_SEGMENT_RE.match(cursor, pos)
        if not match:
            return None
        suffix = match.group(1)
        if suffix == "main" and pos + len(match.group(0)) != len(cursor):
            return None
        suffixes.append(suffix)
        pos = match.end()
    return base, suffixes


def is_canonical_block_id(block_id: str) -> bool:
    normalized = _normalize_identifier(block_id)
    if is_canonical_base_id(normalized):
        return True
    return _split_canonical_derived(normalized) is not None


def _parse_legacy_suffixes(tokens: list[str]) -> list[str]:
    suffixes: list[str] = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token == "lemma" and i + 1 < len(tokens) and tokens[i + 1].isdigit():
            suffixes.append(f"lemma_{tokens[i + 1]}")
            i += 2
            continue
        if token == "main":
            suffixes.append("main")
            i += 1
            continue
        if token == "step" and i + 1 < len(tokens) and tokens[i + 1].isdigit():
            suffixes.append(f"lemma_{tokens[i + 1]}")
            i += 2
            continue
        i += 1
    return suffixes


def _legacy_root_candidates(normalized: str) -> list[str]:
    tokens = normalized.split("_")
    candidates: list[str] = []
    for i in range(len(tokens), 0, -1):
        prefix = "_".join(tokens[:i])
        candidates.append(prefix)
    return candidates


def canonicalize_block_id(block_id: str) -> str:
    normalized = _normalize_identifier(block_id)
    if not normalized:
        return ""

    resolved = resolve_alias(normalized)
    if is_canonical_block_id(resolved):
        return resolved

    split = _split_canonical_derived(resolved)
    if split is not None:
        base, suffixes = split
        return base + "".join(f"__{suffix}" for suffix in suffixes)

    for prefix in _legacy_root_candidates(resolved):
        canonical_prefix = resolve_alias(prefix)
        if not is_canonical_base_id(canonical_prefix):
            continue
        suffix_tokens = resolved.split("_")[len(prefix.split("_")) :]
        suffixes = _parse_legacy_suffixes(suffix_tokens)
        if suffixes:
            return canonical_prefix + "".join(f"__{suffix}" for suffix in suffixes)
        return canonical_prefix

    return resolved


def canonicalize_id_list(raw_ids: Iterable[str] | object) -> list[str]:
    if not isinstance(raw_ids, Iterable) or isinstance(raw_ids, (str, bytes, dict)):
        return []
    ordered: list[str] = []
    seen: set[str] = set()
    for raw_id in raw_ids:
        if not isinstance(raw_id, str):
            continue
        canonical = canonicalize_block_id(raw_id)
        if not canonical or canonical in seen:
            continue
        seen.add(canonical)
        ordered.append(canonical)
    return ordered


def extract_chapter(block_id: str) -> int | None:
    canonical = canonicalize_block_id(block_id)
    if not canonical:
        return None
    base = canonical.split("__", 1)[0]
    match = _BASE_PREFIX_RE.match(base)
    if not match:
        return None
    try:
        return int(match.group(2))
    except (TypeError, ValueError):
        return None


def is_def_or_thm_block_id(block_id: str) -> bool:
    canonical = canonicalize_block_id(block_id)
    if not canonical:
        return False
    base = canonical.split("__", 1)[0]
    return base.startswith(("def_", "thm_"))


def is_problem_block_id(block_id: str) -> bool:
    canonical = canonicalize_block_id(block_id)
    if not canonical:
        return False
    return canonical.split("__", 1)[0].startswith("prob_")


def is_derived_block_id(block_id: str) -> bool:
    return "__" in canonicalize_block_id(block_id)


def parent_block_id(block_id: str) -> str | None:
    canonical = canonicalize_block_id(block_id)
    split = _split_canonical_derived(canonical)
    if split is None:
        return None
    parts = canonical.split("__")
    if len(parts) <= 2:
        return parts[0]
    return "__".join(parts[:-1])


def base_block_id(block_id: str) -> str:
    canonical = canonicalize_block_id(block_id)
    return canonical.split("__", 1)[0] if canonical else ""


def make_derived_id(base_id: str, kind: str, index_path: int | Iterable[int] | None = None) -> str:
    parent = canonicalize_block_id(base_id)
    if not parent or not is_canonical_block_id(parent):
        raise ValueError(f"invalid_parent_block_id:{base_id}")

    normalized_kind = str(kind or "").strip().lower()
    if normalized_kind == "main":
        return f"{parent}__main"
    if normalized_kind != "lemma":
        raise ValueError(f"invalid_derived_kind:{kind}")

    if isinstance(index_path, int):
        indices = [index_path]
    elif index_path is None:
        raise ValueError("lemma_index_path_required")
    else:
        indices = [int(i) for i in index_path]

    derived = parent
    for index in indices:
        if index <= 0:
            raise ValueError(f"invalid_lemma_index:{index}")
        derived = f"{derived}__lemma_{index}"
    return derived


def canonicalize_task_dict(task: dict) -> dict:
    if not isinstance(task, dict):
        return task
    canonical = dict(task)
    raw_block_id = canonical.get("block_id", "")
    canonical_block_id = canonicalize_block_id(raw_block_id)
    if canonical_block_id:
        canonical["block_id"] = canonical_block_id
    canonical["dependencies"] = canonicalize_id_list(canonical.get("dependencies", []))
    if "soft_imports" in canonical:
        canonical["soft_imports"] = canonicalize_id_list(canonical.get("soft_imports", []))
    return canonical


def find_block_ids_in_text(text: str, candidate_ids: Iterable[str]) -> list[str]:
    haystack = str(text or "")
    matches: list[tuple[int, str]] = []
    for candidate in candidate_ids:
        canonical = canonicalize_block_id(candidate)
        if not canonical:
            continue
        variants = (canonical,) + legacy_ids_for(canonical)
        for variant in variants:
            pattern = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(variant)}(?![A-Za-z0-9_])", re.IGNORECASE)
            found = pattern.search(haystack)
            if found:
                matches.append((found.start(), canonical))
                break
    ordered: list[str] = []
    seen: set[str] = set()
    for _, canonical in sorted(matches, key=lambda item: (item[0], item[1])):
        if canonical in seen:
            continue
        seen.add(canonical)
        ordered.append(canonical)
    return ordered
