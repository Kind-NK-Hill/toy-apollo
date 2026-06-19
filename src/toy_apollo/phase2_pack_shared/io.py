from __future__ import annotations

import hashlib
import json
import os
import shutil
from pathlib import Path
from typing import Any


def fs_path(path: Path) -> str:
    raw = str(path)
    if os.name != "nt" or raw.startswith("\\\\?\\"):
        return raw
    absolute = raw if path.is_absolute() else str(path.resolve())
    if absolute.startswith("\\\\"):
        return "\\\\?\\UNC\\" + absolute.lstrip("\\")
    return "\\\\?\\" + absolute


def path_exists(path: Path) -> bool:
    try:
        return os.path.exists(fs_path(path))
    except OSError:
        return False


def unlink_path(path: Path) -> None:
    os.unlink(fs_path(path))


def make_dirs(path: Path, *, exist_ok: bool = True) -> None:
    os.makedirs(fs_path(path), exist_ok=exist_ok)


def read_file_safely(path: Path) -> str:
    try:
        with open(fs_path(path), "r", encoding="utf-8", errors="replace") as f:
            return f.read()
    except Exception:
        return ""


def read_json_safely(path: Path, default: Any) -> Any:
    try:
        with open(fs_path(path), "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def write_text(path: Path, text: str) -> None:
    with open(fs_path(path), "w", encoding="utf-8") as f:
        f.write(text)


def append_text(path: Path, text: str) -> None:
    with open(fs_path(path), "a", encoding="utf-8") as f:
        f.write(text)


def write_json(path: Path, payload: Any) -> None:
    write_text(path, json.dumps(payload, indent=2, ensure_ascii=False))


def copy_file(source: Path, target: Path) -> None:
    shutil.copyfile(fs_path(source), fs_path(target))


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_json(payload: Any) -> str:
    return sha256_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
