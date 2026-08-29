from __future__ import annotations

import os
import shutil
import stat
from pathlib import Path


def remove_git_fixture_tree(root: Path) -> None:
    """Remove a disposable test Git repository, including read-only objects."""

    if not root.exists():
        return

    def clear_readonly_and_retry(function, path: str, exc: BaseException) -> None:
        if not isinstance(exc, PermissionError):
            raise exc
        os.chmod(path, stat.S_IWRITE)
        function(path)

    try:
        shutil.rmtree(root, onexc=clear_readonly_and_retry)
    except TypeError:
        # Python < 3.12 exposes the older onerror callback with exc_info.
        def clear_readonly_legacy(function, path: str, exc_info) -> None:
            clear_readonly_and_retry(function, path, exc_info[1])

        shutil.rmtree(root, onerror=clear_readonly_legacy)

    if root.exists():
        raise RuntimeError(f"Test Git fixture cleanup left a directory behind: {root}")

