from .ledger import (
    LedgerBasisRebindConflictError,
    LedgerDependencyConflictError,
    LedgerManager,
    TaskStatus,
)
from .settings import Settings, get_settings


def __getattr__(name: str):
    """Load SQLite exports lazily so ``state_store -> core.settings`` cannot cycle."""

    if name in {"SQLiteLedgerManager", "open_runtime_ledger"}:
        from . import sqlite_ledger

        return getattr(sqlite_ledger, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

__all__ = [
    "LedgerManager",
    "LedgerBasisRebindConflictError",
    "LedgerDependencyConflictError",
    "TaskStatus",
    "SQLiteLedgerManager",
    "Settings",
    "get_settings",
    "open_runtime_ledger",
]
