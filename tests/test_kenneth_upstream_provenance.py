from __future__ import annotations

import hashlib
from pathlib import Path


KENNETH_COMMIT = "f81f1450e49bd1bdf07cc123c5a221c7b39b0eb1"
KENNETH_DEF_1_2A_SIZE = 61_677
KENNETH_DEF_1_2A_BLOB_SHA = "4c61a677f296ac11e923d06dbb267cf8da0b0ccd"


def test_kenneth_def_1_2a_is_the_byte_exact_reviewed_blob() -> None:
    repository_root = Path(__file__).resolve().parents[1]
    upstream_file = (
        repository_root
        / "upstream"
        / "kenneth"
        / KENNETH_COMMIT[:8]
        / "def_1_2a.lean"
    )

    content = upstream_file.read_bytes()
    git_blob = b"blob " + str(len(content)).encode("ascii") + b"\0" + content

    assert len(content) == KENNETH_DEF_1_2A_SIZE
    assert hashlib.sha1(git_blob).hexdigest() == KENNETH_DEF_1_2A_BLOB_SHA
