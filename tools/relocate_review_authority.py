#!/usr/bin/env python3
"""Run the guarded Phase 5 review-authority relocation workflow.

Inputs are explicit: an immutable legacy state database, the rebuilt target
database, the unified repository and target commit, and a new evidence root.
Use ``--apply`` only after the same command has validated the 181/159/112
closed route partition and completed the fresh corpus/Lake build gates.
"""

from formalization_engine.authority_relocation import main


if __name__ == "__main__":
    raise SystemExit(main())
