import sys
from pathlib import Path

# Keep root entrypoint stable while loading the new src/toy_apollo package layout.
sys.path.insert(0, str(Path(__file__).resolve().parent / "src"))

from toy_apollo.cli.app import main


if __name__ == "__main__":
    raise SystemExit(main())
