"""Record deterministic hashes of the exact QM proof/runtime/fixture sources.

The observed checkout commit is metadata. Local candidate bytes may differ;
the file hashes identify the source actually supplied to verification.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess


PACKAGE = Path(__file__).resolve().parents[1]
REPOSITORY = PACKAGE.parents[1]


def source_paths() -> list[Path]:
    paths = set((PACKAGE / "UEOTQM").rglob("*.lean"))
    paths.update(PACKAGE / name for name in (
        "UEOTQM.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
    ))
    paths.update(p for p in (PACKAGE / "scripts").rglob("*")
                 if p.is_file() and p.suffix in {".py", ".lean", ".sh"})
    kernel = REPOSITORY / "physics/qm/kernel"
    paths.update(kernel.rglob("*.py"))
    paths.update(p for p in (kernel / "certificates").rglob("*")
                 if p.is_file() and p.suffix in {".lean", ".json"})
    paths.add(REPOSITORY / ".github/workflows/ueot-qm.yml")
    return sorted(paths)


def record_source() -> dict:
    try:
        checkout = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPOSITORY, text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        checkout = None
    sources = [{"path": p.relative_to(REPOSITORY).as_posix(),
                "sha256": sha256(p.read_bytes()).hexdigest(),
                "bytes": p.stat().st_size} for p in source_paths()]
    return {
        "schema": "ueot_qm.source_manifest.v2",
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "observed_checkout_commit": checkout,
        "identity_rule": "Per-file hashes identify tested bytes; checkout metadata does not assert a clean tree",
        "source_count": len(sources),
        "sources": sources,
        "source_set_sha256": sha256(json.dumps(
            sources, sort_keys=True, separators=(",", ":"),
        ).encode("utf-8")).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    content = json.dumps(record_source(), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content)
    else:
        print(content, end="")


if __name__ == "__main__":
    main()
