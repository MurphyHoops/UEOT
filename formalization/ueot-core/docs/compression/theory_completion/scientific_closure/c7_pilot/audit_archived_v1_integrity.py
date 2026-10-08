#!/usr/bin/env python3
"""Check immutable C7 v1 evidence bundle integrity, never scientific independence.

The frozen manifest records historical script paths run_pilot.py and
verify_evidence.py; these sources are now archived under *_v1.py. This checker
uses an explicit remapping and never imports the current hardened verifier.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
ARCHIVED_NAME = {
    "run_pilot.py": "run_pilot_v1.py",
    "verify_evidence.py": "verify_evidence_v1.py",
}
MANIFEST = "EVIDENCE_MANIFEST_v1.sha256"


def expected_run_ids():
    ids = set()
    for n in range(1, 4):
        for r in range(1, 6):
            ids.update((f"cert-n{n}-read-r{r}", f"cert-n{n}-single-r{r}"))
    for r in range(1, 6):
        ids.update((f"holdout-replace-r{r}", f"neg-double-r{r}", f"baseline-single-r{r}"))
    assert len(ids) == 45
    return ids


def verify(root: Path):
    problems = []
    raw = (root / MANIFEST).read_text(encoding="utf-8").splitlines()
    manifest_names = set()
    for line in raw:
        parts = line.split("  ", 1)
        if len(parts) != 2 or len(parts[0]) != 64:
            problems.append("malformed manifest entry")
            continue
        digest, historic_name = parts
        if historic_name in manifest_names:
            problems.append(f"duplicate manifest name: {historic_name}")
        manifest_names.add(historic_name)
        physical = ARCHIVED_NAME.get(historic_name, historic_name)
        try:
            actual = hashlib.sha256((root / physical).read_bytes()).hexdigest()
        except FileNotFoundError:
            problems.append(f"missing artifact: {physical}")
            continue
        if actual != digest:
            problems.append(f"sha256 mismatch for archived {historic_name} at {physical}")

    frozen_names = {
        "worker.py", "run_pilot.py", "verify_evidence.py",
        "raw_certification_v1.jsonl", "summary_certification_v1.json",
        "recomputed_certification_v1.json",
        "raw_reproduction_v1.jsonl", "summary_reproduction_v1.json",
        "recomputed_reproduction_v1.json", "reproduction_comparison.json",
    }
    if manifest_names != frozen_names or len(raw) != len(frozen_names):
        problems.append(
            "frozen manifest requires exactly ten entries; "
            f"missing={sorted(frozen_names - manifest_names)}; "
            f"unexpected={sorted(manifest_names - frozen_names)}"
        )
    expected = expected_run_ids()
    inventory = {}
    for filename in ("raw_certification_v1.jsonl", "raw_reproduction_v1.jsonl"):
        try:
            rows = [json.loads(line) for line in (root / filename).read_text().splitlines() if line.strip()]
            ids = [row.get("run_id") if isinstance(row, dict) else None for row in rows]
            complete = len(rows) == 45 and len(set(ids)) == 45 and set(ids) == expected
        except (FileNotFoundError, ValueError, TypeError):
            complete = False
            rows = []
        inventory[filename] = {"record_count": len(rows), "registered_run_ids_complete": complete}
        if not complete:
            problems.append(f"invalid v1 inventory: {filename}")
    return {
        "kind": "ARCHIVED_V1_ARTIFACT_INTEGRITY_ONLY",
        "all_checks_pass": not problems,
        "manifest_entries": len(raw),
        "inventory": inventory,
        "problems": problems,
        "independent_review": "REVIEW_PENDING",
        "historical_no_censoring": "UNVERIFIABLE",
        "real_world_support": "UNVERIFIED",
    }


def main():
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT
    result = verify(root)
    print(json.dumps(result, sort_keys=True, indent=2))
    if not result["all_checks_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
