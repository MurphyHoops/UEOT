#!/usr/bin/env python3
"""Automated Gatekeeper for UEOT AI Lab Wiki & Conference System.

Modes:
  wiki : Validate research/lab_wiki/ structure, IDs, referenced files, and zero-placeholder rules.
  fast : wiki + Lean toolchain/dependency lock + comment-aware proof-escape scan.
  lean : fast + `lake build UEOTPhysicsUnification` + `ExhaustiveAxiomAudit.lean`.
  full : lean + `physics/unification/run_verification.py --check`.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any

sys.dont_write_bytecode = True

WIKI_DIR = Path(__file__).resolve().parent
REPO_ROOT = WIKI_DIR.parents[1]
UNIF_LEAN_DIR = REPO_ROOT / "formalization" / "ueot-physics-unification"
UNIF_PHYS_RUNNER = REPO_ROOT / "physics" / "unification" / "run_verification.py"
DEFAULT_RECEIPT = WIKI_DIR / "receipts" / "latest_gate.json"

REQUIRED_FILES = [
    "README.md",
    "AGENT_PLAYBOOK.md",
    "OPEN_SPECS.md",
    "VERIFIED_LEMMAS.md",
    "DEAD_ENDS.md",
    "MEETING_MINUTES/TEMPLATE.md",
]

SPEC_ID_RE = re.compile(r"^SPEC-\d{8}-\d{2}$")
LEMMA_ID_RE = re.compile(r"^LEMMA-\d{8}-\d{2}$")
DEAD_ID_RE = re.compile(r"^DEAD-\d{8}-\d{2}$")
FORBIDDEN_VERIFIED_TOKEN_RE = re.compile(
    r"\b(?:TODO|TBD|PENDING|WIP|FAIL|FAILED|sorry|admit|sorryAx|native_decide)\b",
    re.IGNORECASE,
)
FORBIDDEN_AXIOM_AUDIT_RE = re.compile(r"\b(?:sorryAx|Lean\.ofReduceBool|admit)\b")
ALLOWED_SPEC_STATUSES = {"OPEN", "IN_PROGRESS", "CLOSED", "DROPPED"}


def _strip_code_ticks(cell: str) -> str:
    s = cell.strip()
    if len(s) >= 2 and s.startswith("`") and s.endswith("`"):
        return s[1:-1].strip()
    return s


def _parse_markdown_tables(text: str) -> list[tuple[list[str], list[list[str]]]]:
    """Return list of (headers, rows) for all pipe tables outside fenced code blocks."""
    tables: list[tuple[list[str], list[list[str]]]] = []
    lines = text.splitlines()
    in_fence = False
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.strip().startswith("```"):
            in_fence = not in_fence
            i += 1
            continue
        if in_fence:
            i += 1
            continue
        if "|" in line and i + 1 < len(lines) and re.match(r"^\s*\|?\s*:?-{3,}:?\s*\|", lines[i + 1]):
            headers = [c.strip() for c in line.strip().strip("|").split("|")]
            i += 2
            rows: list[list[str]] = []
            while i < len(lines) and "|" in lines[i] and lines[i].strip().startswith("|"):
                cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                rows.append(cells)
                i += 1
            tables.append((headers, rows))
            continue
        i += 1
    return tables


def check_wiki() -> dict[str, Any]:
    t0 = time.monotonic()
    errors: list[str] = []
    stats: dict[str, int] = {"open_specs": 0, "verified_lemmas": 0, "dead_ends": 0}

    for rel in REQUIRED_FILES:
        if not (WIKI_DIR / rel).is_file():
            errors.append(f"Missing required wiki file: research/lab_wiki/{rel}")

    if errors:
        return {
            "name": "wiki_integrity",
            "status": "FAIL",
            "duration_sec": round(time.monotonic() - t0, 3),
            "stats": stats,
            "errors": errors,
        }

    # 1. OPEN_SPECS.md
    spec_tables = _parse_markdown_tables((WIKI_DIR / "OPEN_SPECS.md").read_text(encoding="utf-8"))
    seen_specs: set[str] = set()
    if not spec_tables:
        errors.append("OPEN_SPECS.md: missing markdown index table")
    else:
        _, rows = spec_tables[0]
        for idx, row in enumerate(rows, start=1):
            if len(row) < 4:
                errors.append(f"OPEN_SPECS.md row {idx}: expected at least 4 columns")
                continue
            spec_id = _strip_code_ticks(row[0])
            status = _strip_code_ticks(row[1])
            if not SPEC_ID_RE.match(spec_id):
                errors.append(f"OPEN_SPECS.md row {idx}: invalid Spec-ID '{spec_id}' (expected SPEC-YYYYMMDD-NN)")
            if spec_id in seen_specs:
                errors.append(f"OPEN_SPECS.md row {idx}: duplicate Spec-ID '{spec_id}'")
            seen_specs.add(spec_id)
            if status not in ALLOWED_SPEC_STATUSES:
                errors.append(f"OPEN_SPECS.md row {idx}: invalid Status '{status}' (allowed: {sorted(ALLOWED_SPEC_STATUSES)})")
            stats["open_specs"] += 1

    # 2. VERIFIED_LEMMAS.md
    lemma_tables = _parse_markdown_tables((WIKI_DIR / "VERIFIED_LEMMAS.md").read_text(encoding="utf-8"))
    seen_lemmas: set[str] = set()
    if not lemma_tables:
        errors.append("VERIFIED_LEMMAS.md: missing markdown verified table")
    else:
        _, rows = lemma_tables[0]
        for idx, row in enumerate(rows, start=1):
            if len(row) < 7:
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: expected 7 columns")
                continue
            raw_row = " | ".join(row)
            m = FORBIDDEN_VERIFIED_TOKEN_RE.search(raw_row)
            if m:
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: forbidden unverified token '{m.group(0)}'")
            lemma_id = _strip_code_ticks(row[0])
            rel_file = _strip_code_ticks(row[3])
            gate_status = _strip_code_ticks(row[5])
            if not LEMMA_ID_RE.match(lemma_id):
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: invalid Lemma-ID '{lemma_id}' (expected LEMMA-YYYYMMDD-NN)")
            if lemma_id in seen_lemmas:
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: duplicate Lemma-ID '{lemma_id}'")
            seen_lemmas.add(lemma_id)
            if gate_status != "PASS":
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: Gate Status must be 'PASS', got '{gate_status}'")
            target_path = (REPO_ROOT / rel_file).resolve()
            try:
                target_path.relative_to(REPO_ROOT.resolve())
            except ValueError:
                errors.append(f"VERIFIED_LEMMAS.md row {idx}: File '{rel_file}' escapes repository root")
            else:
                if not target_path.is_file():
                    errors.append(f"VERIFIED_LEMMAS.md row {idx}: referenced File does not exist: '{rel_file}'")
            stats["verified_lemmas"] += 1

    # 3. DEAD_ENDS.md
    dead_tables = _parse_markdown_tables((WIKI_DIR / "DEAD_ENDS.md").read_text(encoding="utf-8"))
    seen_dead: set[str] = set()
    if not dead_tables:
        errors.append("DEAD_ENDS.md: missing markdown dead-ends table")
    else:
        _, rows = dead_tables[0]
        for idx, row in enumerate(rows, start=1):
            if len(row) < 6:
                errors.append(f"DEAD_ENDS.md row {idx}: expected at least 6 columns")
                continue
            dead_id = _strip_code_ticks(row[0])
            if not DEAD_ID_RE.match(dead_id):
                errors.append(f"DEAD_ENDS.md row {idx}: invalid Dead-ID '{dead_id}' (expected DEAD-YYYYMMDD-NN)")
            if dead_id in seen_dead:
                errors.append(f"DEAD_ENDS.md row {idx}: duplicate Dead-ID '{dead_id}'")
            seen_dead.add(dead_id)
            stats["dead_ends"] += 1

    return {
        "name": "wiki_integrity",
        "status": "PASS" if not errors else "FAIL",
        "duration_sec": round(time.monotonic() - t0, 3),
        "stats": stats,
        "errors": errors,
    }


def _augmented_env() -> dict[str, str]:
    env = os.environ.copy()
    env["OPENBLAS_NUM_THREADS"] = "1"
    env["OMP_NUM_THREADS"] = "1"
    elan_bin = Path.home() / ".elan" / "bin"
    try:
        has_elan = elan_bin.is_dir()
    except OSError:
        has_elan = False
    if has_elan:
        cur_path = env.get("PATH", "")
        if str(elan_bin) not in cur_path.split(os.pathsep):
            env["PATH"] = f"{elan_bin}{os.pathsep}{cur_path}"
    return env


def _run_cmd(
    name: str,
    cmd: list[str],
    cwd: Path,
    env: dict[str, str],
    timeout_sec: int,
    forbid_output_re: re.Pattern[str] | None = None,
) -> dict[str, Any]:
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    except FileNotFoundError as exc:
        return {
            "name": name,
            "command": " ".join(cmd),
            "cwd": str(cwd.relative_to(REPO_ROOT)),
            "status": "FAIL",
            "returncode": -1,
            "duration_sec": round(time.monotonic() - t0, 3),
            "error": f"Executable not found: {exc}",
        }
    except subprocess.TimeoutExpired:
        return {
            "name": name,
            "command": " ".join(cmd),
            "cwd": str(cwd.relative_to(REPO_ROOT)),
            "status": "FAIL",
            "returncode": -2,
            "duration_sec": round(time.monotonic() - t0, 3),
            "error": f"Timed out after {timeout_sec}s",
        }

    combined = (proc.stdout or "") + ("\n" + proc.stderr if proc.stderr else "")
    status = "PASS" if proc.returncode == 0 else "FAIL"
    extra_err = None
    if status == "PASS" and forbid_output_re is not None:
        m = forbid_output_re.search(combined)
        if m:
            status = "FAIL"
            extra_err = f"Forbidden token '{m.group(0)}' detected in output"

    tail_lines = combined.strip().splitlines()[-15:]
    res: dict[str, Any] = {
        "name": name,
        "command": " ".join(cmd),
        "cwd": str(cwd.relative_to(REPO_ROOT)),
        "status": status,
        "returncode": proc.returncode,
        "duration_sec": round(time.monotonic() - t0, 3),
        "output_tail": tail_lines,
    }
    if extra_err:
        res["error"] = extra_err
    return res


def _git_head_short() -> str:
    try:
        p = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=10,
        )
        return p.stdout.strip() if p.returncode == 0 else "unknown"
    except Exception:
        return "unknown"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=["wiki", "fast", "lean", "full"],
        default="fast",
        help="Verification depth (default: fast)",
    )
    parser.add_argument(
        "--write-receipt",
        action="store_true",
        help="Write JSON receipt to --receipt-path",
    )
    parser.add_argument(
        "--receipt-path",
        type=Path,
        default=DEFAULT_RECEIPT,
        help="Path for JSON gate receipt (default: research/lab_wiki/receipts/latest_gate.json)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help="Per-command timeout in seconds for lean/full steps (default: 1800)",
    )
    args = parser.parse_args()

    env = _augmented_env()
    checks: list[dict[str, Any]] = []

    # 1. Wiki integrity
    checks.append(check_wiki())

    # 2. Fast Lean syntactic & dependency checks
    if args.mode in {"fast", "lean", "full"}:
        checks.append(
            _run_cmd(
                "lean_dependency_lock",
                [sys.executable, "-B", "scripts/check_dependencies.py"],
                UNIF_LEAN_DIR,
                env,
                timeout_sec=120,
            )
        )
        checks.append(
            _run_cmd(
                "lean_no_escapes",
                [sys.executable, "-B", "scripts/check_no_escapes.py"],
                UNIF_LEAN_DIR,
                env,
                timeout_sec=120,
            )
        )

    # 3. Full Lean 4 kernel build & exhaustive axiom audit
    if args.mode in {"lean", "full"}:
        lake_bin = shutil.which("lake", path=env.get("PATH"))
        if not lake_bin:
            checks.append(
                {
                    "name": "lean_toolchain_available",
                    "status": "FAIL",
                    "duration_sec": 0.0,
                    "error": "lake executable not found on PATH or ~/.elan/bin",
                }
            )
        else:
            checks.append(
                _run_cmd(
                    "lean_build_unification",
                    [lake_bin, "build", "UEOTPhysicsUnification"],
                    UNIF_LEAN_DIR,
                    env,
                    timeout_sec=args.timeout,
                )
            )
            checks.append(
                _run_cmd(
                    "lean_exhaustive_axiom_audit",
                    [lake_bin, "env", "lean", "scripts/ExhaustiveAxiomAudit.lean"],
                    UNIF_LEAN_DIR,
                    env,
                    timeout_sec=args.timeout,
                    forbid_output_re=FORBIDDEN_AXIOM_AUDIT_RE,
                )
            )

    # 4. Deterministic numerical unification verification
    if args.mode == "full":
        checks.append(
            _run_cmd(
                "physics_unification_verification",
                [sys.executable, "-B", str(UNIF_PHYS_RUNNER), "--check"],
                REPO_ROOT,
                env,
                timeout_sec=args.timeout,
            )
        )

    overall = "PASS" if all(c["status"] == "PASS" for c in checks) else "FAIL"
    receipt = {
        "schema": "ueot.lab_wiki.gate_receipt.v1",
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "git_head": _git_head_short(),
        "mode": args.mode,
        "overall_status": overall,
        "checks": checks,
    }

    for c in checks:
        mark = "PASS" if c["status"] == "PASS" else "FAIL"
        print(f"[{mark}] {c['name']} ({c['duration_sec']}s)")
        if c["status"] != "PASS":
            if "errors" in c:
                for err in c["errors"]:
                    print(f"       - {err}")
            if "error" in c:
                print(f"       - {c['error']}")
            for line in c.get("output_tail", []):
                print(f"       | {line}")

    if args.write_receipt:
        receipt_path = args.receipt_path if args.receipt_path.is_absolute() else (REPO_ROOT / args.receipt_path)
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Receipt written: {receipt_path.relative_to(REPO_ROOT)}")

    print(f"GATEKEEPER_OVERALL={overall} mode={args.mode} head={receipt['git_head']}")
    return 0 if overall == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
