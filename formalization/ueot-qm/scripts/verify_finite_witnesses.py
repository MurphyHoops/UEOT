#!/usr/bin/env python3
"""Recompile and fully audit the retained finite Lean witnesses.

This gate adds no general theorem count. It binds the witness bytes and all
repository-local general Lean sources/import artifacts before and after each
actual invocation. It does not claim to reconstruct an olean from its hash;
the ordinary package build remains the separate prerequisite.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
CORE_ROOT = PACKAGE_ROOT.parent / "ueot-core"
WITNESSES = ("MixtureExamples", "SurvivalTwoState", "RealTomographyTwoRebit", "QuantumDoobExamples",
             "QuantumPurificationExamples", "ClassicalQuantumMemoryExamples", "QuantumDoobDynamicsExamples",
             "QuantumSeparationExamples", "PurificationUniquenessExamples", "ActionRecordBudgetExamples",
             "QuantumTraceDistanceExamples", "PurificationDimensionExamples", "StoppingRecordBudgetExamples")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_'.]*"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def identity(path: Path) -> dict:
    content = path.read_bytes()
    return {"path": str(path.resolve()), "size": len(content),
            "sha256": hashlib.sha256(content).hexdigest()}


def lean_code(source: str) -> str:
    """Mask nested comments and strings, preserving positions and newlines."""
    result = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            char = source[i]
            if char != "\n":
                result[i] = " "
            if char == "\\" and i + 1 < len(source):
                if source[i + 1] != "\n":
                    result[i + 1] = " "
                i += 2
            else:
                string = char != '"'
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        elif source.startswith("/-", i):
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            result[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)


def witness_declarations(path: Path) -> list[dict]:
    """Read explicit source commands, not generated environment constants."""
    code = lean_code(path.read_text(encoding="utf-8"))
    blocks: list[tuple[str, str]] = []
    declarations = []
    requested = []
    for line in code.splitlines():
        line = line.strip()
        if match := re.fullmatch(r"namespace\s+(" + IDENTIFIER + r")", line):
            blocks.append(("namespace", match[1]))
        elif re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+" + IDENTIFIER + r")?", line):
            blocks.append(("section", ""))
        elif re.fullmatch(r"end(?:\s+" + IDENTIFIER + r")?", line):
            if not blocks:
                raise ValueError(f"Unmatched end in {path.name}")
            blocks.pop()
        elif match := re.match(r"(?:@\[[^]]+\]\s*)?(?:noncomputable\s+)?"
                               r"(theorem|def|abbrev)\s+(" + IDENTIFIER + r")(?=\s|:|\()", line):
            prefix = ".".join(name for kind, name in blocks if kind == "namespace")
            name = f"{prefix}.{match[2]}" if prefix else match[2]
            declarations.append({"kind": match[1], "name": name})
        elif match := re.fullmatch(r"#print\s+axioms\s+(" + IDENTIFIER + r")", line):
            requested.append(match[1])
        elif re.match(r"(?:private\s+|protected\s+)?(?:theorem|def|abbrev)\b", line):
            raise ValueError(f"Unsupported explicit declaration syntax in {path.name}: {line}")
        elif line.startswith("#"):
            raise ValueError(f"Unexpected diagnostic command in {path.name}: {line}")
    if blocks:
        raise ValueError(f"Unclosed namespace/section in {path.name}")
    names = [item["name"] for item in declarations]
    if not names or len(set(names)) != len(names):
        raise ValueError(f"Missing or duplicate explicit declarations in {path.name}")
    if requested != names:
        raise ValueError(f"{path.name}: #print axioms must list every explicit theorem/def/abbrev once, in source order")
    return declarations


def repository_modules() -> dict[str, tuple[Path, Path]]:
    """All QM general modules plus their recursive repository Core imports."""
    pending = ["UEOTQM"] + ["UEOTQM." + p.stem for p in (PACKAGE_ROOT / "UEOTQM").glob("*.lean")]
    modules = {}
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        root = PACKAGE_ROOT if name == "UEOTQM" or name.startswith("UEOTQM.") else CORE_ROOT
        relative = Path(*name.split("."))
        source = root / relative.with_suffix(".lean")
        artifact = root / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        if not source.is_file() or not artifact.is_file():
            raise FileNotFoundError(f"Build prerequisite missing for {name}: {source} or {artifact}")
        modules[name] = (source, artifact)
        for imports in re.findall(r"^\s*import\s+([^\n]+)$", lean_code(source.read_text()), re.M):
            for imported in imports.split():
                if imported == "UEOTQM" or imported.startswith(("UEOTQM.", "UEOT.")):
                    pending.append(imported)
    return modules


def input_snapshot(paths: dict[str, Path]) -> dict:
    modules = repository_modules()
    context = {"verifier": Path(__file__).resolve(), "lean-toolchain": PACKAGE_ROOT / "lean-toolchain",
               "lake-manifest.json": PACKAGE_ROOT / "lake-manifest.json"}
    for name in ("lakefile.lean", "lakefile.toml"):
        if (PACKAGE_ROOT / name).is_file():
            context[name] = PACKAGE_ROOT / name
    return {"witnesses": {name: identity(path) for name, path in sorted(paths.items())},
            "general_modules": {name: {"source": identity(source), "olean": identity(artifact)}
                                for name, (source, artifact) in sorted(modules.items())},
            "context": {name: identity(path) for name, path in sorted(context.items())}}


def run_command(command: list[str], log: Path, timeout: int) -> dict:
    started = utc_now()
    timed_out = False
    launch_error = None
    try:
        result = subprocess.run(command, cwd=PACKAGE_ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout)
        output, exit_code = result.stdout, result.returncode
    except subprocess.TimeoutExpired as exc:
        output, exit_code, timed_out = exc.stdout or b"", None, True
    except OSError as exc:
        output, exit_code, launch_error = str(exc).encode(), None, str(exc)
    log.write_bytes(output)
    return {"command": command, "cwd": str(PACKAGE_ROOT), "started_utc": started,
            "finished_utc": utc_now(), "exit_code": exit_code, "timed_out": timed_out,
            "launch_error": launch_error, "log": identity(log)}


def audit_result(log: Path, declarations: list[dict]) -> dict:
    output = log.read_text(encoding="utf-8", errors="replace")
    reports = re.findall(r"^'([^\n]+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                         output, re.M)
    names = [name for name, _ in reports]
    expected = [item["name"] for item in declarations]
    actual = {name: sorted(axiom.strip() for axiom in axioms.split(",") if axiom.strip())
              for name, axioms in reports}
    duplicates = sorted(name for name, count in Counter(names).items() if count != 1)
    unreviewed = {name: sorted(set(axioms) - ALLOWED_AXIOMS) for name, axioms in actual.items()
                  if set(axioms) - ALLOWED_AXIOMS}
    complete = not duplicates and len(names) == len(expected) and set(names) == set(expected)
    return {"expected": expected, "actual": actual, "duplicate_reports": duplicates,
            "missing_reports": sorted(set(expected) - set(names)),
            "unexpected_reports": sorted(set(names) - set(expected)),
            "unreviewed_axioms": unreviewed, "complete_unique": complete,
            "status": "PASS" if complete and not unreviewed else "FAIL"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=PACKAGE_ROOT / "evidence/finite-witnesses")
    parser.add_argument("--lake", default="lake", help="Lake executable name or filesystem path")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--witness", action="append", choices=WITNESSES,
                        help="Run a selected registered witness; repeat for multiple selections. Default: all.")
    args = parser.parse_args()
    selected = tuple(args.witness) if args.witness else WITNESSES
    if len(set(selected)) != len(selected):
        parser.error("--witness must not repeat the same registered name")
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    paths = {name: PACKAGE_ROOT / "scripts/witnesses" / f"{name}.lean" for name in selected}
    receipt = {"schema": "ueot_qm.finite_witnesses.v1", "status": "FAIL", "started_utc": utc_now(),
               "scope": "concrete witnesses, excluded from general theorem and axiom-audit totals",
               "package_root": str(PACKAGE_ROOT), "allowed_axioms": sorted(ALLOWED_AXIOMS),
               "registered_witnesses": list(WITNESSES), "selected_witnesses": list(selected),
               "selection_is_complete": set(selected) == set(WITNESSES),
               "checks": [], "errors": []}
    before = None
    try:
        if args.timeout_seconds <= 0:
            raise ValueError("--timeout-seconds must be positive")
        lake = shutil.which(args.lake)
        if lake is None:
            raise FileNotFoundError(f"Lake executable not found: {args.lake}")
        # Preserve the invocation basename: elan-style shims may dispatch by it.
        lake = str(Path(lake).absolute())
        receipt["lake_invocation_path"] = lake
        receipt["lake_executable"] = identity(Path(lake))
        before = input_snapshot(paths)
        receipt["inputs_before"] = before
        declarations = {name: witness_declarations(path) for name, path in paths.items()}
        receipt["declarations"] = declarations
        all_declarations = [d for ds in declarations.values() for d in ds]
        receipt["witness_theorem_count"] = sum(d["kind"] == "theorem" for d in all_declarations)
        receipt["witness_def_count"] = sum(d["kind"] == "def" for d in all_declarations)
        receipt["witness_abbrev_count"] = sum(d["kind"] == "abbrev" for d in all_declarations)
        receipt["witness_audit_count"] = len(all_declarations)
        pin = (PACKAGE_ROOT / "lean-toolchain").read_text().strip()
        match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", pin)
        if not match:
            raise ValueError(f"Unsupported pinned toolchain format: {pin}")
        version_log = output_dir / "toolchain.log"
        version = run_command([lake, "env", "lean", "--version"], version_log, args.timeout_seconds)
        version["pinned_toolchain"] = pin
        version["matches_pin"] = bool(re.search(r"\bversion\s+" + re.escape(match[1]) + r"\b",
                                                version_log.read_text(errors="replace")))
        receipt["toolchain"] = version
        if version["exit_code"] != 0 or not version["matches_pin"]:
            raise RuntimeError("The actual lake env lean version did not match the pinned toolchain")
        for name, path in paths.items():
            if input_snapshot(paths) != before:
                raise RuntimeError(f"Input source/artifact identity changed before {name}")
            log = output_dir / f"{name}.compile.log"
            check = run_command([lake, "env", "lean", str(path)], log, args.timeout_seconds)
            check.update({"name": name, "source": before["witnesses"][name],
                          "declaration_count": len(declarations[name]),
                          "audit": audit_result(log, declarations[name])})
            check["inputs_unchanged"] = input_snapshot(paths) == before
            check["status"] = ("PASS" if check["exit_code"] == 0 and check["audit"]["status"] == "PASS"
                               and check["inputs_unchanged"] else "FAIL")
            receipt["checks"].append(check)
            print(f"{name}: {check['status']} ({len(declarations[name])} explicit declaration audits)", flush=True)
    except (OSError, ValueError, RuntimeError) as exc:
        receipt["errors"].append(str(exc))
    finally:
        if before is not None:
            try:
                receipt["inputs_after"] = input_snapshot(paths)
                receipt["all_inputs_unchanged"] = receipt["inputs_after"] == before
                receipt["lake_executable_unchanged"] = identity(Path(receipt["lake_invocation_path"])) == receipt["lake_executable"]
            except (OSError, ValueError) as exc:
                receipt["all_inputs_unchanged"] = False
                receipt["errors"].append(f"Final identity check failed: {exc}")
        passed = (not receipt["errors"] and len(receipt["checks"]) == len(selected)
                  and all(check["status"] == "PASS" for check in receipt["checks"])
                  and receipt.get("all_inputs_unchanged") and receipt.get("lake_executable_unchanged"))
        receipt["status"] = "PASS" if passed else "FAIL"
        receipt["finished_utc"] = utc_now()
        (output_dir / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"{receipt['status']}: {output_dir / 'verification.json'}", flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
