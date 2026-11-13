#!/usr/bin/env python3
"""Targeted UEOT reproduction. Run with the pinned project's `lake env python3`.

Writes only a newly created output directory outside the project. It never runs
lake build, updates dependencies, edits source, or labels a reused proof fresh.
This script and its Lean probe are PREPARED, NOT EXECUTED, until a run receipt says otherwise.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone


def now():
    return datetime.now(timezone.utc).isoformat()


def sha256(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def blob(path):
    data = Path(path).read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def capture(argv, cwd, env=None):
    p = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True)
    if p.returncode:
        raise RuntimeError(f"command failed ({p.returncode}): {argv!r}\n{p.stdout}\n{p.stderr}")
    return p.stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True,
                    help="Must not already exist; must be outside the repository")
    ap.add_argument("--expected-head", default=None,
                    help="Default: the plan's observed main. Record a newly verified head explicitly if necessary.")
    ap.add_argument("--step-timeout", type=int, default=900)
    args = ap.parse_args()
    bundle = Path(__file__).resolve().parent
    plan = json.loads((bundle / "D3_PLAN.json").read_text())
    expected = json.loads((bundle / "EXPECTED_SOURCE_BLOBS.json").read_text())
    repo = args.repo.resolve()
    project = repo / plan["project_relative"]
    output = args.output.resolve()
    if output == repo or repo in output.parents:
        raise SystemExit("Output must be outside the repository; do not write production .lake artifacts.")
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    overlay = output / "overlay"
    probe_dir = output / "probe"
    for p in (logs, overlay, probe_dir):
        p.mkdir()
    record = {
        "schema": plan["schema"], "status": "RUNNING", "started_utc": now(),
        "scope": plan["scope"], "repo": str(repo), "project": str(project),
        "output": str(output), "fresh_lean_execution": False,
        "full_clean_build": False, "reused_dependencies": True,
        "production_source_mutations": False, "steps": [],
        "bundle_sha256": {p.name: sha256(p) for p in
                          [Path(__file__), bundle / "D3_PLAN.json", bundle / "EXPECTED_SOURCE_BLOBS.json", bundle / "D3Probe.lean"]},
    }
    receipt_path = output / "D3_RECEIPT.json"

    def checkpoint():
        save(receipt_path, record)

    def execute(label, argv, cwd, env):
        logfile = logs / (label + ".log")
        started = time.time()
        row = {"label": label, "argv": argv, "cwd": str(cwd),
               "started_utc": now(), "log": str(logfile)}
        print(json.dumps({"event": "START", "label": label, "utc": now()}), flush=True)
        with logfile.open("wb") as log:
            child = subprocess.Popen(argv, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
            while True:
                try:
                    code = child.wait(timeout=15)
                    break
                except subprocess.TimeoutExpired:
                    elapsed = time.time() - started
                    print(json.dumps({"event": "RUNNING", "label": label, "seconds": round(elapsed)}), flush=True)
                    if elapsed > args.step_timeout:
                        child.terminate()
                        try:
                            child.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            child.kill()
                            child.wait()
                        code = child.returncode
                        row["timeout"] = True
                        break
        row.update({"exit_code": code, "seconds": round(time.time() - started, 3),
                    "finished_utc": now(), "log_sha256": sha256(logfile)})
        record["steps"].append(row)
        checkpoint()
        print(json.dumps({"event": "END", "label": label, "exit_code": code, "seconds": row["seconds"]}), flush=True)
        if code or row.get("timeout"):
            raise RuntimeError(f"{label} failed; inspect {logfile}; no automatic rebuild or dependency change.")
        return row, logfile.read_text(errors="replace")

    try:
        record["git_head"] = capture(["git", "rev-parse", "HEAD"], repo)
        wanted_head = args.expected_head or plan["target_head"]
        record["expected_head"] = wanted_head
        if record["git_head"] != wanted_head:
            raise RuntimeError("Repository HEAD differs from the explicitly selected reproduction head.")
        record["tracked_project_status"] = capture(
            ["git", "status", "--porcelain", "--untracked-files=no", "--", plan["project_relative"]], repo)
        if record["tracked_project_status"]:
            raise RuntimeError("Tracked project changes must be resolved in the isolated checkout before reproduction.")
        mismatches = [rel for rel, value in expected["files"].items()
                      if not (project / rel).is_file() or blob(project / rel) != value]
        record["source_identity"] = {"compared_files": len(expected["files"]),
                                     "proof_baseline": expected["baseline"], "mismatches": mismatches}
        if mismatches:
            raise RuntimeError("Source/lock identity mismatch; do not reuse the old plan without review.")
        if (project / "lean-toolchain").read_text().strip() != plan["lean_toolchain"]:
            raise RuntimeError("Lean pin mismatch.")
        manifest = json.loads((project / "lake-manifest.json").read_text())
        package_rows = []
        for pkg in manifest["packages"]:
            p = project / manifest["packagesDir"] / pkg["name"]
            actual = capture(["git", "rev-parse", "HEAD"], p)
            dirty = capture(["git", "status", "--porcelain", "--untracked-files=no"], p)
            package_rows.append({"name": pkg["name"], "path": str(p.resolve()),
                                 "expected_rev": pkg["rev"], "actual_rev": actual, "tracked_status": dirty})
            if actual != pkg["rev"] or dirty:
                raise RuntimeError(f"Locked dependency {pkg['name']} is at a different or modified source revision.")
        record["dependency_sources"] = package_rows
        mathlib = next(x for x in package_rows if x["name"] == "mathlib")
        if mathlib["actual_rev"] != plan["mathlib_rev"]:
            raise RuntimeError("Mathlib pin mismatch.")

        inherited_lean_path = os.environ.get("LEAN_PATH", "")
        if not inherited_lean_path:
            raise RuntimeError("LEAN_PATH is empty. Invoke using the pinned project's lake env python3.")
        roots = [Path(p).resolve() if Path(p).is_absolute() else (project / p).resolve()
                 for p in inherited_lean_path.split(os.pathsep) if p]
        lean_command = shutil.which("lean")
        if not lean_command:
            raise RuntimeError("No lean executable in the pinned Lake environment.")
        prefix = Path(capture([lean_command, "--print-prefix"], project))
        direct_lean = prefix / "bin" / "lean"
        if not direct_lean.is_file():
            raise RuntimeError("Cannot bind the active Lean executable to its reported prefix.")
        lean = str(direct_lean.resolve())
        version = capture([lean, "--version"], project)
        if "4.33.1" not in version or plan["lean_commit"] not in version:
            raise RuntimeError("Actual Lean version/commit differs from the locked historical proof compiler.")
        lean_help = capture([lean, "--help"], project)
        (output / "LEAN_HELP.txt").write_text(lean_help + "\n")
        if "--deps" not in lean_help:
            raise RuntimeError("This fixed compiler did not advertise --deps; review the runner before changing commands.")
        record["compiler"] = {"command": lean, "sha256": sha256(lean), "version": version,
                              "prefix": str(prefix), "lake_version": capture(["lake", "--version"], project)}
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(overlay)] + [str(p) for p in roots])
        record["lean_path"] = env["LEAN_PATH"].split(os.pathsep)
        checkpoint()

        def dependency_trace(label, source, cwd):
            row, text = execute(label + "-deps", [lean, "--deps", source], cwd, env)
            items = []
            for line in text.splitlines():
                candidate = line.strip().strip('"')
                if not candidate.endswith(".olean"):
                    continue
                path = Path(candidate)
                if not path.is_absolute():
                    path = (cwd / path).resolve()
                if not path.is_file():
                    raise RuntimeError(f"Dependency path emitted by Lean is missing: {path}")
                item = {"path": str(path), "sha256": sha256(path),
                        "fresh_overlay": overlay == path.parent or overlay in path.parents,
                        "lake_trace_files": []}
                for trace in (path.with_suffix(".trace"), Path(str(path) + ".trace")):
                    if trace.is_file():
                        item["lake_trace_files"].append({"path": str(trace), "sha256": sha256(trace)})
                items.append(item)
            if not items:
                raise RuntimeError(f"No dependency paths parsed from {label}; inspect the compiler's actual format.")
            row["resolved_dependencies"] = items
            checkpoint()
            return items

        fresh_rows = []
        for index, item in enumerate(plan["fresh_modules"], 1):
            label = f"{index:02d}-" + item["module"].split(".")[-1]
            src = project / item["source"]
            dst = overlay / (item["module"].replace(".", "/") + ".olean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            if dst.exists():
                raise RuntimeError(f"Fresh output unexpectedly exists: {dst}")
            dependency_trace(label, item["source"], project)
            source_hash = sha256(src)
            record["fresh_lean_execution"] = True
            row, text = execute(label, [lean, "-o", str(dst), "-i", str(dst.with_suffix(".ilean")), item["source"]], project, env)
            if not dst.is_file() or src.is_file() and sha256(src) != source_hash:
                raise RuntimeError("Compiler did not produce its new artifact, or source changed while compiling.")
            if re.search(r"declaration uses.*sorry|sorryAx", text):
                raise RuntimeError("Unfinished proof reported during source recompilation.")
            artifacts = [{"path": str(p), "sha256": sha256(p), "bytes": p.stat().st_size,
                          "mtime_ns": p.stat().st_mtime_ns}
                         for p in sorted(dst.parent.glob(dst.stem + ".*")) if p.is_file()]
            row.update({"module": item["module"], "source": str(src), "source_git_blob": blob(src),
                        "source_sha256": source_hash, "new_artifacts": artifacts,
                        "warning_lines": [l for l in text.splitlines() if "warning:" in l]})
            fresh_rows.append(row)
            record["fresh_successful_source_count"] = len(fresh_rows)
            checkpoint()

        probe = probe_dir / "D3Probe.lean"
        shutil.copyfile(bundle / "D3Probe.lean", probe)
        if sha256(probe) != plan["probe_sha256"]:
            raise RuntimeError("Probe changed after its plan was fixed.")
        deps = dependency_trace("D3Probe", "D3Probe.lean", probe_dir)
        resolved = {str(Path(x["path"]).resolve()) for x in deps}
        required = {str((overlay / (x["module"].replace(".", "/") + ".olean")).resolve())
                    for x in plan["fresh_modules"]}
        if not required <= resolved:
            raise RuntimeError("Probe did not resolve every explicitly imported fresh module from the overlay: " + repr(sorted(required - resolved)))
        prow, probe_text = execute("D3Probe", [lean, "-o", str(overlay / "D3Probe.olean"),
                                               "-i", str(overlay / "D3Probe.ilean"), "D3Probe.lean"], probe_dir, env)
        parsed = {}
        pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
        for match in pattern.finditer(probe_text):
            parsed[match.group(1)] = [s.strip() for s in (match.group(2) or "").split(",") if s.strip()]
        axiom_results = []
        for endpoint in plan["endpoints"]:
            name = endpoint["name"]
            if name not in parsed:
                raise RuntimeError(f"No actual #print axioms output parsed for {name}; inspect output, do not invent a PASS.")
            axes = parsed[name]
            extra = [a for a in axes if a not in endpoint["allowed_axioms"]]
            suffix = endpoint.get("allowed_native_axiom_suffix")
            if suffix:
                if len(extra) != 1 or not (extra[0] == suffix or extra[0].endswith("." + suffix)):
                    raise RuntimeError(f"Disclosed native axiom identity changed for {name}: {extra}")
            elif extra:
                raise RuntimeError(f"Unexpected axioms for {name}: {extra}")
            axiom_results.append({"name": name, "axioms": axes, "evidence_mode": endpoint["evidence_mode"],
                                  "source": endpoint["source"], "role": endpoint["role"]})
        if not (overlay / "D3Probe.olean").is_file():
            raise RuntimeError("No new compiled probe artifact.")
        remaining = [rel for rel, value in expected["files"].items() if blob(project / rel) != value]
        if remaining:
            raise RuntimeError("Tracked proof/config source bytes changed during reproduction.")
        record.update({"status": "PASS_TARGETED_EXECUTION_REVIEW_REQUIRED", "finished_utc": now(),
                       "fresh_source_count": len(fresh_rows), "fresh_probe_endpoint_count": len(axiom_results),
                       "axiom_results": axiom_results,
                       "probe_source_sha256": sha256(probe), "probe_olean_sha256": sha256(overlay / "D3Probe.olean"),
                       "all_selected_imports_resolved_to_fresh_overlay": True,
                       "source_identity_unchanged_after": True,
                       "semantic_review_required": "Confirm printed Countable/discount/independent types/ValidIdentity/ProgramPopulation/positive branch/ProbabilityValid/full Policy/nonempty/expected-growth conditions against the fixed contract.",
                       "not_claimed": ["full clean build", "fresh recompilation of every imported dependency", "new native computation of the two cached numeric endpoints", "empirical validity", "global novelty"]})
        checkpoint()
        print(json.dumps({"event": "COMPLETE", "status": record["status"], "receipt": str(receipt_path)}), flush=True)
        return 0
    except Exception as exc:
        record.update({"status": "FAILED_OR_BLOCKED", "finished_utc": now(), "failure": str(exc)})
        checkpoint()
        print(json.dumps({"event": "STOP", "status": record["status"], "failure": str(exc), "receipt": str(receipt_path)}, ensure_ascii=False), flush=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
