#!/usr/bin/env python3
"""Targeted UEOT reproduction. Run with the pinned project's `lake env python3`.

Writes only a newly created output directory outside the project. It never runs
lake build, updates dependencies, edits source, or labels a reused proof fresh.
This script and its Lean probe are PREPARED, NOT EXECUTED, until a run receipt says otherwise.
V2 fixes Lean's top-level namespace-root selection by mirroring the existing
project cache with file symlinks, while reserving every fresh target artifact.
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


def is_protected_artifact(relative_path, protected_stems, is_directory=False):
    """Reserve every target stem extension, including private/server/trace files.

    A namespace DIRECTORY equal to a stem (notably UEOT/) must still be mirrored.
    It is not the UEOT.olean output. Never symlink any directory.
    """
    rel = Path(relative_path).as_posix()
    return any(rel.startswith(stem + ".") or
               (not is_directory and rel == stem) for stem in protected_stems)


def snapshot_cached_targets(cache_root, protected_stems):
    """Hash only existing artifacts of selected stems, before any overlay exists."""
    cache_root = Path(cache_root).resolve(strict=True)
    files = {}

    def visit(path, ancestors):
        real = path.resolve(strict=True)
        if path.is_dir():
            if real in ancestors:
                raise RuntimeError(f"Cycle in selected cached artifacts: {path}")
            for child in sorted(path.iterdir(), key=lambda p: p.name):
                visit(child, ancestors | {real})
        elif path.is_file():
            rel = path.relative_to(cache_root).as_posix()
            files[rel] = {"relative_path": rel, "reported_path": str(path),
                          "resolved_path": str(real), "bytes": real.stat().st_size,
                          "sha256": sha256(real)}
        else:
            raise RuntimeError(f"Broken or special selected cached artifact: {path}")

    for stem in sorted(protected_stems):
        base = cache_root / stem
        for path in sorted(base.parent.glob(base.name + ".*")):
            visit(path, set())
        if os.path.lexists(base) and not base.is_dir():
            visit(base, set())
    return [files[key] for key in sorted(files)]


def compare_cached_targets(before, after):
    old = {x["relative_path"]: x for x in before}
    new = {x["relative_path"]: x for x in after}
    changes = []
    for name in sorted(set(old) | set(new)):
        a, b = old.get(name), new.get(name)
        if a is None or b is None or any(a[k] != b[k] for k in ("resolved_path", "bytes", "sha256")):
            changes.append({"relative_path": name, "before": a, "after": b})
    return {"status": "UNCHANGED" if not changes else "CHANGED", "before_count": len(before),
            "after_count": len(after), "changes": changes}


def mirror_project_cache(cache_root, overlay, protected_stems):
    cache_root = Path(cache_root).resolve(strict=True)
    overlay = Path(overlay).resolve(strict=True)
    links = []
    excluded = []
    directory_count = 0

    def visit(source_directory, relative_directory, ancestors):
        nonlocal directory_count
        real_directory = source_directory.resolve(strict=True)
        if real_directory in ancestors:
            raise RuntimeError(f"Directory symlink cycle in existing project cache: {source_directory}")
        ancestors = ancestors | {real_directory}
        destination = overlay / relative_directory
        if destination.is_symlink():
            raise RuntimeError(f"Overlay directory must be physical, not a symlink: {destination}")
        destination.mkdir(parents=True, exist_ok=True)
        directory_count += 1
        for entry in sorted(source_directory.iterdir(), key=lambda p: p.name):
            relative = relative_directory / entry.name
            directory = entry.is_dir()
            if is_protected_artifact(relative, protected_stems, directory):
                real = entry.resolve(strict=True)
                row = {"relative_path": relative.as_posix(), "source_path": str(entry),
                       "resolved_source_path": str(real), "directory": directory}
                if not directory:
                    if not real.is_file():
                        raise RuntimeError(f"Unsupported target artifact in cache: {entry}")
                    row["bytes"] = real.stat().st_size
                excluded.append(row)
                continue
            if directory:
                visit(entry, relative, ancestors)
            elif entry.is_file():
                real = entry.resolve(strict=True)
                target = overlay / relative
                if os.path.lexists(target):
                    raise RuntimeError(f"Overlay link slot already exists: {target}")
                target.symlink_to(real)
                links.append({"overlay_path": str(target), "source_path": str(entry),
                              "resolved_source_path": str(real)})
            else:
                raise RuntimeError(f"Missing/broken or special cache entry: {entry}")

    visit(cache_root, Path(), set())
    return {"source_cache_root": str(cache_root), "overlay_root": str(overlay),
            "linked_file_count": len(links), "linked_directory_count": 0,
            "materialized_directory_count": directory_count,
            "protected_stems": sorted(protected_stems),
            "excluded_target_artifacts": excluded, "file_links": links}


def classify_dependency(reported, cwd, overlay):
    """Resolve absolute and relative Lean output alike; do not call links fresh."""
    raw = Path(reported)
    absolute = Path(os.path.abspath(raw if raw.is_absolute() else Path(cwd) / raw))
    resolved = absolute.resolve(strict=True)
    if not resolved.is_file():
        raise RuntimeError(f"Dependency path emitted by Lean is not a file: {absolute}")
    overlay = Path(overlay).resolve(strict=True)
    return {"reported_path": reported, "absolute_reported_path": str(absolute),
            "resolved_path": str(resolved), "path": str(resolved),
            "fresh_overlay": overlay == resolved.parent or overlay in resolved.parents,
            "reported_path_is_symlink": absolute.is_symlink()}


def require_fresh_slot(path, overlay):
    """All output parents are real directories; no old target artifact is linked."""
    path = Path(path)
    overlay = Path(overlay).resolve(strict=True)
    if os.path.lexists(path):
        raise RuntimeError(f"Fresh output slot already exists, including a dangling link: {path}")
    parent = path.parent
    while parent != overlay:
        if parent.is_symlink() or overlay not in parent.parents:
            raise RuntimeError(f"Unsafe output parent: {parent}")
        parent = parent.parent
    for artifact in path.parent.glob(path.stem + ".*"):
        raise RuntimeError(f"Fresh target already has a sibling artifact: {artifact}")


def require_regular_fresh_file(path, overlay):
    path = Path(path)
    overlay = Path(overlay).resolve(strict=True)
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"Fresh compiler artifact is missing or is a symlink: {path}")
    resolved = path.resolve(strict=True)
    if resolved != path.absolute() or overlay not in resolved.parents:
        raise RuntimeError(f"Fresh compiler artifact resolves outside its physical slot: {path}")


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
    for p in (logs, probe_dir):
        p.mkdir()
    record = {
        "schema": plan["schema"], "runner_revision": 2,
        "status": "RUNNING", "started_utc": now(),
        "scope": plan["scope"], "repo": str(repo), "project": str(project),
        "output": str(output), "fresh_lean_execution": False,
        "full_clean_build": False, "reused_dependencies": True,
        "production_source_mutations": False, "steps": [],
        "bundle_sha256": {p.name: sha256(p) for p in
                          [Path(__file__), bundle / "D3_PLAN.json", bundle / "EXPECTED_SOURCE_BLOBS.json", bundle / "D3Probe.lean"]},
    }
    receipt_path = output / "D3_RECEIPT.json"
    old_cache_snapshot = None
    selected_cache_root = None
    protected_stems = None

    def checkpoint():
        save(receipt_path, record)

    def check_old_cache_after():
        if old_cache_snapshot is None:
            return None
        after = snapshot_cached_targets(selected_cache_root, protected_stems)
        comparison = compare_cached_targets(old_cache_snapshot, after)
        comparison["checked_utc"] = now()
        after_path = output / "OLD_TARGET_CACHE_AFTER.json"
        save(after_path, after)
        comparison["snapshot_path"] = str(after_path)
        comparison["snapshot_sha256"] = sha256(after_path)
        record["old_target_cache_after"] = comparison
        checkpoint()
        return comparison

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
        cache_roots = sorted({p.resolve(strict=True) for p in roots
                              if (p / "UEOT.olean").is_file() and (p / "UEOT").is_dir()}, key=str)
        if len(cache_roots) != 1:
            raise RuntimeError("Expected one real project cache root containing UEOT.olean and UEOT/: " + repr(cache_roots))
        protected_stems = {x["module"].replace(".", "/") for x in plan["fresh_modules"]} | {"D3Probe"}
        selected_cache_root = cache_roots[0]
        old_cache_snapshot = snapshot_cached_targets(selected_cache_root, protected_stems)
        before_path = output / "OLD_TARGET_CACHE_BEFORE.json"
        save(before_path, old_cache_snapshot)
        record["old_target_cache_before"] = {"source_cache_root": str(selected_cache_root),
            "artifact_count": len(old_cache_snapshot), "checked_utc": now(),
            "snapshot_path": str(before_path), "snapshot_sha256": sha256(before_path)}
        checkpoint()
        overlay.mkdir()
        cache_mirror = mirror_project_cache(selected_cache_root, overlay, protected_stems)
        mirror_manifest_path = output / "CACHE_MIRROR_MANIFEST.json"
        save(mirror_manifest_path, cache_mirror)
        record["cache_mirror"] = {k: v for k, v in cache_mirror.items() if k != "file_links"}
        record["cache_mirror"]["manifest_path"] = str(mirror_manifest_path)
        record["cache_mirror"]["manifest_sha256"] = sha256(mirror_manifest_path)
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
                item = classify_dependency(candidate, cwd, overlay)
                resolved = Path(item["resolved_path"])
                item.update({"sha256": sha256(resolved), "lake_trace_files": []})
                trace_paths = set()
                for path in (Path(item["absolute_reported_path"]), resolved):
                    for trace in (path.with_suffix(".trace"), Path(str(path) + ".trace")):
                        if trace.is_file():
                            real_trace = trace.resolve(strict=True)
                            if real_trace not in trace_paths:
                                trace_paths.add(real_trace)
                                item["lake_trace_files"].append({"reported_path": str(trace),
                                    "resolved_path": str(real_trace), "sha256": sha256(real_trace)})
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
            require_fresh_slot(dst, overlay)
            dependency_trace(label, item["source"], project)
            source_hash = sha256(src)
            record["fresh_lean_execution"] = True
            row, text = execute(label, [lean, "-o", str(dst), "-i", str(dst.with_suffix(".ilean")), item["source"]], project, env)
            require_regular_fresh_file(dst, overlay)
            if sha256(src) != source_hash:
                raise RuntimeError("Source changed while compiling.")
            if re.search(r"declaration uses.*sorry|sorryAx", text):
                raise RuntimeError("Unfinished proof reported during source recompilation.")
            artifact_paths = [p for p in sorted(dst.parent.glob(dst.stem + ".*")) if p.is_file()]
            for artifact in artifact_paths:
                require_regular_fresh_file(artifact, overlay)
            artifacts = [{"path": str(p), "sha256": sha256(p), "bytes": p.stat().st_size,
                          "mtime_ns": p.stat().st_mtime_ns}
                         for p in artifact_paths]
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
        resolved = {x["resolved_path"] for x in deps if x["fresh_overlay"]}
        fresh_target_paths = [overlay / (x["module"].replace(".", "/") + ".olean")
                              for x in plan["fresh_modules"]]
        for path in fresh_target_paths:
            require_regular_fresh_file(path, overlay)
        required = {str(path.resolve(strict=True)) for path in fresh_target_paths}
        if not required <= resolved:
            raise RuntimeError("Probe did not resolve every explicitly imported fresh module from the overlay: " + repr(sorted(required - resolved)))
        require_fresh_slot(overlay / "D3Probe.olean", overlay)
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
        require_regular_fresh_file(overlay / "D3Probe.olean", overlay)
        remaining = [rel for rel, value in expected["files"].items() if blob(project / rel) != value]
        if remaining:
            raise RuntimeError("Tracked proof/config source bytes changed during reproduction.")
        old_cache_check = check_old_cache_after()
        if old_cache_check["status"] != "UNCHANGED":
            raise RuntimeError("Existing cached target artifacts changed during isolated compilation; inspect the before/after records.")
        record.update({"status": "PASS_TARGETED_EXECUTION_REVIEW_REQUIRED", "finished_utc": now(),
                       "fresh_source_count": len(fresh_rows), "fresh_probe_endpoint_count": len(axiom_results),
                       "axiom_results": axiom_results,
                       "probe_source_sha256": sha256(probe), "probe_olean_sha256": sha256(overlay / "D3Probe.olean"),
                       "all_selected_imports_resolved_to_fresh_overlay": True,
                       "all_fresh_targets_are_regular_files": True,
                       "excluded_old_target_artifacts_unchanged": True,
                       "source_identity_unchanged_after": True,
                       "semantic_review_required": "Confirm printed Countable/discount/independent types/ValidIdentity/ProgramPopulation/positive branch/ProbabilityValid/full Policy/nonempty/expected-growth conditions against the fixed contract.",
                       "not_claimed": ["full clean build", "fresh recompilation of every imported dependency", "new native computation of the two cached numeric endpoints", "empirical validity", "global novelty"]})
        checkpoint()
        print(json.dumps({"event": "COMPLETE", "status": record["status"], "receipt": str(receipt_path)}), flush=True)
        return 0
    except Exception as exc:
        record.update({"status": "FAILED_OR_BLOCKED", "finished_utc": now(), "failure": str(exc)})
        try:
            check_old_cache_after()
        except Exception as cache_exc:
            record["old_target_cache_after"] = {"status": "CHECK_FAILED", "failure": str(cache_exc)}
        checkpoint()
        print(json.dumps({"event": "STOP", "status": record["status"], "failure": str(exc), "receipt": str(receipt_path)}, ensure_ascii=False), flush=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
