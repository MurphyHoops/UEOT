#!/usr/bin/env python3
"""Read completed UEOT QM CI evidence; never run proof/runtime gates or write Core.

Uses authenticated gh for read-only API calls and artifact downloads. A directory
without this script's successful-download marker is not assumed complete. Existing
unmarked downloads are left untouched; a fresh sibling is used instead.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone, timedelta
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import traceback

REPO = "MurphyHoops/UEOT"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RUNTIME_FILES = {
    "finite_conditioning.py", "fixtures.py", "frozen_plan.json",
    "positive_chain_plan.json", "test_finite_conditioning.py", "exact_witnesses.py",
    "run_reference.py", "verify_runtime.py", "README.md",
}
PINS = {"numpy": "2.3.5", "scipy": "1.17.0", "sympy": "1.14.0"}
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def unique(directory, filename):
    paths = sorted(p for p in directory.rglob(filename) if p.is_file())
    require(len(paths) == 1, f"Expected one {filename} in {directory}; found {paths}")
    require(not paths[0].is_symlink(), f"Symlink is not accepted as raw evidence: {paths[0]}")
    return paths[0]


def inventory(directory):
    entries = []
    for path in sorted(directory.rglob("*")):
        require(not path.is_symlink(), f"Artifact symlink is outside this verifier's scope: {path}")
        if path.is_file():
            entries.append({"path": path.relative_to(directory).as_posix(),
                            "bytes": path.stat().st_size, "sha256": sha(path)})
    require(entries, f"Artifact directory has no files: {directory}")
    return entries


def utc(value):
    result = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(result.tzinfo is not None, f"Timestamp has no timezone: {value}")
    return result.astimezone(timezone.utc)


def axiom_requests(text):
    # These actual audit files contain only imports, comments and #print commands.
    # Remove nested Lean block comments and line comments before counting requests.
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif not depth and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i] if not depth or text[i] == "\n" else " ")
            i += 1
    require(depth == 0, "Unclosed Lean block comment in actual AxiomAudit.lean")
    return re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", "".join(out), re.M)


class Verification:
    def __init__(self, args):
        self.args = args
        self.root = args.repo_root.resolve(strict=True)
        self.private = self.root / ".physics-staging/ci" / f"{args.label}-{args.run_id}"
        self.private.mkdir(parents=True, exist_ok=True)
        self.api_dir = self.private / "api"
        self.api_dir.mkdir(exist_ok=True)
        self.commands = []
        self.result = {"schema": "ueot_qm.release_ci_verification.v1", "status": "IN_PROGRESS",
                       "repository": REPO, "run_id": args.run_id, "label": args.label,
                       "expected_head": args.expected_head, "expected_event": args.expected_event}

    def command(self, argv, timeout=60):
        try:
            r = subprocess.run(argv, cwd=self.root, capture_output=True, timeout=timeout)
        except (OSError, subprocess.TimeoutExpired) as exc:
            self.commands.append({"command": argv, "error": str(exc)})
            raise RuntimeError(f"Command did not finish successfully: {argv}: {exc}") from exc
        self.commands.append({"command": argv, "returncode": r.returncode})
        require(r.returncode == 0, f"Command failed ({r.returncode}): {argv}\n"
                + r.stderr.decode("utf-8", errors="replace")[-6000:])
        return r.stdout

    def api(self, endpoint, filename):
        raw = self.command(["gh", "api", "--method", "GET", endpoint])
        (self.api_dir / filename).write_bytes(raw)
        return json.loads(raw)

    def pages(self, endpoint, key, prefix):
        found, page = [], 1
        while True:
            join = "&" if "?" in endpoint else "?"
            data = self.api(f"{endpoint}{join}per_page=100&page={page}", f"{prefix}-page-{page}.json")
            batch = data[key]
            require(isinstance(batch, list), f"Invalid {key} API response")
            found.extend(batch)
            if len(found) >= data["total_count"]:
                require(len(found) == data["total_count"], f"Inconsistent paginated {key} count")
                return found
            require(batch, f"Pagination stopped before all {key} were returned")
            page += 1
            require(page <= 100, f"Unexpectedly large {key} response")

    def expected_source(self, relative):
        path = self.root / relative
        require(path.is_file() and not path.is_symlink(), f"Missing source file: {path}")
        committed = self.command(["git", "show", f"{self.args.expected_head}:{relative}"])
        require(hashlib.sha256(committed).hexdigest() == sha(path),
                f"Current source differs from expected-head git blob: {relative}")
        return path

    def download(self, kind, artifact):
        marker = self.private / f"{kind}-download.json"
        if marker.is_file():
            old = load(marker)
            directory = self.private / old.get("directory", "INVALID")
            require(directory.resolve().parent == self.private.resolve(), "Unsafe cached artifact directory")
            if (old.get("artifact_id") == artifact["id"] and old.get("run_id") == self.args.run_id
                    and old.get("expected_head") == self.args.expected_head
                    and old.get("download_returncode") == 0 and directory.is_dir()
                    and old.get("files") == inventory(directory)):
                return directory, old["files"], "REUSED_VERIFIED_SUCCESSFUL_DOWNLOAD"
        directory = self.private / kind
        if directory.exists() and any(directory.iterdir()):
            directory = Path(tempfile.mkdtemp(prefix=f"{kind}-fresh-", dir=self.private))
        else:
            directory.mkdir(exist_ok=True)
        self.command(["gh", "run", "download", str(self.args.run_id), "--repo", REPO,
                      "--name", artifact["name"], "--dir", str(directory)], timeout=180)
        files = inventory(directory)
        write_json(marker, {"artifact_id": artifact["id"], "run_id": self.args.run_id,
                           "expected_head": self.args.expected_head, "download_returncode": 0,
                           "directory": directory.name, "files": files})
        return directory, files, "FRESH_SUCCESSFUL_GH_DOWNLOAD"

    def verify_runtime(self, directory, job):
        names = ["execution_receipt.json", "semantic_tests.log", "exact_witnesses.json",
                 "exact_witnesses.log", "runtime_results.json", "numerical_reference.log"]
        files = {name: unique(directory, name) for name in names}
        receipt, exact, numeric = (load(files[n]) for n in
                                  ("execution_receipt.json", "exact_witnesses.json", "runtime_results.json"))
        require(receipt["status"] == "PASS" and receipt["source_unchanged_during_execution"] is True,
                "Actual runtime receipt is not PASS with unchanged source")
        require(set(receipt["source_sha256"]) == RUNTIME_FILES, "Runtime receipt does not bind exactly the nine expected sources")
        sources = {name: self.expected_source(f"physics/qm/conditioning/{name}") for name in sorted(RUNTIME_FILES)}
        for name, path in sources.items():
            require(sha(path) == receipt["source_sha256"][name], f"Runtime source hash mismatch: {name}")
        gates = receipt["gates"]
        require(len(gates) == 3 and {g["name"] for g in gates} ==
                {"semantic_tests", "exact_witnesses", "numerical_reference"}, "Unexpected runtime gates")
        begin, end = utc(job["started_at"]), utc(job["completed_at"])
        recorded = utc(receipt["executed_at_utc"])
        require(begin - timedelta(minutes=5) <= recorded <= end + timedelta(minutes=5),
                "Runtime receipt timestamp is outside the actual CI job interval")
        for gate in gates:
            require(gate["status"] == "PASS" and gate["returncode"] == 0, f"Failed runtime gate: {gate['name']}")
            require(gate["log"] == gate["name"] + ".log", "Unexpected runtime log path")
            require(sha(files[gate["log"]]) == gate["log_sha256"], f"Runtime log hash mismatch: {gate['name']}")
            require(math.isfinite(gate["seconds"]) and gate["seconds"] >= 0, "Invalid runtime gate duration")
            require(begin - timedelta(minutes=5) <= utc(gate["started_at_utc"]) <= recorded,
                    "Runtime gate timestamp is inconsistent with CI execution")
        semantic = files["semantic_tests.log"].read_text()
        require(re.search(r"Ran 19 tests in [^\n]+\n\s*\nOK\s*$", semantic), "Actual semantic log does not report 19 successful tests")
        require(exact["check_count"] == len(exact["checks"]) == 95 and
                all(c["status"] == "PASS_EXACT_SYMBOLIC" for c in exact["checks"]), "Expected 95 passing exact finite checks")
        require(len({c["name"] for c in exact["checks"]}) == 95, "Duplicate exact check names")
        require(exact["checker_sha256"] == sha(sources["exact_witnesses.py"]), "Exact checker hash mismatch")
        require(exact["plan_sha256"] == sha(sources["frozen_plan.json"]) and
                exact["positive_complete_chain"]["plan_sha256"] == sha(sources["positive_chain_plan.json"]), "Exact model plan hash mismatch")
        require(numeric["status"] == "PASS_NUMERICAL_REFERENCE_NOT_CERTIFIED_GENERAL_ALGORITHM", "Unexpected numerical evidence status")
        require(set(numeric["source_sha256"]) == RUNTIME_FILES - {"README.md", "verify_runtime.py"}, "Unexpected numerical source manifest")
        require(all(h == sha(sources[n]) for n, h in numeric["source_sha256"].items()), "Numerical source hash mismatch")
        require(numeric["plan_sha256"] == sha(sources["frozen_plan.json"]), "Numerical plan hash mismatch")
        versions = receipt["versions"]
        require(str(versions["python"]).startswith("3.12."), "CI Python is outside the requested 3.12 series")
        require(all(versions[p] == v for p, v in PINS.items()), "CI dependency versions differ from declared pins")
        require(exact["sympy_version"] == versions["sympy"] and
                all(numeric["versions"][p] == versions[p] for p in ("numpy", "scipy")), "Runtime evidence version disagreement")
        self.result["runtime"] = {"status": "PASS", "semantic_tests": 19, "exact_finite_checks": 95,
                                  "source_files": 9, "versions": versions, "executed_at_utc": receipt["executed_at_utc"],
                                  "source_sha256": receipt["source_sha256"], "gates": gates,
                                  "evidence_scope": receipt["evidence_scope"]}
        return files

    def verify_lean(self, directory):
        files = {name: unique(directory, name) for name in
                 ("source-identity.log", "lean-build.log", "axiom-audit.log", "proof-axioms.json")}
        identity = files["source-identity.log"].read_text().splitlines()
        require(identity and identity[0].strip() == self.args.expected_head, "Actual CI source-identity head differs")
        identity_count = 0
        for line in identity[1:]:
            if not line.strip():
                continue
            match = re.fullmatch(r"([0-9a-f]{64})\s+[* ]?(.+)", line)
            require(match, f"Unrecognized source-identity record: {line}")
            digest, name = match.groups()
            relative = PurePosixPath(name)
            require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe source identity path")
            path = self.root / "formalization/ueot-qm" / name
            require(path.is_file() and sha(path) == digest, f"Current Lean source identity mismatch: {name}")
            identity_count += 1
        require(identity_count > 0, "CI source identity lacks actual file hashes")
        build = ANSI.sub("", files["lean-build.log"].read_text())
        require(re.search(r"\bBuild completed successfully\b", build), "Actual Lean build log lacks its success completion")
        require(not re.search(r"^\s*error:", build, re.M), "Actual Lean build log contains an error")
        audit_source = self.expected_source("formalization/ueot-qm/scripts/AxiomAudit.lean")
        requests = axiom_requests(audit_source.read_text())
        require(len(requests) == 1285 and len(set(requests)) == 1285, "Expected 1285 distinct actual AxiomAudit requests")
        text = ANSI.sub("", files["axiom-audit.log"].read_text())
        reports = re.findall(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.M)
        require(len(reports) == 1285 and all(c == 1 for c in Counter(n for n, _ in reports).values()), "Missing/duplicate actual Lean axiom reports")
        actual = {name: sorted(a.strip() for a in axioms.split(",") if a.strip()) for name, axioms in reports}
        require(set(actual) == set(requests), "Actual axiom report names differ from requested source names: " + repr(sorted(set(actual) ^ set(requests))))
        bad = {name: sorted(set(axioms) - ALLOWED) for name, axioms in actual.items() if not set(axioms) <= ALLOWED}
        require(not bad, "Unreviewed Lean axiom dependencies: " + repr(bad))
        proof = load(files["proof-axioms.json"])
        require(proof["status"] == "PASS" and proof["declaration_count"] == 1285 and
                set(proof["allowed_foundation"]) == ALLOWED and proof["declarations"] == actual,
                "Archived proof-axioms.json disagrees with actual axiom log")
        self.result["lean"] = {"status": "PASS", "named_axiom_reports": 1285,
                               "allowed_axioms": sorted(ALLOWED), "axiom_requests_sha256": sha(audit_source),
                               "source_identity_hashed_files": identity_count,
                               "scope": "actual complete public build and 1285 requested named declarations; not a census of compiler-generated constants"}
        # Preserve these additional original files when uniquely present. Multiple
        # same-name records are an ambiguity, never silently resolved by ordering.
        for name in ("source-manifest.json", "lean-install.log", "lake-manifest.json"):
            if list(directory.rglob(name)):
                files[name] = unique(directory, name)
        return files

    def run(self):
        top = self.command(["git", "rev-parse", "--show-toplevel"]).decode().strip()
        require(Path(top).resolve() == self.root, "--repo-root must be the actual git repository root")
        self.result["local_head_at_verification"] = self.command(["git", "rev-parse", "HEAD"]).decode().strip()
        run = self.api(f"repos/{REPO}/actions/runs/{self.args.run_id}", "run.json")
        self.result["run"] = run
        require(run["id"] == self.args.run_id, "GitHub returned a different run id")
        require(run["status"] == "completed" and run["conclusion"] == "success", "CI is not completed/success; no wait or polling is performed")
        require(run["head_sha"] == self.args.expected_head and run["event"] == self.args.expected_event, "CI head or event mismatch")
        require(run["path"] == ".github/workflows/ueot-qm.yml", "Run belongs to another workflow")
        require(run["repository"]["full_name"].lower() == REPO.lower(), "CI repository mismatch")
        attempt = run["run_attempt"]
        jobs = self.pages(f"repos/{REPO}/actions/runs/{self.args.run_id}/attempts/{attempt}/jobs", "jobs", "jobs")
        require(len(jobs) == 2 and {j["name"] for j in jobs} == {"runtime", "lean"}, "Expected exactly the actual runtime and lean jobs")
        for job in jobs:
            require(job["run_id"] == self.args.run_id and job["head_sha"] == self.args.expected_head, "Job run/head mismatch")
            require(job["status"] == "completed" and job["conclusion"] == "success", f"Job failed: {job['name']}")
            require(job["steps"] and all(s["status"] == "completed" and s["conclusion"] in {"success", "skipped"} for s in job["steps"]), f"Incomplete or unsuccessful step in {job['name']}")
        self.result["jobs"] = jobs
        by_job = {j["name"]: j for j in jobs}
        lean_steps = {s["name"]: s for s in by_job["lean"]["steps"]}
        for name in ("Build all QM proofs", "Audit theorem axioms", "Verify generated exact certificates and false witnesses", "Verify retained finite and quantum Lean witnesses"):
            require(name in lean_steps and lean_steps[name]["conclusion"] == "success", f"Required Lean CI gate did not succeed: {name}")
        artifacts = self.pages(f"repos/{REPO}/actions/runs/{self.args.run_id}/artifacts", "artifacts", "artifacts")
        retained, artifacts_result, inventories = {}, {}, {}
        for kind in ("runtime", "lean"):
            name = f"ueot-qm-{kind}-{self.args.run_id}"
            matching = [a for a in artifacts if a["name"] == name and not a["expired"]]
            require(len(matching) == 1, f"Expected one unexpired artifact named {name}; found {len(matching)}")
            artifact = matching[0]
            require(artifact.get("workflow_run", {}).get("id") == self.args.run_id, "Artifact run identity mismatch")
            require(artifact.get("workflow_run", {}).get("head_sha") == self.args.expected_head, "Artifact head identity mismatch")
            directory, entries, mode = self.download(kind, artifact)
            artifacts_result[kind] = {"github_metadata": artifact, "download_mode": mode,
                                      "local_directory": str(directory.relative_to(self.root)),
                                      "downloaded_file_count": len(entries),
                                      "hash_scope": "SHA256 of every extracted file; remote API digest is retained as metadata, not a locally verified raw-zip hash"}
            inventories[kind] = entries
            retained[kind] = self.verify_runtime(directory, by_job[kind]) if kind == "runtime" else self.verify_lean(directory)
            require(inventory(directory) == entries, f"Artifact files changed during {kind} verification")
        self.result["artifacts"] = artifacts_result
        self.result["counts"] = {"ci_jobs": 2, "runtime_semantic_tests": 19,
                                 "runtime_exact_finite_checks": 95, "runtime_source_files": 9,
                                 "requested_named_axiom_reports": 1285}
        self.result["count_scope"] = "19 actual unittest tests; 95 exact finite symbolic checks; 9 runtime source files; 1285 named axiom requests/reports. No new count of the separate 155-file proof closure is inferred."
        self.result["head_sha"], self.result["event"] = run["head_sha"], run["event"]
        self.result["run_url"], self.result["run_attempt"] = run["html_url"], attempt
        self.result["status"] = "PASS"
        self.result["verified_at_utc"] = datetime.now(timezone.utc).isoformat()
        self.result["commands"] = self.commands
        self.result["verifier_sha256"] = sha(Path(__file__))
        self.result["raw_zip_hash_computed"] = False
        self.result["scientific_gates_reexecuted"] = False
        destination = self.root / "physics/qm/kernel/evidence/v31.10/ci" / f"{self.args.label}-{self.args.run_id}"
        destination.mkdir(parents=True, exist_ok=True)
        copied = []
        for group, paths in retained.items():
            for name, source in paths.items():
                target = destination / group / name
                target.parent.mkdir(exist_ok=True)
                require(not target.exists() or sha(target) == sha(source), f"Refusing to overwrite different retained raw evidence: {target}")
                if not target.exists():
                    shutil.copyfile(source, target)
                copied.append({"path": target.relative_to(destination).as_posix(), "sha256": sha(target),
                               "artifact_relative_path": source.relative_to(self.root / artifacts_result[group]["local_directory"]).as_posix()})
        for source in sorted(self.api_dir.glob("*.json")):
            target = destination / "api" / source.name
            target.parent.mkdir(exist_ok=True)
            # API metadata is a timestamped current observation; raw artifact logs
            # above remain immutable. Keep the exact API stdout bytes.
            shutil.copyfile(source, target)
            copied.append({"path": target.relative_to(destination).as_posix(), "sha256": sha(target)})
        write_json(destination / "artifact-file-inventory.json", {"schema": "ueot_qm.extracted_artifact_inventory.v1",
                   "repository": REPO, "run_id": self.args.run_id, "artifacts": artifacts_result,
                   "files": inventories, "raw_zip_hash_computed": False})
        self.result["copied_raw_evidence"] = copied
        self.result["artifact_inventory_sha256"] = sha(destination / "artifact-file-inventory.json")
        write_json(destination / "verification.json", self.result)
        print(json.dumps({"status": "PASS", "verification": str(destination / "verification.json"), "counts": self.result["counts"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--run-id", type=int, required=True)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--expected-event", required=True)
    parser.add_argument("--label", choices=("pr", "main"), required=True)
    args = parser.parse_args()
    if args.run_id <= 0 or not re.fullmatch(r"[0-9a-f]{40}", args.expected_head):
        parser.error("run-id must be positive and expected-head a lowercase full 40-character SHA")
    verification = None
    try:
        verification = Verification(args)
        verification.run()
    except Exception as exc:
        failure = {"schema": "ueot_qm.release_ci_verification_failure.v1", "status": "FAILED",
                   "repository": REPO, "run_id": args.run_id, "expected_head": args.expected_head,
                   "expected_event": args.expected_event, "error_type": type(exc).__name__,
                   "message": str(exc), "traceback": traceback.format_exc(),
                   "recorded_at_utc": datetime.now(timezone.utc).isoformat()}
        if verification is not None:
            failure["commands"] = verification.commands
            failure["partial_observations"] = verification.result
            path = verification.private / "verification.failure.json"
            write_json(path, failure)
            failure["failure_receipt"] = str(path)
        print(json.dumps({k: failure[k] for k in ("status", "message", "failure_receipt") if k in failure}), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
