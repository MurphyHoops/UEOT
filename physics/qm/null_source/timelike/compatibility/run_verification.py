"""Verify the new compatibility results, reusing byte-identical prior proofs.

The predecessor's 5 + 9 scientific entries are NOT rerun. Their archived local
receipts and exact-head public CI observation are checked against a fixed Git
baseline. Four new checkers run in separate, unoptimized Python processes.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BASE = "1a90c68b6178968e6b8239fc97a8b26200f8d59d"
BASE_CI = 44491673166
WORKFLOW = ".github/workflows/ueot-physics-source-response.yml"
INHERITED_RANGES = [
    "physics/qm/null_source/timelike/continuation/",
    "physics/qm/null_source/timelike/evolution/",
    "physics/qm/null_source/timelike/instrument/",
    "physics/qm/null_source/timelike/identification/",
    "physics/qm/null_source/FINITE_WINDOW.md",
    "physics/qm/status/CURRENT.json",
    "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean",
]
CURRENT_DOCUMENTS = [
    WORKFLOW,
    "physics/qm/README.md",
    "physics/qm/ROADMAP.md",
    "physics/qm/null_source/timelike/README.md",
]
DEPENDENCIES = {
    "numpy": "2.5.4", "scipy": "1.18.1",
    "sympy": "1.14.0", "mpmath": "1.3.0",
}
ENTRIES = [
    ("state_transport_and_repair", "state/check.py"),
    ("homothetic_stress_and_uniform_defect", "scaling/check.py"),
    ("constraint_roots_and_positive_sources", "constraints/constraints.py"),
    ("independent_uniform_stress_and_noise_review", "review.py"),
]

def digest(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    return digest(path.read_bytes())

def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO)

def git_names(*args):
    return {name.decode("utf-8") for name in git(*args).split(b"\0") if name}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def inherited_manifest():
    baseline = git_names("ls-tree", "-rz", "--name-only", BASE, "--", *INHERITED_RANGES)
    present = git_names("ls-files", "-z", "--cached", "--others", "--exclude-standard",
                        "--", *INHERITED_RANGES)
    require(baseline == present,
            "Inherited proof inventory changed; new baseline review required: " +
            repr({"added": sorted(present-baseline), "removed": sorted(baseline-present)}))
    require(len(baseline) == 59, "Unexpected predecessor file count")
    manifest = {}
    for rel in sorted(baseline):
        path = REPO / rel
        require(path.is_file() and not path.is_symlink(), "Missing/nonregular input: " + rel)
        expected = digest(git("show", BASE + ":" + rel))
        actual = file_sha(path)
        require(actual == expected, "Inherited source bytes changed: " + rel)
        manifest[rel] = actual
    return manifest

def current_manifest():
    files = [p for p in HERE.rglob("*")
             if p.is_file() and "__pycache__" not in p.parts
             and p != HERE / "verification.json" and p.suffix in {".py", ".md", ".json"}]
    files += [REPO / rel for rel in CURRENT_DOCUMENTS]
    return {str(p.relative_to(REPO)): file_sha(p) for p in sorted(set(files))}

def predecessor_evidence(inherited):
    snapshot_path = HERE / "baseline_ci.json"
    snapshot = json.loads(snapshot_path.read_text())
    run = snapshot["run"]
    require(run["id"] == BASE_CI and run["head_sha"] == BASE and
            run["status"] == "completed" and run["conclusion"] == "success" and
            run["path"] == WORKFLOW, "Predecessor CI identity/status mismatch")
    require(run["html_url"] ==
            "https://github.com/MurphyHoops/UEOT/actions/runs/" + str(BASE_CI),
            "Unexpected predecessor CI URL")
    job = next(j for j in snapshot["jobs"] if j["name"] == "reproduce")
    require(job["head_sha"] == BASE and job["status"] == "completed" and
            job["conclusion"] == "success", "Predecessor job did not pass this head")
    step_names = [
        "Reproduce source binding, stress, apparatus and finite-data results",
        "Reproduce dynamic stress, initial constraint and finite-window inference",
    ]
    for name in step_names:
        step = next(s for s in job["steps"] if s["name"] == name)
        require(step["conclusion"] == "success" and step["status"] == "completed",
                "Predecessor scientific step not successful: " + name)
    receipts = []
    for directory, field, count in [
        ("continuation", "new_entry_results", 5),
        ("evolution", "entries", 9),
    ]:
        rel = "physics/qm/null_source/timelike/" + directory + "/verification.json"
        old = json.loads((REPO / rel).read_text())
        rows = old[field]
        require(len(rows) == count and all(row["returncode"] == 0 for row in rows),
                "Archived predecessor receipt not fully passed: " + directory)
        for key in ["current_source_manifest", "inherited_inputs_unchanged"]:
            for name, expected in old[key].items():
                require(name in inherited and inherited[name] == expected,
                        "Transitive predecessor input not frozen: " + name)
        receipts.append({
            "path": rel, "sha256": inherited[rel],
            "local_git_head_at_execution": old["git_head_at_execution"],
            "passed_entries": [row["entry"] for row in rows],
            "entry_count": count,
            "executed_again_this_run": False,
        })
    return {
        "base_commit": BASE, "exact_head_ci": run,
        "ci_snapshot_path": str(snapshot_path.relative_to(REPO)),
        "ci_snapshot_sha256": file_sha(snapshot_path),
        "ci_snapshot_semantics": snapshot["semantics"],
        "old_workflow_sha256": digest(git("show", BASE + ":" + WORKFLOW)),
        "archived_local_receipts": receipts,
        "entry_count_reused": 14,
        "current_old_inputs_equal_base": True,
        "inherited_file_count": len(inherited),
        "inherited_source_manifest": inherited,
    }

def scientific_exit():
    result = json.loads((HERE / "review.json").read_text())
    require(result["new_mode_integrations"] == 0, "Unexpected new integrations")
    model = result["physical_models"]
    require(model["infinite_field_included"] and model["defect_covariantly_conserved"],
            "Full-field conserved defect not certified")
    exact = model["exact_correlated_source"]
    rational = model["explicit_rational_source"]
    require(exact["initial_density_defect"] == "0" and
            exact["initial_momentum_defect"] == "0" and
            exact["Qeff0_and_M2_are_correlated"], "Exact source correlation lost")
    require(Fraction(exact["M2_interval"][0]) > 0 and Fraction(rational["M2"]) > 0,
            "Source must remain positive")
    for row in [exact, rational]:
        for key in ["uniform_density_relative_defect_upper",
                    "uniform_pressure_relative_defect_upper"]:
            require(0 <= Fraction(row[key]) < Fraction(1,100), "One-percent gate failed")
    require(not rational["is_exact_initial_constraint_solution"],
            "Finite-precision source mislabeled as exact")
    require(Fraction(rational["initial_Einstein_nn_relative_abs_upper"]) <
            Fraction(1,500000), "Explicit source initial residual exceeded budget")
    noise = model["retained_source_mixture_noise"]
    for key in ["relative_to_total_mean_squared_lower",
                "explicit_source_relative_to_total_mean_squared_lower"]:
        require(Fraction(noise[key]) > Fraction(1499,2000), "Noise lower gate failed")
    for key in ["distance_to_an_exact_metric_certified",
                "existence_of_an_exact_nearby_solution_proved",
                "global_asymptotically_flat_extension_constructed",
                "physical_instrument_implementation_certified"]:
        require(model[key] is False, "Unproved scope upgraded: " + key)
    return {
        "lambda": model["lambda"],
        "exact_correlated_source": exact,
        "explicit_rational_source": rational,
        "retained_source_mixture_noise": noise,
        "infinite_field_uniform_mean_equation_defect": "CERTIFIED",
        "full_exact_semiclassical_evolution_and_stability": "OPEN",
        "global_state_and_instrument_realization": "OPEN",
        "new_Lean_proofs": False, "new_matching_hardware_data": False,
        "Core_unique_physical_selection": "OPEN", "whole_unified_physics_goal": "OPEN",
    }

def main():
    require(__debug__ and sys.flags.optimize == 0, "Proof assertions require nonoptimized Python")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    parser.add_argument("--logs", type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    logs = (args.logs or Path(tempfile.mkdtemp(prefix="ueot-compatibility-logs-"))).resolve()
    require(REPO not in logs.parents and logs != REPO, "Logs must be outside the repository")
    require(output == HERE / "verification.json" or
            (REPO not in output.parents and output != REPO),
            "Only the default verification.json may be written inside the repository")
    logs.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    require(sys.version_info[:2] == (3,14), "Replay requires Python 3.14")
    actual_versions = {name: version(name) for name in DEPENDENCIES}
    require(actual_versions == DEPENDENCIES, "Scientific dependency versions changed")
    before_old = inherited_manifest()
    reused = predecessor_evidence(before_old)
    before_new = current_manifest()
    execution_head = git("rev-parse", "HEAD").decode().strip()
    execution_status = git("status", "--short").decode()
    env = os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1",
                "PYTHONDONTWRITEBYTECODE": "1"})
    rows = []
    for name, relative in ENTRIES:
        command = [sys.executable, "-B", str(HERE / relative), "--check"]
        started = time.monotonic()
        completed = subprocess.run(command, cwd=REPO, env=env, capture_output=True, timeout=120)
        stdout_path = logs / (name + ".stdout.txt")
        stderr_path = logs / (name + ".stderr.txt")
        stdout_path.write_bytes(completed.stdout)
        stderr_path.write_bytes(completed.stderr)
        row = {
            "entry": name, "source": str((HERE/relative).relative_to(REPO)),
            "arguments": ["--check"], "returncode": completed.returncode,
            "duration_seconds": round(time.monotonic()-started,3),
            "stdout_sha256": digest(completed.stdout),
            "stderr_sha256": digest(completed.stderr),
            "stdout_path": str(stdout_path), "stderr_path": str(stderr_path),
        }
        rows.append(row)
        print(("PASS" if completed.returncode == 0 else "FAIL") + ": " + name, flush=True)
        if completed.returncode:
            print(completed.stdout.decode(errors="replace"), flush=True)
            print(completed.stderr.decode(errors="replace"), flush=True)
    require(before_old == inherited_manifest(), "Inherited input changed during execution")
    require(before_new == current_manifest(), "New source changed during execution")
    successful = all(row["returncode"] == 0 for row in rows)
    science = scientific_exit() if successful else {"status": "FAILED_NEW_CHECK"}
    report = {
        "schema": "ueot-compatibility-verification/1",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "git_head_at_execution": execution_head,
        "working_tree_status_before_execution": execution_status,
        "receipt_generated_before_commit_if_worktree_dirty": bool(execution_status),
        "python": sys.version, "platform": platform.platform(),
        "dependencies": actual_versions,
        "process_environment": {key:env[key] for key in
                                ["OPENBLAS_NUM_THREADS","OMP_NUM_THREADS","PYTHONDONTWRITEBYTECODE"]},
        "reused": reused, "executed_now": rows,
        "current_source_manifest": before_new,
        "source_manifests_unchanged_after_execution": True,
        "new_mode_integrations": 0, "old_scientific_entries_rerun": 0,
        "scientific_exit": science, "status": "PASS" if successful else "FAIL",
    }
    output.write_text(json.dumps(report,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 14 earlier entries with 59 byte-identical inputs; executed 4 new entries.")
    print("Receipt: " + str(output))
    return 0 if successful else 1

if __name__ == "__main__":
    raise SystemExit(main())
