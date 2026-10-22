#!/usr/bin/env python3
"""Run an unfiltered current-source gate while preserving its actual output."""
from argparse import ArgumentParser
import ast
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import time


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def source_fingerprint(repo):
    core = repo / "formalization/ueot-core"
    paths = sorted({core / "UEOT.lean", *core.joinpath("UEOT").rglob("*.lean")},
                   key=lambda path: path.relative_to(core).with_suffix("").as_posix().replace("/", "."))
    value = sha256()
    for path in paths:
        name = path.relative_to(core).with_suffix("").as_posix().replace("/", ".")
        value.update(name.encode() + b"\0" + path.read_bytes() + b"\0")
    return len(paths), value.hexdigest()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--gate", choices=["reuse-01", "fkrg-01", "clone-01"], required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    common = "formalization/ueot-core/docs/compression/theory_completion/"
    commands = {
        "reuse-01": common + "knowledge/reuse/test_fkrg_reuse.py",
        "fkrg-01": common + "knowledge/test_fkrg.py",
        "clone-01": common + "knowledge/reuse/REBUILD_CLONE_CANDIDATES.py",
    }
    tested = commands[args.gate]
    packet = repo / (common + "unified_closure/path_realization_v1")
    target = packet / "local-gates" / args.gate
    target.mkdir(exist_ok=False)
    applied = json.loads((packet / "consumer-plan/APPLIED_SIX_PATHS_01.json").read_text())
    inputs = {row["path"] for row in applied["paths"]}
    inputs.update(commands.values())
    inputs.update(common + suffix for suffix in [
        "knowledge/fkrg.py", "knowledge/reuse/pr_preflight.py",
        "knowledge/reuse/test_pr_preflight.py", "unified_closure/audit_umc_local.py",
        "unified_closure/build_umc_global_map.py", "knowledge/reuse/CLONE_CANDIDATES_68.json",
        "knowledge/reuse/PATH_REALIZATION_REUSE_OVERLAY_V1.json",
        "knowledge/reuse/PATH_REALIZATION_NATIVE_V1.json",
        "knowledge/reuse/VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean",
    ])
    before = {rel: digest(repo / rel) for rel in sorted(inputs)}
    for row in applied["paths"]:
        assert before[row["path"]] == row["after_sha256"], row["path"]
    module_count, fingerprint = source_fingerprint(repo)
    assert module_count == 691
    assert fingerprint == "de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379"
    base = "d503586107974c56e0773b4ea106b41a7d144b43"
    immutable_inputs = [common + suffix for suffix in [
        "knowledge/fkrg.py", "knowledge/test_fkrg.py",
        "knowledge/reuse/pr_preflight.py", "knowledge/reuse/test_pr_preflight.py",
        "unified_closure/audit_umc_local.py", "unified_closure/build_umc_global_map.py",
        "knowledge/reuse/CLONE_CANDIDATES_68.json",
    ]]
    for rel in immutable_inputs:
        original = subprocess.run(["git", "show", base + ":" + rel], cwd=repo,
                                  check=True, capture_output=True).stdout
        assert original == (repo / rel).read_bytes(), rel
    argv = [sys.executable, str(repo / tested)]
    command = {"command": argv, "cwd": str(repo), "gate": args.gate,
               "unfiltered_normal_script_entrypoint": True,
               "input_sha256_before": before,
               "source_tree_sha256": fingerprint,
               "module_count": module_count,
               "runner_sha256": digest(Path(__file__)),
               "started_at": datetime.now(timezone.utc).isoformat()}
    (target / "COMMAND.json").write_text(json.dumps(command, indent=2) + "\n")
    start = time.monotonic()
    with (target / "STDOUT.txt").open("wb") as stdout, (target / "STDERR.txt").open("wb") as stderr:
        result = subprocess.run(argv, cwd=repo, stdout=stdout, stderr=stderr)
    seconds = time.monotonic() - start
    after = {rel: digest(repo / rel) for rel in sorted(inputs)}
    after_source = source_fingerprint(repo)
    combined = (target / "STDOUT.txt").read_text() + (target / "STDERR.txt").read_text()
    detail = {}
    gate_pass = result.returncode == 0
    if args.gate != "clone-01":
        expected = sum(isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                       and node.name.startswith("test_")
                       for node in ast.walk(ast.parse((repo / tested).read_text())))
        ran = re.findall(r"Ran (\d+) tests? in ", combined)
        detail = {"expected_test_methods": expected,
                  "actual_tests": int(ran[-1]) if ran else None,
                  "skipped": bool(re.search(r"skipped[= ]", combined)),
                  "unittest_ok": bool(re.search(r"^OK\s*$", combined, re.M))}
        gate_pass = gate_pass and detail["actual_tests"] == expected and not detail["skipped"] and detail["unittest_ok"]
    else:
        detail = json.loads((target / "STDOUT.txt").read_text())
        gate_pass = gate_pass and detail["status"] == "PASS" and detail["cross_file_proof_related_code_clone_pairs"] == 68
    stable = before == after and after_source == (module_count, fingerprint)
    receipt = {**command, "state": "PASS" if gate_pass and stable else "FAIL",
               "exit_code": result.returncode, "seconds": seconds,
               "stdout_sha256": digest(target / "STDOUT.txt"),
               "stderr_sha256": digest(target / "STDERR.txt"),
               "input_sha256_after": after, "inputs_and_sources_unchanged": stable,
               "immutable_input_paths_equal_baseline": immutable_inputs,
               "result": detail,
               "parser_suite": "REUSED_PRESERVED_PARSER_01_89_TEST_PASS_NOT_RERUN"}
    receipt_path = target / "RECEIPT.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"state": receipt["state"], "gate": args.gate,
                      "seconds": seconds, "exit_code": result.returncode,
                      "result": detail, "receipt_sha256": digest(receipt_path)}))
    if receipt["state"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
