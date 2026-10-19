"""Regenerate, bind and kernel-check the six committed v31.3 Lean examples.

The generic UEOTQM package must already be built with its pinned toolchain.
This command compiles only generated instance files. Each positive instance
must print exactly seven expected axiom audits. Each post-generation negative
control must fail at the unchanged ``checked`` proof AND have an independently
accepted ``check data = false`` witness with the identical numerical prefix.

The complete JSON receipt is written to OUTPUT_DIR/verification.json. Logs,
regenerated inputs and negative controls remain beside it for review. The
stdout JSON is a concise receipt summary; progress is written to stderr.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

from demo_v313 import export_examples


KERNEL_ROOT = Path(__file__).resolve().parent
REPO_ROOT = KERNEL_ROOT.parents[2]
EXAMPLE_NAMES = ("z", "hz", "hsz", "ragged", "d1", "d4")
AUDIT_NAMES = (
    "checked", "presentation", "all_word_response_iff", "finite_tree_coordinates",
    "all_finite_tree_laws", "complete_tree_normalization", "closed_coordinate_update",
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SCHEMA = "ueot_qm.lean_export_verification.v1"
CHECKED_LINE = "theorem checked : ExactCertificate.check data = true := by decide +kernel"
AXIOM_RE = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.MULTILINE,
)
ERROR_RE = re.compile(r"^(.+?):([0-9]+):([0-9]+): error: (.*)$", re.MULTILINE)
MODULE_RE = re.compile(r"UEOTQM\.Generated\.Certificate_[0-9a-f]{64}\Z")


class VerificationError(RuntimeError):
    """The declared verification contract was not met."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def write_receipt(path: Path, receipt: dict) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
                         encoding="utf-8")
    temporary.replace(path)


def audit_targets(module_name: str) -> list[str]:
    return [module_name + "." + name for name in AUDIT_NAMES]


def parse_axioms(log: str) -> tuple[dict[str, list[str]], list[str]]:
    """Parse every complete Lean axiom report, rejecting duplicates or gaps."""
    actual: dict[str, list[str]] = {}
    problems = []
    matches = list(AXIOM_RE.finditer(log))
    reports = log.count("depends on axioms:") + log.count("does not depend on any axioms")
    if reports != len(matches):
        problems.append("an axiom report was malformed or not fully parsed")
    for match in matches:
        name, payload = match.groups()
        axioms = [] if payload is None else [a.strip() for a in payload.split(",") if a.strip()]
        if name in actual:
            problems.append("duplicate axiom target: " + name)
        if len(set(axioms)) != len(axioms):
            problems.append("duplicate axiom in report: " + name)
        actual[name] = axioms
    return actual, problems


def error_diagnostics(log: str) -> list[dict]:
    headers = list(ERROR_RE.finditer(log))
    result = []
    for index, match in enumerate(headers):
        stop = headers[index + 1].start() if index + 1 < len(headers) else len(log)
        following_audit = AXIOM_RE.search(log, match.end())
        if following_audit is not None:
            stop = min(stop, following_audit.start())
        result.append({
            "file": match.group(1), "line": int(match.group(2)),
            "column": int(match.group(3)), "message": match.group(4),
            "detail": log[match.start():stop].strip(),
        })
    return result


def execute(command: list[str], cwd: Path, log_path: Path, timeout_seconds: int) -> dict:
    """Run an owned subprocess group, preserving timeout and launch failures."""
    started_at, clock_start = utc_now(), time.monotonic()
    exit_code = None
    timed_out = False
    launch_error = None
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("wb") as stream:
        try:
            process = subprocess.Popen(command, cwd=cwd, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                exit_code = process.wait(timeout=timeout_seconds)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()
            except BaseException:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise
        except OSError as error:
            launch_error = str(error)
            stream.write(("Process launch failed: " + launch_error + "\n").encode("utf-8"))
    raw_log = log_path.read_bytes()
    return {
        "command": command, "cwd": str(cwd), "started_at": started_at,
        "finished_at": utc_now(), "duration_seconds": round(time.monotonic() - clock_start, 6),
        "timeout_seconds": timeout_seconds, "timed_out": timed_out,
        "launch_error": launch_error, "exit_code": exit_code,
        "log_path": str(log_path), "log_sha256": digest(raw_log), "log_bytes": len(raw_log),
    }


def execution_problems(execution: dict) -> list[str]:
    if execution["timed_out"]:
        return ["process timed out; this is not mathematical rejection evidence"]
    if execution["launch_error"] is not None:
        return ["process could not be launched: " + execution["launch_error"]]
    return []


def accepted_case(name: str, source: Path, targets: list[str], lake: str,
                  package_root: Path, output_dir: Path, timeout_seconds: int,
                  expected_source_sha256: str) -> dict:
    source_hash = digest(source.read_bytes())
    if source_hash != expected_source_sha256:
        raise VerificationError("source differs from its expected bytes before compilation: " + name)
    execution = execute([lake, "env", "lean", str(source)], package_root,
                        output_dir / "logs" / (name + ".compile.log"), timeout_seconds)
    log = Path(execution["log_path"]).read_text(encoding="utf-8", errors="replace")
    actual, problems = parse_axioms(log)
    problems.extend(execution_problems(execution))
    if execution["exit_code"] != 0:
        problems.append("Lean did not exit successfully")
    if error_diagnostics(log) or re.search(r"(?:^|\s)error:", log):
        problems.append("Lean printed an error diagnostic")
    if set(actual) != set(targets) or len(actual) != len(targets):
        problems.append("actual axiom targets differ from the complete expected target set")
    for target, axioms in actual.items():
        forbidden = sorted(set(axioms) - ALLOWED_AXIOMS)
        if forbidden:
            problems.append("unexpected axioms in " + target + ": " + ", ".join(forbidden))
    final_source_hash = digest(source.read_bytes())
    if final_source_hash != source_hash:
        problems.append("source changed during compilation")
    return {
        "name": name, "status": "PASS" if not problems else "FAIL",
        "source_path": str(source), "source_sha256": source_hash,
        "expected_source_sha256": expected_source_sha256,
        "source_sha256_after": final_source_hash, "execution": execution,
        "expected_audit_targets": targets, "actual_axioms": actual,
        "diagnostics": error_diagnostics(log), "problems": problems,
    }


@dataclass(frozen=True)
class Mutation:
    name: str
    base: str
    definition: str
    old: str
    new: str
    purpose: str


WORD_FIRST = "((⟨0, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome))"
WORD_SECOND = "((⟨1, by decide⟩ : Action), (⟨0, by decide⟩ : Outcome))"
MUTATIONS = (
    Mutation("negative_weight", "z", "weights", "(1 : ℚ)", "(2 : ℚ)",
             "Corrupt a nonnegative weight so weighted completeness fails."),
    Mutation("negative_basis", "z", "basisData", "(1 : ℚ)", "(2 : ℚ)",
             "Corrupt a supplied matrix while retaining its actual word witness."),
    Mutation("negative_pullback", "z", "coefficients", "(0 : ℚ)", "(1 : ℚ)",
             "Corrupt one coefficient in a claimed local pullback row."),
    Mutation("negative_word", "hz", "words", WORD_FIRST + ", " + WORD_SECOND,
             WORD_SECOND + ", " + WORD_FIRST,
             "Reverse a noncommuting chronological witness while retaining its matrix."),
)


def mutate_definition(source: str, mutation: Mutation) -> str:
    marker = "def " + mutation.definition + " :"
    if source.count(marker) != 1:
        raise VerificationError("expected one numerical definition: " + mutation.definition)
    start = source.index(marker)
    end = source.index("\n\n", start)
    block = source[start:end]
    if mutation.old not in block:
        raise VerificationError("mutation pattern missing in " + mutation.definition)
    return source[:start] + block.replace(mutation.old, mutation.new, 1) + source[end:]


def data_prefix(source: str) -> str:
    if source.count(CHECKED_LINE) != 1:
        raise VerificationError("expected exactly the frozen kernel checked theorem")
    return source.split(CHECKED_LINE, 1)[0]


def negative_case(mutation: Mutation, base: dict, lake: str, package_root: Path,
                  output_dir: Path, timeout_seconds: int, base_passed: bool) -> dict:
    original = Path(base["generated_source_path"]).read_text(encoding="utf-8")
    if digest(original.encode("utf-8")) != base["source_sha256"]:
        raise VerificationError("negative-control base differs from the verified positive source")
    changed = mutate_definition(original, mutation)
    prefix = data_prefix(changed)
    if changed.split(CHECKED_LINE, 1)[1] != original.split(CHECKED_LINE, 1)[1]:
        raise VerificationError("a numerical mutation changed the original proof suffix")
    module_name = base["module_name"]
    source = output_dir / "negative" / (mutation.name + ".lean")
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(changed, encoding="utf-8")
    false_source = output_dir / "negative" / (mutation.name + "_rejected.lean")
    false_source.write_text(prefix +
        "theorem rejected : ExactCertificate.check data = false := by decide +kernel\n\n"
        "#print axioms rejected\n\nend " + module_name + "\n", encoding="utf-8")
    false_source_hash = digest(false_source.read_bytes())
    false_prefix = false_source.read_text(encoding="utf-8").split("theorem rejected :", 1)[0]
    if false_prefix != prefix:
        raise VerificationError("false witness numerical prefix differs from negative control")
    expected_error_line = prefix.count("\n") + 1
    source_hash = digest(source.read_bytes())
    execution = execute([lake, "env", "lean", str(source)], package_root,
                        output_dir / "logs" / (mutation.name + ".compile.log"), timeout_seconds)
    log = Path(execution["log_path"]).read_text(encoding="utf-8", errors="replace")
    diagnostics = error_diagnostics(log)
    rejected_axioms, _ = parse_axioms(log)
    problems = execution_problems(execution)
    if execution["exit_code"] != 1:
        problems.append("the original true-check proof did not return Lean's expected error exit code 1")
    if len(diagnostics) != 1:
        problems.append("expected exactly one error, located at the unchanged checked proof")
    else:
        diagnostic = diagnostics[0]
        reported_path = Path(diagnostic["file"])
        if not reported_path.is_absolute():
            reported_path = package_root / reported_path
        if reported_path.resolve() != source.resolve() or diagnostic["line"] != expected_error_line:
            problems.append("the error is not at this source's checked theorem")
        if ("Tactic `decide` failed for proposition" not in diagnostic["message"] or
                "ExactCertificate.check data = true" not in diagnostic["detail"]):
            problems.append("the error does not identify the actual true-check proposition")
        if re.search(r"timeout|maximum recursion|maxRecDepth|maxHeartbeats|out of memory|"
                     r"unknown module|unexpected token|failed to synthesize|PANIC",
                     diagnostic["detail"], re.IGNORECASE):
            problems.append("a resource, import, syntax or elaboration failure is not a negative proof")
    if len(re.findall(r"^(?:error:|.*: error:)", log, re.MULTILINE)) != len(diagnostics):
        problems.append("an additional unlocated error is not accepted as negative evidence")
    if digest(source.read_bytes()) != source_hash:
        problems.append("negative source changed during compilation")
    false_witness = accepted_case(mutation.name + "_rejected", false_source,
                                 [module_name + ".rejected"], lake, package_root,
                                 output_dir, timeout_seconds, false_source_hash)
    if false_witness["status"] != "PASS":
        problems.append("the identical numerical data did not prove check = false")
    if not base_passed:
        problems.append("the unmodified positive base did not pass in this verification run")
    final_negative = source.read_bytes()
    final_false = false_source.read_bytes()
    final_negative_text = final_negative.decode("utf-8")
    final_false_text = final_false.decode("utf-8")
    prefixes_unchanged = (
        digest(final_negative) == source_hash and digest(final_false) == false_source_hash
        and data_prefix(final_negative_text) == prefix
        and final_false_text.count("theorem rejected :") == 1
        and final_false_text.split("theorem rejected :", 1)[0] == prefix
    )
    if not prefixes_unchanged:
        problems.append("negative source or false-witness data changed before both checks completed")
    prefix_hash = digest(prefix.encode("utf-8")) if prefixes_unchanged else None
    false_witness["identical_data_prefix_sha256"] = prefix_hash
    return {
        "name": mutation.name, "status": "PASS" if not problems else "FAIL",
        "base_example": mutation.base, "base_source_sha256": base["source_sha256"],
        "module_name": module_name, "source_path": str(source), "source_sha256": source_hash,
        "identical_data_prefix_sha256": prefix_hash,
        "data_prefixes_identical_after_both_compilations": prefixes_unchanged,
        "source_sha256_after": digest(final_negative),
        "mutation": {"definition": mutation.definition, "old": mutation.old,
                     "new": mutation.new, "purpose": mutation.purpose},
        "true_claim_rejection": {
            "execution": execution, "expected_error_line": expected_error_line,
            "diagnostics": diagnostics, "actual_axioms_from_failed_elaboration": rejected_axioms,
            "failed_elaboration_is_not_an_accepted_proof": True,
        },
        "false_witness": false_witness, "problems": problems,
    }


def regenerate_and_compare(fixtures: Path, output_dir: Path) -> list[dict]:
    """Regenerate in a fresh temporary directory, then require identical bytes."""
    destination = output_dir / "generated"
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ueot_qm_lean_exports_") as temporary:
        generated = Path(temporary)
        index = export_examples(generated)
        entries = index.get("examples", [])
        if tuple(entry.get("name") for entry in entries) != EXAMPLE_NAMES:
            raise VerificationError("regeneration did not return the six declared examples in order")
        if (generated / "exports.json").read_bytes() != (fixtures / "exports.json").read_bytes():
            raise VerificationError("regenerated exports.json differs from the committed index")
        bindings = []
        for entry in entries:
            name, module_name = entry["name"], entry["module_name"]
            if not MODULE_RE.fullmatch(module_name):
                raise VerificationError("generated module name is outside the fixed numeric naming contract")
            if entry["source_path"] != name + ".lean" or entry["manifest_path"] != name + ".manifest.json":
                raise VerificationError("fixture paths must be the declared flat example filenames")
            source_bytes = (generated / entry["source_path"]).read_bytes()
            manifest_bytes = (generated / entry["manifest_path"]).read_bytes()
            source_hash, manifest_hash = digest(source_bytes), digest(manifest_bytes)
            if source_hash != entry["source_sha256"] or manifest_hash != entry["manifest_sha256"]:
                raise VerificationError("regenerated index hashes disagree with actual bytes for " + name)
            manifest = json.loads(manifest_bytes)
            if (manifest.get("module_name") != module_name or
                    manifest.get("source_sha256") != source_hash or
                    manifest.get("audit_targets") != audit_targets(module_name)):
                raise VerificationError("manifest source/audit binding differs for " + name)
            source_text = source_bytes.decode("utf-8")
            if re.findall(r"^namespace (\S+)$", source_text, re.MULTILINE) != [module_name]:
                raise VerificationError("source namespace differs from the manifest for " + name)
            if re.findall(r"^#print axioms (\S+)$", source_text, re.MULTILINE) != list(AUDIT_NAMES):
                raise VerificationError("source does not request exactly all seven expected audits")
            if re.search(r"\b(?:sorry|admit|native_decide|axiom|opaque)\b", source_text):
                raise VerificationError("source includes a forbidden proof escape token")
            data_prefix(source_text)
            for field, payload in (("source_path", source_bytes), ("manifest_path", manifest_bytes)):
                fixture = fixtures / entry[field]
                if fixture.read_bytes() != payload:
                    raise VerificationError("regenerated bytes differ from committed fixture: " + str(fixture))
                (destination / entry[field]).write_bytes(payload)
            bindings.append({
                "name": name, "module_name": module_name, "source_sha256": source_hash,
                "manifest_sha256": manifest_hash, "fixture_source_path": str(fixtures / entry["source_path"]),
                "fixture_manifest_path": str(fixtures / entry["manifest_path"]),
                "generated_source_path": str(destination / entry["source_path"]),
                "generated_manifest_path": str(destination / entry["manifest_path"]),
                "source_bytes_identical": True, "manifest_bytes_identical": True,
            })
        (destination / "exports.json").write_bytes((generated / "exports.json").read_bytes())
        return bindings


def source_bindings(package_root: Path) -> dict[str, str]:
    """Record source inputs without claiming to rebuild imported dependencies."""
    paths = [package_root / "lean-toolchain", package_root / "lake-manifest.json",
             KERNEL_ROOT / "demo_v313.py", KERNEL_ROOT / "verify_lean_exports.py",
             KERNEL_ROOT / "ueot_qm" / "lean_export.py"]
    paths.extend(sorted((package_root / "UEOTQM").glob("*.lean")))
    paths.extend(sorted((package_root / ".lake" / "build" / "lib" / "lean" / "UEOTQM").glob("*.olean")))
    return {str(path): digest(path.read_bytes()) for path in paths if path.is_file()}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--package-root", type=Path,
                        default=REPO_ROOT / "formalization" / "ueot-qm")
    parser.add_argument("--fixtures", type=Path, default=KERNEL_ROOT / "certificates" / "v31.3")
    parser.add_argument("--timeout-seconds", type=int, default=300,
                        help="per-process limit; a timeout always fails verification (default: 300)")
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if os.sep in args.lake:
        args.lake = str(Path(args.lake).expanduser().resolve())
    output_dir, package_root, fixtures = (path.resolve() for path in
                                          (args.output_dir, args.package_root, args.fixtures))
    output_dir.mkdir(parents=True, exist_ok=True)
    receipt_path = output_dir / "verification.json"
    receipt = {
        "schema": SCHEMA, "status": "RUNNING", "started_at": utc_now(),
        "package_root": str(package_root), "fixtures_root": str(fixtures),
        "python_version": sys.version, "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "expected_examples": list(EXAMPLE_NAMES), "regeneration": [],
        "positive_cases": [], "negative_cases": [], "problems": [],
        "dependency_policy": "Uses already-built pinned package dependencies; does not rebuild the package.",
        "negative_policy": "Require original checked-proof failure and identical-data check=false kernel proof.",
    }
    write_receipt(receipt_path, receipt)
    try:
        receipt["source_bindings"] = source_bindings(package_root)
        pinned = (package_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", pinned)
        if match is None:
            raise VerificationError("a release-pinned Lean toolchain is required")
        toolchain = execute([args.lake, "env", "lean", "--version"], package_root,
                            output_dir / "logs" / "toolchain_version.log", args.timeout_seconds)
        version_text = Path(toolchain["log_path"]).read_text(encoding="utf-8", errors="replace")
        receipt["toolchain"] = {"pin": pinned, "version_output": version_text, "execution": toolchain}
        if (execution_problems(toolchain) or toolchain["exit_code"] != 0 or
                not re.search(r"Lean \(version " + re.escape(match.group(1)) + r"(?:,|\))", version_text)):
            raise VerificationError("Lean invocation did not match the package's pinned release")
        receipt["regeneration"] = regenerate_and_compare(fixtures, output_dir)
        receipt["index_sha256"] = digest((output_dir / "generated" / "exports.json").read_bytes())
        if digest((fixtures / "exports.json").read_bytes()) != receipt["index_sha256"]:
            raise VerificationError("committed index changed after fresh byte comparison")
        write_receipt(receipt_path, receipt)
        bindings = {entry["name"]: entry for entry in receipt["regeneration"]}
        positive_status = {}
        for name in EXAMPLE_NAMES:
            print("Verifying positive " + name, file=sys.stderr, flush=True)
            entry = bindings[name]
            case = accepted_case(name, Path(entry["generated_source_path"]),
                                 audit_targets(entry["module_name"]), args.lake,
                                 package_root, output_dir, args.timeout_seconds, entry["source_sha256"])
            case["manifest_sha256"] = entry["manifest_sha256"]
            receipt["positive_cases"].append(case)
            positive_status[name] = case["status"] == "PASS"
            write_receipt(receipt_path, receipt)
        for mutation in MUTATIONS:
            print("Verifying negative and false witness " + mutation.name, file=sys.stderr, flush=True)
            case = negative_case(mutation, bindings[mutation.base], args.lake, package_root,
                                 output_dir, args.timeout_seconds, positive_status[mutation.base])
            receipt["negative_cases"].append(case)
            write_receipt(receipt_path, receipt)
        receipt["source_bindings_after"] = source_bindings(package_root)
        if receipt["source_bindings_after"] != receipt["source_bindings"]:
            raise VerificationError("implementation sources or local dependency artifacts changed during verification")
        for entry in receipt["regeneration"]:
            if (digest(Path(entry["fixture_source_path"]).read_bytes()) != entry["source_sha256"] or
                    digest(Path(entry["fixture_manifest_path"]).read_bytes()) != entry["manifest_sha256"]):
                raise VerificationError("committed fixtures changed during verification")
        if digest((fixtures / "exports.json").read_bytes()) != receipt["index_sha256"]:
            raise VerificationError("committed index changed during verification")
    except (OSError, ValueError, KeyError, TypeError, VerificationError) as error:
        receipt["problems"].append(type(error).__name__ + ": " + str(error))
    receipt["finished_at"] = utc_now()
    receipt["summary"] = {
        "positive_passed": sum(case["status"] == "PASS" for case in receipt["positive_cases"]),
        "positive_expected": len(EXAMPLE_NAMES),
        "negative_passed": sum(case["status"] == "PASS" for case in receipt["negative_cases"]),
        "negative_expected": len(MUTATIONS),
        "false_witness_passed": sum(case["false_witness"]["status"] == "PASS"
                                    for case in receipt["negative_cases"]),
        "positive_audit_targets_expected": len(EXAMPLE_NAMES) * len(AUDIT_NAMES),
        "false_witness_audit_targets_expected": len(MUTATIONS),
    }
    complete = (not receipt["problems"] and receipt["summary"]["positive_passed"] == len(EXAMPLE_NAMES)
                and receipt["summary"]["negative_passed"] == len(MUTATIONS))
    receipt["status"] = "PASS" if complete else "FAIL"
    write_receipt(receipt_path, receipt)
    print(json.dumps({"status": receipt["status"], "receipt": str(receipt_path),
                      "summary": receipt["summary"], "problems": receipt["problems"]},
                     indent=2, ensure_ascii=False))
    return 0 if complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
