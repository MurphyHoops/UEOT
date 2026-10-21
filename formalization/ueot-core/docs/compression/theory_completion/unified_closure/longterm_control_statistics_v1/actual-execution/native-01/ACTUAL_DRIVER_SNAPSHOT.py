#!/usr/bin/env python3
"""Collect and replay compiler evidence for this additive Core increment.

The existing eight overlays are immutable. Preparation uses the complete actual
Git-base declaration parser, rather than extending the frozen lexical parser.
The established raw-type/compiled-proof export protocol is reused explicitly;
no historical declaration repair is needed in this increment.

The run requires an actual successful full-build receipt and an unchanged full
build identity. It preserves both real executions and emits a candidate overlay
only after fixed-edge replay and complete JSON equality. Registration and
independent semantic review are separate operations.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import types
from hashlib import sha256

CORE = "formalization/ueot-core/"
REUSE = CORE + "docs/compression/theory_completion/knowledge/reuse/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/"
NAME = "LONGTERM_CONTROL_STATISTICS"
MARKER = NAME + "_NATIVE_JSON "
EXPORTER = NAME + "_NATIVE_EXPORT.lean"
VERIFIER = "VERIFY_" + NAME + "_OVERLAY_TYPES.lean"
NATIVE = NAME + "_NATIVE_V1.json"
OVERLAY = NAME + "_REUSE_OVERLAY_V1.json"
PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 666, 4147, 8


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_base_consumer(repo, base, name):
    """Use the actual immutable predecessor registry, including after registration.

    Its file location still points to the repository's immutable evidence files.
    The executed code is exactly the Git object at the supplied base, not a
    truncated or otherwise rewritten version of the current consumer.
    """
    path = REUSE + "fkrg_reuse.py"
    source = subprocess.check_output(["git", "show", base + ":" + path], cwd=repo)
    module = types.ModuleType(name)
    module.__file__ = str(repo / path)
    sys.modules[name] = module
    exec(compile(source, module.__file__, "exec"), module.__dict__)
    return module, sha256(source).hexdigest()


def prepare(repo, out, base):
    repo, out = Path(repo).resolve(), Path(out).resolve()
    if out.is_relative_to(repo):
        raise RuntimeError("OUTPUT_MUST_BE_OUTSIDE_REPOSITORY")
    base = subprocess.check_output(
        ["git", "rev-parse", "--verify", base + "^{commit}"], cwd=repo, text=True).strip()
    reuse, consumer_sha = load_base_consumer(repo, base, "longterm_previous_reuse")
    immutable_helpers = []
    for relative in (REUSE + "pr_preflight.py", REUSE + "../fkrg.py",
                     PACKET + "registered_interfaces/native_protocol/prepare_registered_interfaces_export.py",
                     PACKET + "registered_interfaces/native_protocol/build_identity.py"):
        path = (repo / relative).resolve()
        canonical = path.relative_to(repo).as_posix()
        old = subprocess.check_output(["git", "show", base + ":" + canonical], cwd=repo)
        assert path.read_bytes() == old, "IMMUTABLE_PROTOCOL_HELPER_CHANGED: " + canonical
        immutable_helpers.append({"path": canonical, "sha256": sha256(old).hexdigest()})
    previous = reuse.load(verify_source=False)
    assert (len(previous["modules"]), len(previous["graph"]), len(previous["overlays"])) == (
        PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS)
    parser = load_module("longterm_base_parser", repo / REUSE / "pr_preflight.py")
    base = parser.commit(repo, base)
    base_sources = parser.corpus(repo, base)
    assert len(base_sources) == PRIOR_MODULES
    core = repo / CORE
    current = {p.relative_to(repo).as_posix(): p.read_text() for p in
               [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]}
    assert set(base_sources) <= set(current)
    root = CORE + "UEOT/V3/Compression/TheoryCompletion.lean"
    changed = {p for p in base_sources if base_sources[p] != current[p]}
    assert changed == {root}, changed
    old_imports = base_sources[root].splitlines()
    new_imports = current[root].splitlines()
    assert [line for line in new_imports if line in old_imports] == old_imports
    assert all(line.startswith("import UEOT.V3.Compression.TheoryCompletion.")
               for line in new_imports if line not in old_imports)
    added = sorted(set(current) - set(base_sources))
    assert added and all(p.startswith(CORE + "UEOT/V3/Compression/TheoryCompletion/") for p in added)
    expected_prior = {p["path"] for p in previous["modules"]}
    assert set(base_sources) == expected_prior
    overrides = {}
    for overlay in previous["overlays"]:
        overrides.update(overlay.get("source_hash_overrides", {}))
    for row in previous["modules"]:
        assert sha256(base_sources[row["path"]].encode()).hexdigest() == overrides.get(
            row["path"], row["content_sha256"]), row["path"]
    baseline = [d for p, s in base_sources.items() for d in parser.declarations(p, s)]
    baseline_names = parser.validate_unique(baseline, "ACTUAL_IMMUTABLE_BASE")
    assert set(baseline_names) == set(previous["graph"])
    declarations = [d for p in added for d in parser.declarations(p, current[p])]
    parser.validate_unique(declarations, "NEW_SOURCE_DECLARATIONS")
    assert not set(d["symbol"] for d in declarations) & set(previous["graph"])
    modules = [{"module": p[len(CORE):-5].replace("/", "."), "path": p,
                "content_sha256": digest(repo / p), "source_origin": "UEOT_MAINTAINED"} for p in added]
    public = [{"name": d["symbol"], "module": d["path"][len(CORE):-5].replace("/", "."),
               "path": d["path"], "line": d["line"], "source_origin": "UEOT_MAINTAINED",
               "registration_kind": "new_source_public"} for d in declarations]
    old_protocol = repo / PACKET / "registered_interfaces/native_protocol/prepare_registered_interfaces_export.py"
    helper = load_module("longterm_frozen_export_protocol", old_protocol)
    prior = [row["name"] for overlay in previous["overlays"] for row in overlay["public_theorems"]]
    exporter = helper.render_export(prior, public, modules, [])
    exporter = exporter.replace("REGISTERED_INTERFACES", NAME)
    exporter = exporter.replace("registered.length == 4094", f"registered.length == {PRIOR_THEOREMS}")
    exporter = exporter.replace(
        "newNames.size == 53 && historicalRepairNames.size == 1 && sourceModules.size == 8",
        f"newNames.size == {len(public)} && historicalRepairNames.size == 0 && sourceModules.size == {len(modules)}")
    out.mkdir(parents=True, exist_ok=True)
    (out / EXPORTER).write_text(exporter)
    fkrg = load_module("longterm_source_fingerprint", repo / REUSE / "../fkrg.py")
    payload = {"status": "PENDING_ACTUAL_NATIVE_EXECUTION", "baseline_ref": base,
               "baseline_reuse_consumer": {"path": REUSE + "fkrg_reuse.py", "sha256": consumer_sha},
               "immutable_protocol_helpers": immutable_helpers,
               "integration_driver_sha256": digest(__file__),
               "source_tree_sha256": fkrg.fingerprint(fkrg.sources()),
               "complete_source_modules": len(current), "base_snapshot_modules": PRIOR_MODULES,
               "registered_prior_theorems": PRIOR_THEOREMS, "prior_overlay_count": PRIOR_OVERLAYS,
               "prior_overlay": {"path": reuse.OVERLAY_PATHS[-1].relative_to(repo).as_posix(),
                                 "sha256": reuse.OVERLAY_SHA256S[-1]},
               "source_hash_overrides": {root: digest(repo / root)}, "added_modules": modules,
               "public_source_candidates": public, "exporter_sha256": digest(out / EXPORTER),
               "reused_export_protocol": {"path": old_protocol.relative_to(repo).as_posix(),
                                          "sha256": digest(old_protocol)},
               "lexical_reuse_hints": [{**d, "reuse_candidates": parser.candidate_hints(d, baseline)}
                                       for d in declarations]}
    dump(out / "SOURCE_PREFLIGHT.json", payload)
    return payload


def read_native(path):
    matches = [line[len(MARKER):] for line in Path(path).read_text().splitlines() if line.startswith(MARKER)]
    if len(matches) != 1:
        raise RuntimeError("EXPECTED_ONE_ACTUAL_NATIVE_JSON")
    return json.loads(matches[0])


def validate_native(pre, native):
    candidates = {row["name"]: row for row in pre["public_source_candidates"]}
    rows = native["public_source_theorems"]
    assert len(rows) == len(candidates) and {r["name"] for r in rows} == set(candidates)
    n = len(rows)
    assert native["registered_prior_theorems"] == PRIOR_THEOREMS
    assert native["schema"] == NAME + "_NATIVE_EXPORT_V1"
    assert native["cross_isDefEq_comparisons"] == n * PRIOR_THEOREMS
    assert native["internal_isDefEq_comparisons"] == n * (n - 1) // 2
    assert native["new_source_public_theorem_count"] == n
    assert native["historical_public_repair_count"] == 0
    assert native["collisions"] == [], native["collisions"]
    modules = [row["module"] for row in pre["added_modules"]]
    assert native["native_audit_modules"] == modules
    scope = native["all_native_theorem_constants"]
    by_name = {row["name"]: row for row in scope}
    assert len(by_name) == len(scope) and set(candidates) <= set(by_name)
    assert {row["source_module"] for row in scope} == set(modules)
    for row in scope:
        assert set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
        assert isinstance(row["is_private"], bool) and row["type"]
        assert len(row["direct_constants"]) == len(set(row["direct_constants"]))
        assert set(row["direct_theorem_constants"]) <= set(row["direct_constants"])
    for row in rows:
        assert row["source_module"] == candidates[row["name"]]["module"]
        assert row["registration_kind"] == "new_source_public"
        assert by_name[row["name"]]["is_private"] is False
        for field in ("source_module", "type", "level_parameters", "direct_constants"):
            assert row[field] == by_name[row["name"]][field]
    return rows, scope


def run(repo, out, base, build_receipt):
    repo, out = Path(repo).resolve(), Path(out).resolve()
    if out.exists() and any(out.iterdir()):
        raise RuntimeError("NEW_EXECUTION_DIRECTORY_REQUIRED")
    receipt = json.loads(Path(build_receipt).read_text())
    assert receipt["state"] == "PASS" and receipt["full_build"]["exit_code"] == 0
    identity = receipt["identity"]
    identity_helper = load_module("longterm_build_identity", repo / PACKET /
                                 "registered_interfaces/native_protocol/build_identity.py")
    def check_identity():
        return identity_helper.capture(repo, lake=identity["runtime_tools"]["lake"]["executable"],
                                       lean=identity["runtime_tools"]["lean"]["executable"], expected=identity)
    check_identity()
    assert digest(Path(build_receipt).parent / receipt["full_build"]["log_name"]) == receipt["full_build"]["log_sha256"]
    pre = prepare(repo, out, base)
    assert pre["source_tree_sha256"] == identity["source_tree_sha256"]
    assert pre["complete_source_modules"] == identity["module_count"]
    status = {"state": "RUNNING", "baseline_ref": pre["baseline_ref"],
              "build_receipt_sha256": digest(build_receipt), "results": []}
    def execute(label, source):
        check_identity()
        cmd = [identity["runtime_tools"]["lake"]["executable"], "env",
               identity["runtime_tools"]["lean"]["executable"], str(source)]
        log = out / (label + ".log")
        start = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(cmd, cwd=repo / CORE, stdout=stream, stderr=subprocess.STDOUT)
        record = {"label": label, "command": cmd, "exit_code": result.returncode,
                  "seconds": round(time.monotonic() - start, 3), "log_sha256": digest(log)}
        status["results"].append(record)
        dump(out / "STATUS.json", status)
        if result.returncode:
            raise RuntimeError("ACTUAL_LEAN_EXECUTION_FAILED: " + label)
        check_identity()
        return read_native(log)
    try:
        first = execute("native_export", out / EXPORTER)
        rows, scope = validate_native(pre, first)
        dump(out / "observed_first_native.json", first)
        entries = ["    (`" + row["name"] + ", [" + ", ".join("`" + d for d in sorted(row["source_theorem_deps"])) + "]),"
                   for row in rows]
        fixed = (out / EXPORTER).read_text()
        anchor = "  let mut nativeScope : Array Json := #[]"
        assert fixed.count(anchor) == 1
        fixed = fixed.replace(anchor, "  let expectedEdges : Array (Name × List Name) := #[\n" +
                              "\n".join(entries) + "\n  ]\n" + anchor)
        anchor = "    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep"
        assert fixed.count(anchor) == 1
        fixed = fixed.replace(anchor, anchor + "\n" +
            "    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)\n" +
            '      | throwError "LONGTERM_EXPECTED_EDGES_MISSING"\n' +
            "    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do\n" +
            '      throwError s!"LONGTERM_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}"')
        fixed = fixed.replace("  let mut cross := 0", f"  unless nativeScope.size == {len(scope)} do\n" +
                              '    throwError "LONGTERM_NATIVE_CENSUS_DRIFT"\n  let mut cross := 0')
        (out / VERIFIER).write_text(fixed)
        second = execute("fixed_verifier", out / VERIFIER)
        validate_native(pre, second)
        assert first == second, "COMPLETE_NATIVE_JSON_MISMATCH"
        dump(out / NATIVE, second)
        prior_reuse, _ = load_base_consumer(repo, pre["baseline_ref"], "longterm_final_prior")
        registered = set(prior_reuse.load(verify_source=False)["graph"])
        all_names = registered | {row["name"] for row in rows}
        for row in rows:
            assert set(row["source_theorem_deps"]) == (set(row["direct_constants"]) & all_names) - {row["name"]}
        public = [{**{k: v for k, v in candidate.items() if k != "module"},
                   "source_module": row["source_module"], "source_theorem_deps": sorted(row["source_theorem_deps"])}
                  for row in rows for candidate in pre["public_source_candidates"] if candidate["name"] == row["name"]]
        edges = [{"source": row["name"], "target": target} for row in public for target in row["source_theorem_deps"]]
        private = sum(row["is_private"] for row in scope)
        overlay = {"schema": "FKRG_REUSE_OVERLAY_V1", "overlay_id": NAME + "_REUSE_OVERLAY_V1",
                   "source_checkpoint": "worktree-sha256:" + pre["source_tree_sha256"],
                   "source_checkpoint_kind": "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT",
                   **{k: pre[k] for k in ("baseline_ref", "base_snapshot_modules", "prior_overlay", "source_hash_overrides", "added_modules")},
                   "public_theorems": public,
                   "type_distinctness": {"status": "PASS", "verifier": REUSE + VERIFIER,
                       "new_theorems": len(rows), "registered_prior_theorems": PRIOR_THEOREMS,
                       "cross_isDefEq_comparisons": len(rows) * PRIOR_THEOREMS,
                       "internal_isDefEq_comparisons": len(rows) * (len(rows) - 1) // 2,
                       "definitionally_equal_matches": 0,
                       "protocol": "Raw stored compiled types; fresh liftTermElabM per Meta.isDefEq comparison; stored universe names retained. Not a general logical-equivalence decision."},
                   "proof_dependency_certification": {"status": "PASS", "verifier": REUSE + VERIFIER,
                       "measure": "Actual theorem proof-value getUsedConstants restricted to all previous and new registered public theorem names",
                       "registered_direct_edges": len(edges), "edges": edges},
                   "native_axiom_census": {"status": "PASS", "physical_source_modules": len(pre["added_modules"]),
                       "theorem_constants": len(scope), "private_theorem_constants": private,
                       "confirmed_public_source_candidates": len(rows), "other_native_public_constants": len(scope) - private - len(rows),
                       "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
                       "scope": "All compiler-owned theorem constants of every added module, including private and generated constants"},
                   "native_export_evidence": {"path": REUSE + NATIVE, "sha256": digest(out / NATIVE)},
                   "native_execution": {"build_receipt_sha256": digest(build_receipt), "source_tree_sha256": pre["source_tree_sha256"],
                       "native_export_exit_code": 0, "fixed_certificate_exit_code": 0,
                       "fixed_certificate_sha256": digest(out / VERIFIER), "fixed_export_equals_initial_native_export": True,
                       "results": status["results"]},
                   "scientific_role": "UNCOUNTED_SAME_SOURCE_LONGTERM_POLICY_AND_ROWWISE_SISC",
                   "counted_core_impact": "NONE", "scientific_closure": "NOT_ESTABLISHED"}
        dump(out / OVERLAY, overlay)
        dump(out / "development_lexical_reuse_hints.json", pre["lexical_reuse_hints"])
        status["state"] = "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION"
        status["summary"] = {"modules": len(pre["added_modules"]), "public_source_theorems": len(rows),
                             "native_constants": len(scope), "registered_edges": len(edges),
                             "overlay_sha256": digest(out / OVERLAY), "verifier_sha256": digest(out / VERIFIER),
                             "native_sha256": digest(out / NATIVE)}
    except Exception as exc:
        status["state"] = "FAILED"
        status["error"] = repr(exc)
        raise
    finally:
        dump(out / "STATUS.json", status)
    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "run"])
    for arg in ("repo", "output"):
        parser.add_argument("--" + arg, type=Path, required=True)
    parser.add_argument("--base-ref", required=True)
    parser.add_argument("--build-receipt", type=Path)
    args = parser.parse_args()
    if args.mode == "run":
        if args.build_receipt is None:
            parser.error("run requires --build-receipt")
        result = run(args.repo, args.output, args.base_ref, args.build_receipt)
    else:
        result = prepare(args.repo, args.output, args.base_ref)
        result = {"status": result["status"], "modules": len(result["added_modules"]),
                  "public_source_candidates": len(result["public_source_candidates"])}
    print(json.dumps(result, ensure_ascii=False, indent=2))
