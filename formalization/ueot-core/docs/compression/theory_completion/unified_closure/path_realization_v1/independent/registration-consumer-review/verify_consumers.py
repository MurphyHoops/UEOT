#!/usr/bin/env python3
"""Independently audit six consumers, retained evidence, DAG and existing logs.

No test suite, Lean, Mac, generator write, or registration is executed.
Only the final reviewer JSON is written in this directory.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter, deque
import copy
import csv
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess

BASE = "d503586107974c56e0773b4ea106b41a7d144b43"
SOURCE = "de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379"
CORE = "formalization/ueot-core/"
TC = CORE + "docs/compression/theory_completion/"
PACKET = TC + "unified_closure/path_realization_v1/"
REUSE = TC + "knowledge/reuse/"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    repo = parser.parse_args().repo.resolve(strict=True)
    observed, checks = {}, []

    def sha(value):
        return hashlib.sha256(value).hexdigest()

    def read(path):
        path = Path(path)
        assert path.is_file() and not path.is_symlink(), str(path)
        value = path.read_bytes()
        assert path not in observed or observed[path] == value, "INPUT_CHANGED"
        observed[path] = value
        return value

    def obj(path):
        return json.loads(read(path))

    def check(name, condition):
        assert condition, name
        checks.append(name)

    def old_blob(path):
        return subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)

    def assignments(tree):
        return {n.targets[0].id: n.value for n in tree.body
                if isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)}

    def dump(tree):
        return ast.dump(tree, include_attributes=False)

    packet = repo / PACKET
    applied_path = packet / "consumer-plan/APPLIED_SIX_PATHS_01.json"
    applied = obj(applied_path)
    check("exact_six_path_candidate_manifest",
          sha(read(applied_path)) == "fb8546ac7f6005e3b683986028f568d774294acbc89cd460f3a87693bbedfe03"
          and applied["source_tree_sha256"] == SOURCE and len(applied["paths"]) == 6)
    old, current = {}, {}
    for entry in applied["paths"]:
        path = entry["path"]
        old[path], current[path] = old_blob(path), read(repo / path)
        check("exact_before_after:" + path, sha(old[path]) == entry["before_sha256"]
              and sha(current[path]) == entry["after_sha256"])
    required = {TC + "unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json", TC + "knowledge/README.md",
                *(REUSE + x for x in ("fkrg_reuse.py", "test_fkrg_reuse.py",
                    "REBUILD_CLONE_CANDIDATES.py", "README.md"))}
    check("only_authorized_six_paths_in_candidate", set(current) == required)

    consumer_path = REUSE + "fkrg_reuse.py"
    old_ast, new_ast = ast.parse(old[consumer_path]), ast.parse(current[consumer_path])
    old_assign, new_assign = assignments(old_ast), assignments(new_ast)
    arrays = ("OVERLAY_PATHS", "OVERLAY_TYPE_CHECKS", "OVERLAY_SHA256S", "OVERLAY_TYPE_CHECK_SHA256S")
    normalized = copy.deepcopy(new_ast)
    for name in arrays:
        check("old_ten_registry_entries_preserved:" + name,
              len(old_assign[name].elts) == 10 and len(new_assign[name].elts) == 11
              and [dump(x) for x in new_assign[name].elts[:-1]] == [dump(x) for x in old_assign[name].elts])
        assignments(normalized)[name].elts.pop()
    check("consumer_entire_ast_unchanged_after_four_appends", dump(normalized) == dump(old_ast))
    overlay_files = [x.right.value for x in new_assign["OVERLAY_PATHS"].elts]
    verifier_files = [x.right.value for x in new_assign["OVERLAY_TYPE_CHECKS"].elts]
    overlay_hashes = ast.literal_eval(new_assign["OVERLAY_SHA256S"])
    verifier_hashes = ast.literal_eval(new_assign["OVERLAY_TYPE_CHECK_SHA256S"])
    overlays, retained = [], []
    for index, filename in enumerate(overlay_files):
        path = REUSE + filename
        data = read(repo / path)
        overlay = json.loads(data)
        overlays.append(overlay)
        check("pinned_overlay:" + filename, sha(data) == overlay_hashes[index])
        vp = REUSE + verifier_files[index]
        check("pinned_fixed_verifier:" + verifier_files[index], sha(read(repo / vp)) == verifier_hashes[index])
        if index < 10:
            check("old_overlay_and_fixed_bytes_retained:" + filename,
                  data == old_blob(path) and read(repo / vp) == old_blob(vp))
            retained.extend([{"path": path, "sha256": sha(data)},
                             {"path": vp, "sha256": sha(read(repo / vp))}])
            evidence = overlay.get("native_export_evidence")
            if evidence:
                nb = read(repo / evidence["path"])
                check("old_native_bytes_retained:" + evidence["path"],
                      sha(nb) == evidence["sha256"] and nb == old_blob(evidence["path"]))
                retained.append({"path": evidence["path"], "sha256": sha(nb)})
    check("actual_new_registration_and_fixed_pins",
          overlay_hashes[-1] == applied["registered_overlay_sha256"] ==
          "8e72781498acf49496733ace5dfbf80257830ff3a6d85e1b02e66474f936ec3b"
          and verifier_hashes[-1] == "430aae70eec2c7cf87530020e24a8e43beae7021e2f8282f4c0c9b2949195714")
    audit_dir = repo / TC / "knowledge/audits/2026-10-10"
    for name, expected in ast.literal_eval(old_assign["EVIDENCE_SHA"]).items():
        path = audit_dir / name
        data = read(path)
        check("immutable_audit_evidence:" + name,
              sha(data) == expected and data == old_blob(path.relative_to(repo).as_posix()))
    clone_path = REUSE + "CLONE_CANDIDATES_68.json"
    clone_bytes = read(repo / clone_path)
    check("immutable_68_clone_rows_retained",
          clone_bytes == old_blob(clone_path)
          and sha(clone_bytes) == ast.literal_eval(old_assign["CLONE_SHA256"])
          and len(json.loads(clone_bytes)) == 68)
    clone_ast_old = ast.parse(old[REUSE + "REBUILD_CLONE_CANDIDATES.py"])
    clone_ast_new = ast.parse(current[REUSE + "REBUILD_CLONE_CANDIDATES.py"])
    clone_ast_old.body.pop(0)
    clone_ast_new.body.pop(0)
    check("clone_scanner_code_unchanged_except_module_docstring", dump(clone_ast_old) == dump(clone_ast_new))

    tests_old = ast.parse(old[REUSE + "test_fkrg_reuse.py"])
    tests_new = ast.parse(current[REUSE + "test_fkrg_reuse.py"])
    added_tests = {
        "test_path_realization_native_ownership_types_and_registered_edges",
        "test_path_realization_same_source_and_canonical_reuse",
        "test_path_realization_public_witness_really_uses_all_private_mass_facts",
        "test_path_realization_registration_preserves_raw_execution_and_metadata_scope",
    }
    old_tests = {n.name for n in ast.walk(tests_old) if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")}
    new_tests = {n.name for n in ast.walk(tests_new) if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")}
    check("exact_four_new_test_methods_old_fifty_retained",
          len(old_tests) == 50 and len(new_tests) == 54 and new_tests - old_tests == added_tests
          and old_tests <= new_tests)
    normalized_tests = copy.deepcopy(tests_new)
    for cls in normalized_tests.body:
        if isinstance(cls, ast.ClassDef):
            cls.body = [n for n in cls.body if not (isinstance(n, ast.FunctionDef) and n.name in added_tests)]
    normalized_old = copy.deepcopy(tests_old)

    class Counts(ast.NodeTransformer):
        def visit_Constant(self, node):
            if type(node.value) is int:
                node.value = {684: 691, 673: 680, 4272: 4345, 479: 552,
                              108: 133, 10: 11, 727: 841, 5614: 5728}.get(node.value, node.value)
            return node

    for node in ast.walk(normalized_old):
        if not isinstance(node, ast.FunctionDef):
            continue
        if node.name == "test_evidence_and_sources_exact_baseline":
            Counts().visit(node)
        elif node.name == "test_calibrated_defect_overlay_chain_and_kernel_graph":
            assert node.body[0].value.args[1].value == 10
            node.body[0].value.args[1].value = 11
        elif node.name == "test_new_lean_module_cannot_be_omitted_from_index":
            assert node.body[1].value.args[1].value == 684
            node.body[1].value.args[1].value = 691
    check("all_old_test_logic_preserved_except_exact_current_totals", dump(normalized_old) == dump(normalized_tests))

    graph_csv = read(audit_dir / "all_3793_theorem_direct_reuse_graph.csv").decode()
    graph = {r["name"]: json.loads(r["source_theorem_deps_json"])
             for r in csv.DictReader(io.StringIO(graph_csv))}
    prior_graph = None
    for index, overlay in enumerate(overlays):
        for row in overlay["public_theorems"]:
            assert row["name"] not in graph
            graph[row["name"]] = row.get("source_theorem_deps", [])
        for repair in overlay.get("existing_proof_dependency_repairs", []):
            assert graph[repair["name"]] == repair["prior_source_theorem_deps"]
            assert set(repair["actual_source_theorem_deps"]) == set(graph[repair["name"]]) | set(repair["added_source_theorem_deps"])
            graph[repair["name"]] = repair["actual_source_theorem_deps"]
        if index == 9:
            prior_graph = copy.deepcopy(graph)
    check("all_prior_registered_nodes_and_edges_preserved",
          len(prior_graph) == 4272 and sum(map(len, prior_graph.values())) == 5614
          and all(graph[k] == v for k, v in prior_graph.items()))
    check("full_current_graph_independently_reconstructed",
          len(graph) == 4345 and sum(map(len, graph.values())) == 5728
          and len(set(graph) - set(prior_graph)) == 73
          and sum(len(graph[k]) for k in set(graph) - set(prior_graph)) == 114
          and all(set(ds) <= set(graph) for ds in graph.values()))
    native = obj(repo / overlays[-1]["native_export_evidence"]["path"])
    scope = {r["name"]: r for r in native["all_native_theorem_constants"]}
    for row in overlays[-1]["public_theorems"]:
        name = row["name"]
        check("new_registered_edge_set_from_actual_constants:" + name,
              set(row["source_theorem_deps"]) == (set(scope[name]["direct_constants"]) & set(graph)) - {name})
    spec = importlib.util.spec_from_file_location("independent_review_live_reuse", repo / consumer_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    live_data = module.load()
    live_graph = {k: json.loads(v["source_theorem_deps_json"]) for k, v in live_data["graph"].items()}
    check("normal_freshness_checked_live_graph_equals_independent_reconstruction", live_graph == graph)
    live_status = module.status(live_data)

    dag_path = TC + "unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json"
    dag = json.loads(current[dag_path])
    old_dag = json.loads(old[dag_path])
    builder = TC + "unified_closure/build_umc_global_map.py"
    check("dag_builder_unchanged_from_accepted_base", read(repo / builder) == old_blob(builder))
    entries = dag["entries"]
    core = repo / CORE
    paths = [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]
    modules = {p.relative_to(core).with_suffix("").as_posix().replace("/", "."): p for p in paths if p.is_file()}
    check("dag_exact_complete_691_module_set", len(modules) == 691 and set(entries) == set(modules))
    declaration = re.compile(r'^\s*(?:(?:@\[[^\]\n]*\]|private|protected|noncomputable|unsafe)\s+)*'
                             r'(theorem|lemma|structure|class|def|abbrev|inductive)\s+'
                             r"([A-Za-z_][A-Za-z_0-9']*)", re.M)
    source_digest = hashlib.sha256()
    computed = {}
    for name, path in sorted(modules.items()):
        data = read(path)
        source_digest.update(name.encode() + b"\0" + data + b"\0")
        text = data.decode()
        category = "Core_v3_and_Substrate"
        for marker, label in (("/TheoryCompletion/UnifiedClosure/", "UMC_New_Bridges"),
            ("/TheoryCompletion/ScientificClosure/", "C1_C7_SISC"),
            ("/TheoryCompletion/", "P0_P12_TheoryCompletion"), ("/Compression/Hierarchy/", "Hierarchy"),
            ("/Compression/Objecthood/", "Objecthood"), ("/Compression/CrossTrack/", "CrossTrack"),
            ("/Compression/", "Compression_Frozen_Bridges")):
            if marker in path.as_posix():
                category = label
                break
        heads = re.findall(r'/-!\s*#\s+([^\n]+)', text)
        tokens = declaration.findall(text)
        computed[name] = {"source": path.relative_to(repo).as_posix(), "bytes": len(data),
            "lines": len(text.splitlines()), "category": category,
            "title": heads[0][:160] if heads else None,
            "imports": re.findall(r'^\s*import\s+(\S+)', text, re.M),
            "theorem_lemma_count": sum(k in ("theorem", "lemma") for k, _ in tokens),
            "decl_count": len(tokens)}
    check("all_691_dag_entries_equal_current_source_metadata", computed == entries and source_digest.hexdigest() == SOURCE)
    changed_old = [k for k in old_dag["entries"] if old_dag["entries"][k] != entries[k]]
    check("old_dag_only_public_root_metadata_changes",
          changed_old == ["UEOT.V3.Compression.TheoryCompletion"]
          and set(entries) - set(old_dag["entries"]) == {r["module"] for r in overlays[-1]["added_modules"]})
    adjacency = {k: [x for x in v["imports"] if x in entries] for k, v in entries.items()}
    missing = {k: [x for x in v["imports"] if x.startswith("UEOT.") and x not in entries]
               for k, v in entries.items() if any(x.startswith("UEOT.") and x not in entries for x in v["imports"])}
    reachable, queue = set(), ["UEOT"]
    while queue:
        name = queue.pop()
        if name not in reachable:
            reachable.add(name)
            queue.extend(adjacency[name])
    indegree = Counter(x for ds in adjacency.values() for x in ds)
    degrees = {k: indegree[k] for k in entries}
    ready = deque(k for k, n in degrees.items() if n == 0)
    removed = 0
    while ready:
        name = ready.popleft()
        removed += 1
        for child in adjacency[name]:
            degrees[child] -= 1
            if degrees[child] == 0:
                ready.append(child)
    cross = Counter((entries[k]["category"], entries[x]["category"])
                    for k, ds in adjacency.items() for x in ds if entries[k]["category"] != entries[x]["category"])
    check("dag_closed_root_reachable_and_acyclic_independent_graph_walk",
          len(reachable) == removed == 691 and missing == {} and dag["cycles_detected"] == []
          and dag["not_reachable_from_UEOT_root"] == [] and dag["missing_internal_imports"] == {})
    check("dag_all_aggregate_metadata_reconstructed",
          dag["source_tree_sha256"] == SOURCE and dag["total_Lean_modules"] == 691
          and dag["reachable_from_UEOT_root"] == len(reachable)
          and dag["total_source_lines"] == sum(x["lines"] for x in entries.values())
          and dag["total_theorem_lemma_tokens"] == sum(x["theorem_lemma_count"] for x in entries.values())
          and dag["category_counts"] == dict(Counter(x["category"] for x in entries.values()))
          and dag["most_imported_first_party"] == [{"module": k, "direct_dependents": indegree[k]}
              for k in sorted(entries, key=lambda k: (-indegree[k], k))[:45]]
          and dag["cross_category_direct_edges"] == [{"from": a, "to": b, "edges": n}
              for (a, b), n in sorted(cross.items())]
          and dag["scope"] == old_dag["scope"] and dag["source_semantics"] == old_dag["source_semantics"])

    gates = {}
    for name, count, expected_sha in (
        ("reuse-01", 54, "eab49e8dfe1ce6eabb61dae048e766f3a474a74adae4c26c4b7a067ce94eb234"),
        ("fkrg-01", 30, "51d9e76473d89286b8dd6ebbd9a07f6785c41c2514da3d756c0f2f08c8d03d2b"),
        ("clone-01", None, "518569eb6345554b04818fe3d98fb59a82a35e5b8fc7a0d9aecebc2348b04c13")):
        directory = packet / "local-gates" / name
        receipt = obj(directory / "RECEIPT.json")
        stdout, stderr = read(directory / "STDOUT.txt"), read(directory / "STDERR.txt")
        check("actual_gate_receipt_and_raw_logs:" + name,
              sha(read(directory / "RECEIPT.json")) == expected_sha
              and receipt["state"] == "PASS" and receipt["exit_code"] == 0
              and receipt["unfiltered_normal_script_entrypoint"] is True
              and len(receipt["command"]) == 2 and receipt["source_tree_sha256"] == SOURCE
              and receipt["module_count"] == 691 and receipt["inputs_and_sources_unchanged"] is True
              and receipt["input_sha256_before"] == receipt["input_sha256_after"]
              and sha(stdout) == receipt["stdout_sha256"] and sha(stderr) == receipt["stderr_sha256"]
              and sha(read(packet / "local-gates/run_current_gate.py")) == receipt["runner_sha256"])
        for path, expected in receipt["input_sha256_after"].items():
            check("gate_input_still_exact:" + name + ":" + path, sha(read(repo / path)) == expected)
        for path in receipt["immutable_input_paths_equal_baseline"]:
            check("gate_immutable_input_is_baseline:" + name + ":" + path, read(repo / path) == old_blob(path))
        if count is not None:
            text = stderr.decode()
            logged = re.findall(r'^test_.* \.\.\. ok$', text, re.M)
            check("full_unfiltered_zero_skip_test_log:" + name,
                  len(logged) == count and re.search(rf'Ran {count} tests in [0-9.]+s', text) is not None
                  and text.rstrip().endswith("OK") and "skipped" not in text.lower()
                  and receipt["result"] == {"expected_test_methods": count, "actual_tests": count,
                      "skipped": False, "unittest_ok": True})
        else:
            check("full_current_clone_scan_exact_68_rows",
                  json.loads(stdout) == receipt["result"] and receipt["result"]["status"] == "PASS"
                  and receipt["result"]["cross_file_proof_related_code_clone_pairs"] == 68
                  and stderr == b"")
        if name == "fkrg-01":
            check("actual_real_fast_audit_case_executed",
                  b"test_real_fast_audit_preserves_all_historical_receipts" in stderr
                  and b"UMC_LOCAL_BRANCH_AUDIT" in stdout)
        gates[name] = {"receipt_sha256": expected_sha, "seconds": receipt["seconds"],
                       "result": receipt["result"], "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr)}
    parser_dir = packet / "local-gates/parser-01"
    prior_parser = obj(parser_dir / "RECEIPT.json")
    check("original_89_parser_pass_reused_without_rerun",
          prior_parser["status"] == "PASS" and prior_parser["unittest_ran_count"] == 89
          and prior_parser["unittest_skipped_count"] == 0 and prior_parser["test_suite_modified_or_filtered"] is False
          and sha(read(parser_dir / "STDERR.txt")) == prior_parser["stderr_sha256"]
          and sha(read(parser_dir / "STDOUT.txt")) == prior_parser["stdout_sha256"])

    for name in (TC + "knowledge/README.md", REUSE + "README.md"):
        text = current[name].decode()
        check("current_documentation_boundaries:" + name,
              SOURCE in text and "4,345" in text and "5,728" in text
              and "NOT_ESTABLISHED" in text and "249" in text and "114" in text)
        diff = subprocess.check_output(["git", "diff", "--unified=0", BASE, "--", name], cwd=repo).decode()
        added = "\n".join(l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++"))
        for target in re.findall(r'\]\(([^)]+)\)', added):
            file = target.split("#", 1)[0]
            if file and not re.match(r"https?://", file):
                check("new_documentation_reference_exists:" + target, (repo / name).parent.joinpath(file).exists())
    check("all_reviewed_bytes_stable", all(p.read_bytes() == data for p, data in observed.items()))
    result = {
        "schema": "PATH_REALIZATION_INDEPENDENT_CONSUMER_DAG_REVIEW_V1",
        "state": "CLEAR_SIX_CONSUMERS_DAG_OLD_TEN_PRESERVATION_AND_ACTUAL_LOCAL_GATES",
        "reviewer": "/root/finite_memory_realization", "consumer_author": "/root/c3_executable_search",
        "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Independent full six-path diffs, exact old evidence preservation, complete source/DAG and proof-graph reconstruction, existing actual gate logs",
        "independence": "Reviewer did not edit the six consumers, generate the accepted DAG, run the local suites or execute registration. Prior protocol authorship and three Lean modules are disclosed in the separate registration review; this is not self-mathematics certification.",
        "baseline_ref": BASE, "source_tree_sha256": SOURCE,
        "applied_manifest_sha256": sha(read(applied_path)), "six_paths": applied["paths"],
        "old_overlay_count_preserved": 10, "retained_artifacts": retained,
        "consumer_logic_unchanged_except_four_registry_appends": True,
        "old_test_count": 50, "new_test_count": 54, "added_tests": sorted(added_tests),
        "full_source_modules": 691, "dag_all_entries_checked": 691,
        "dag_root_reachable": 691, "dag_cycles": [], "dag_missing_internal_imports": {},
        "live_graph_status_from_normal_freshness_load": live_status,
        "old_graph_nodes": 4272, "old_graph_edges": 5614,
        "new_graph_nodes": 4345, "new_graph_edges": 5728,
        "new_direct_edges_from_actual_constants": 114,
        "actual_local_gate_logs_reviewed": gates,
        "parser_89_reused_not_rerun": True,
        "checks_passed": checks, "check_script_sha256": sha(Path(__file__).read_bytes()),
        "remaining": ["Canonical integration and its separate actual receipt", "Git-object preflight",
                      "Publication/CI/resulting-main and final dual-end tree identity"],
        "raw_receipts_rewritten": False, "global_mathematical_closure": "NOT_ESTABLISHED",
    }
    output = Path(__file__).parent / "CONSUMER_DAG_REVIEW.json"
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"state": result["state"], "checks": len(checks),
        "output": str(output), "sha256": sha(output.read_bytes())}, indent=2))


if __name__ == "__main__":
    main()
