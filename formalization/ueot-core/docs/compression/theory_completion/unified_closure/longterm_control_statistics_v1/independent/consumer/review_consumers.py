#!/usr/bin/env python3
"""Independent read-only review; writes only this review directory."""
import ast
import copy
import importlib.util
import json
from hashlib import sha1, sha256
from pathlib import Path
import subprocess
import sys

if not __debug__:
    raise RuntimeError("Review assertions require ordinary Python")

REPO = Path("/workspace/scratch/534b0448126c/ueot-core-next")
OUT = Path(__file__).resolve().parent
BASE = "ff71e63256c88ad2bb527fdd3004d55c77894ab7"
SOURCE = "60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31"
CORE = REPO / "formalization/ueot-core"
HERE = CORE / "docs/compression/theory_completion/knowledge/reuse"
EXEC = CORE / "docs/compression/theory_completion/unified_closure/longterm_control_statistics_v1/actual-execution"
checks = []


def check(label, condition):
    if not condition:
        raise AssertionError(label)
    checks.append(label)


def git_bytes(path):
    return subprocess.check_output(
        ["git", "show", BASE + ":" + path.relative_to(REPO).as_posix()], cwd=REPO)


def assignment(tree, name):
    return next(n for n in tree.body if isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == name for t in n.targets))


def normalized(tree):
    return ast.dump(tree, include_attributes=False)


input_files = [HERE / name for name in [
    "fkrg_reuse.py", "test_fkrg_reuse.py", "REBUILD_CLONE_CANDIDATES.py",
    "LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json",
    "LONGTERM_CONTROL_STATISTICS_NATIVE_V1.json",
    "VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean",
]]
before = {p: p.read_bytes() for p in input_files}
old_consumer = ast.parse(git_bytes(input_files[0]))
new_consumer = ast.parse(before[input_files[0]])
reduced = copy.deepcopy(new_consumer)
registries = ["OVERLAY_PATHS", "OVERLAY_TYPE_CHECKS", "OVERLAY_SHA256S",
              "OVERLAY_TYPE_CHECK_SHA256S"]
for name in registries:
    old = assignment(old_consumer, name).value
    new = assignment(reduced, name).value
    check(name + "_append_one_preserve_first_eight",
          isinstance(old, ast.List) and isinstance(new, ast.List)
          and len(old.elts) == 8 and len(new.elts) == 9
          and [normalized(x) for x in old.elts] == [normalized(x) for x in new.elts[:8]])
    new.elts = new.elts[:8]


def truth_value(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            for i, key in enumerate(node.keys):
                if isinstance(key, ast.Constant) and key.value == "source_of_truth":
                    return node, i
    raise AssertionError("Missing source_of_truth")


old_dict, old_index = truth_value(old_consumer)
new_dict, new_index = truth_value(reduced)
new_dict.values[new_index] = copy.deepcopy(old_dict.values[old_index])
check("consumer_executable_AST_unchanged_except_four_appends_and_description",
      normalized(reduced) == normalized(old_consumer))

old_tests = ast.parse(git_bytes(input_files[1]))
new_tests = ast.parse(before[input_files[1]])
old_class = next(n for n in old_tests.body if isinstance(n, ast.ClassDef))
new_class = next(n for n in new_tests.body if isinstance(n, ast.ClassDef))
old_methods = {n.name: n for n in old_class.body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")}
new_methods = {n.name: n for n in new_class.body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")}
added_tests = {
    "test_longterm_overlay_native_owner_types_and_edge_binding",
    "test_longterm_same_source_reuse_and_sisc_physical_owner",
}
check("45_old_tests_preserved_47_current_exactly_two_additions",
      len(old_methods) == 31 and len(new_methods) == 33
      and sum(isinstance(n, ast.FunctionDef) and n.name.startswith("test_")
              for c in old_tests.body if isinstance(c, ast.ClassDef) for n in c.body) == 45
      and sum(isinstance(n, ast.FunctionDef) and n.name.startswith("test_")
              for c in new_tests.body if isinstance(c, ast.ClassDef) for n in c.body) == 47
      and set(new_methods) - set(old_methods) == added_tests
      and set(old_methods) <= set(new_methods))
allowed_counts = {
    "test_evidence_and_sources_exact_baseline": {
        666: 678, 655: 667, 4147: 4237, 354: 444,
        75: 102, 8: 9, 531: 680, 5418: 5567,
    },
    "test_calibrated_defect_overlay_chain_and_kernel_graph": {8: 9},
    "test_new_lean_module_cannot_be_omitted_from_index": {666: 678},
}


class CounterUpdate(ast.NodeTransformer):
    def __init__(self, mapping):
        self.mapping = mapping
        self.hits = {key: 0 for key in mapping}

    def visit_Constant(self, node):
        if type(node.value) is int and node.value in self.mapping:
            self.hits[node.value] += 1
            node.value = self.mapping[node.value]
        return node


expected_tests = copy.deepcopy(old_tests)
expected_class = next(n for n in expected_tests.body if isinstance(n, ast.ClassDef))
for method in expected_class.body:
    if isinstance(method, ast.FunctionDef) and method.name in allowed_counts:
        transform = CounterUpdate(allowed_counts[method.name])
        transform.visit(method)
        check("only_expected_current_count_literals:" + method.name,
              all(hit == 1 for hit in transform.hits.values()))
reduced_tests = copy.deepcopy(new_tests)
reduced_class = next(n for n in reduced_tests.body if isinstance(n, ast.ClassDef))
reduced_class.body = [n for n in reduced_class.body
                      if not isinstance(n, ast.FunctionDef) or n.name not in added_tests]
check("all_old_test_semantics_unchanged_except_exact_current_count_literals",
      normalized(expected_tests) == normalized(reduced_tests))

old_scanner = git_bytes(input_files[2])
new_scanner = before[input_files[2]]
old_doc, new_doc = ast.parse(old_scanner).body[0], ast.parse(new_scanner).body[0]
check("scanner_algorithm_all_bytes_after_docstring_unchanged",
      old_scanner.splitlines(keepends=True)[old_doc.end_lineno:] ==
      new_scanner.splitlines(keepends=True)[new_doc.end_lineno:])

spec = importlib.util.spec_from_file_location("reviewed_fkrg_reuse", input_files[0])
reuse = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = reuse
spec.loader.exec_module(reuse)
data = reuse.load()
status = reuse.status(data)
expected_status = {
    "module_source_hashes_verified": 678, "ueot_maintained_modules": 667,
    "vendor_modules": 11, "public_source_theorems_with_direct_proof_graph": 4237,
    "verified_equal_type_groups": 37, "equal_type_statement_names": 77,
    "near_type_not_defeq_candidate_pairs": 15, "crossfile_exact_code_clone_candidates": 68,
    "overlay_public_theorems": 444, "overlay_cross_snapshot_defeq_matches": 0,
    "overlay_lexical_reuse_candidates": 102, "overlay_count": 9,
    "overlay_registered_direct_edges": 680, "overlay_historical_public_repairs": 1,
    "overlay_existing_registered_direct_edge_repairs": 1,
}
for key, value in expected_status.items():
    check("actual_loaded_status:" + key, status[key] == value)
check("actual_loaded_public_graph_edges_5567",
      sum(len(json.loads(r["source_theorem_deps_json"])) for r in data["graph"].values()) == 5567)

historical = list(reuse.OVERLAY_PATHS[:8]) + list(reuse.OVERLAY_TYPE_CHECKS[:8])
for path in reuse.OVERLAY_PATHS[:8]:
    native = json.loads(path.read_text()).get("native_export_evidence")
    if native:
        historical.append(REPO / native["path"])
historical.extend([reuse.AUDIT / name for name in reuse.EVIDENCE_SHA])
historical.extend([reuse.LEDGER, HERE / "CLONE_CANDIDATES_68.json"])
historical.extend(CORE / name for name in reuse.BUILD_ENVIRONMENT_SHA256)
historical = sorted(set(historical))
for path in historical:
    check("immutable_bytes:" + path.relative_to(REPO).as_posix(), path.read_bytes() == git_bytes(path))
clones = json.loads((HERE / "CLONE_CANDIDATES_68.json").read_text())
check("immutable_clone_68_pairs_12_long_max31",
      (len(clones), sum(x["equal_nonblank_code_lines"] >= 15 for x in clones),
       max(x["equal_nonblank_code_lines"] for x in clones)) == (68, 12, 31))
ledger = json.loads(reuse.LEDGER.read_text())
check("immutable_PID_106_generated11_adapter89_boundary6_generators4",
      tuple(ledger["coverage"][k] for k in ["final_disposition_pids", "generated_pids",
            "retained_adapter_pids", "retained_boundary_pids", "counted_generators"]) == (106, 11, 89, 6, 4))

tree = subprocess.check_output(["git", "ls-tree", "-r", "-z", BASE, "--",
    "formalization/ueot-core/UEOT.lean", "formalization/ueot-core/UEOT"], cwd=REPO)
changed_prior_sources = []
prior_count = 0
for record in tree.split(b"\0"):
    if not record:
        continue
    meta, rawpath = record.split(b"\t", 1)
    path = rawpath.decode()
    if not path.endswith(".lean"):
        continue
    prior_count += 1
    source = (REPO / path).read_bytes()
    blob = sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
    if blob != meta.decode().split()[2]:
        changed_prior_sources.append(path)
check("all_666_prior_package_sources_preserved_except_authorized_aggregator",
      prior_count == 666 and changed_prior_sources == [
          "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean"])

current = data["overlays"][8]
native = json.loads(before[input_files[4]])
check("registered_overlay_source_fingerprint", current["source_checkpoint"] == "worktree-sha256:" + SOURCE)
check("no_ninth_layer_historical_repair_keys",
      not {"historical_public_repairs", "existing_proof_dependency_repairs"} & current.keys())
scope = {row["name"]: row for row in native["all_native_theorem_constants"]}
public = {row["name"]: row for row in current["public_theorems"]}
native_public = {row["name"]: row for row in native["public_source_theorems"]}
check("native_scope_199_public90_private30", len(scope) == 199 and len(public) == 90
      and sum(row["is_private"] for row in scope.values()) == 30)
check("native_physical_owners_exact_12_modules",
      {row["source_module"] for row in scope.values()} == {row["module"] for row in current["added_modules"]}
      and len(current["added_modules"]) == 12)
check("native_all_standard_axioms", all(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
      for row in scope.values()))
check("same_public_name_set", set(public) == set(native_public) and set(public) <= set(scope))
for name, row in public.items():
    actual = (set(scope[name]["direct_constants"]) & set(data["graph"])) - {name}
    check("native_registered_edge_identity:" + name, set(row["source_theorem_deps"]) == actual)
    check("native_public_owner_type_identity:" + name,
          not scope[name]["is_private"]
          and row["source_module"] == scope[name]["source_module"]
          and all(native_public[name][field] == scope[name][field]
                  for field in ["source_module", "type", "level_parameters", "direct_constants"]))
check("native_registered_edge_total149", sum(len(row["source_theorem_deps"]) for row in public.values()) == 149)
check("native_type_comparisons_no_collisions",
      (native["cross_isDefEq_comparisons"], native["internal_isDefEq_comparisons"], native["collisions"]) ==
      (373230, 4005, []))

prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
sisc = "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC."
routes = [
    (prefix + "SameSourceKilledExitFluxCheck.actual_failure_mass_telescope",
     prefix + "SameSourceConditionedTerminalCheck.actual_survival_mass_at_zero"),
    (prefix + "SameSourceSurvivalTailCheck.killed_survival_mass_tendsto_homogeneous_neverHit_real",
     prefix + "SameSourceSafePrefixCheck.homogeneous_survival_real_eq_killed_pow_sum"),
    (sisc + "rowwise_protocol_calibrated_on_good", sisc + "rowwise_population_risk_eq_registered"),
    (sisc + "measure_rowwise_failure_to_identify_le", prefix + "RowwiseProbeSampling.measure_coordinateGood_compl_le"),
    (prefix + "SISCRowwiseProbeWitness.actual_product_candidate_power", sisc + "measure_rowwise_failure_to_identify_le"),
]
for caller, target in routes:
    check("actual_native_route:" + caller, target in scope[caller]["direct_constants"]
          and target in public[caller]["source_theorem_deps"])
policy = prefix + "SupportViabilityClosure."
check("actual_native_infinite_policy_registered_routes_exact",
      set(public[policy + "arbitrarily_long_zero_uncovered_iff_single_all_times_policy"]["source_theorem_deps"]) == {
          policy + "initial_infiniteViability_iff_exists_all_times_zero_uncovered_policy",
          policy + "initial_viability_iff_exists_zero_uncovered_policy"})
check("duplicate_time_zero_absent",
      prefix + "SameSourceKilledExitFluxCheck.actual_survival_zero" not in data["graph"])
check("sisc_owning_module_is_physical_UnifiedClosure",
      scope[sisc + "rowwise_protocol_calibrated_on_good"]["source_module"] ==
      prefix + "SISCRowwiseProbeCalibration"
      and reuse.explain(data, sisc + "rowwise_protocol_calibrated_on_good")["area"] ==
      "V3/Compression/TheoryCompletion/UnifiedClosure")
check("wrong_kernel_boundary_registered",
      prefix + "SISCRowwiseProbeWitness.exact_data_good_does_not_calibrate_wrong_kernel" in public)

umc_path = EXEC / "umc-full-01/UMC_FULL_AUDIT.json"
umc_status_path = EXEC / "umc-full-01/STATUS.json"
umc = json.loads(umc_path.read_text())
umc_status = json.loads(umc_status_path.read_text())
check("existing_UMC_full_receipt_source_and_scope",
      umc_status["exit_code"] == 0 and umc_status["source_tree_sha256"] == SOURCE
      and umc["full_Lean"] == "PASS" and umc["research_modules"] == 79
      and umc["UMC_native_census"]["theorem_constants"] == 1073
      and umc["UMC_axioms"] == "1073/1073_LEAN_STANDARD_AXIOMS"
      and umc["source_PIDs_located"] == 106 and umc["frozen_source_impact"] == "NONE")
check("UMC_raw_log_digest", sha256((EXEC / "umc-full-01/audit.log").read_bytes()).hexdigest() ==
      umc_status["log_sha256"])
source_review_path = OUT.parent / "source-chain-production-review/ACTUAL_EXECUTION_REVIEW.json"
source_review = json.loads(source_review_path.read_text())
check("separate_raw_execution_review_CLEAR_same_source",
      source_review["status"] == "ACTUAL_EXECUTION_EVIDENCE_REVIEW_CLEAR"
      and source_review["source_tree_sha256"] == SOURCE)
check("review_inputs_unchanged_during_review", all(path.read_bytes() == blob for path, blob in before.items()))

(OUT / "source-snapshots").mkdir(parents=True, exist_ok=True)
for path in input_files[:3]:
    (OUT / "source-snapshots" / path.name).write_bytes(before[path])
manifest = [{"path": path.relative_to(REPO).as_posix(), "sha256": sha256(blob).hexdigest(),
             "bytes": len(blob)} for path, blob in before.items()]
result = {
    "status": "INDEPENDENT_CONSUMER_REVIEW_CLEAR", "base": BASE, "source_tree_sha256": SOURCE,
    "scope": "Read-only consumer/test/evidence integration review; no gate suite, Lean build or Mac operation rerun",
    "inputs": manifest, "checks": checks, "check_count": len(checks),
    "old_test_count": 45, "current_test_count": 47, "added_test_names": sorted(added_tests),
    "historical_artifact_count_exact_bytes": len(historical),
    "current_status": status, "changed_prior_package_sources": changed_prior_sources,
    "proof_routes_checked": [{"caller": caller, "target": target} for caller, target in routes],
    "source_execution_review": {"path": str(source_review_path), "sha256": sha256(source_review_path.read_bytes()).hexdigest()},
    "UMC_full_receipt": {"path": str(umc_path), "sha256": sha256(umc_path.read_bytes()).hexdigest()},
    "test_semantics": "All 45 historical tests retained; only exact current-census literals in three old methods changed. Two additions bind observed native fields, proof routes and physical ownership.",
    "release_boundary": "Exact Git-object preflight, PR and resulting-main acceptance remain separate release gates; this review does not certify publication.",
}
(OUT / "CONSUMER_REVIEW.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({"status": result["status"], "checks": len(checks),
                  "historical_artifacts_unchanged": len(historical), "tests": [45,47],
                  "report": str(OUT / "CONSUMER_REVIEW.json")}, indent=2))
