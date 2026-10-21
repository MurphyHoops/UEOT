#!/usr/bin/env python3
"""Prepare an evidence-bound five-file consumer patch, without running Lean.

The default writes only a proposed tree, patch and receipt to --output.
--apply installs those exact five proposed files after all inputs pass.
Raw native/registration artifacts must already exist; no pending value is
substituted for an actual count or digest. The nine prior overlays and all
47 existing regression methods are preserved, apart from current counts.
"""
from __future__ import annotations

import argparse
import ast
import difflib
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from string import Template
import types

HERE = Path(__file__).resolve().parent
BASE = "299a4e3a71914af064ccd7916bb285bac201f62a"
SOURCE = "179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6"
KNOWLEDGE = "formalization/ueot-core/docs/compression/theory_completion/knowledge/"
REUSE = KNOWLEDGE + "reuse/"
PACKET = "formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/"
OVERLAY = "FINITE_MEMORY_REUSE_OVERLAY_V1.json"
NATIVE = "FINITE_MEMORY_NATIVE_V1.json"
VERIFIER = "VERIFY_FINITE_MEMORY_OVERLAY_TYPES.lean"
PATHS = (REUSE + "fkrg_reuse.py", REUSE + "test_fkrg_reuse.py",
         REUSE + "REBUILD_CLONE_CANDIDATES.py", KNOWLEDGE + "README.md", REUSE + "README.md")
BASE_SHA256S = (
    "c598f8c5aad77afbac3082dee7ceebf79471408f6646fa1567ebf09027acfc74",
    "692b427234dffff6915ed1297c5e1fb0c256577369605691be38cb68ae2797e7",
    "75650dd952415292da28df5056be8504ae7b8468349cf0ea02fb42b85e4a4b2d",
    "ffcce5a5f854ea6c8d17f898608dbbdfef903d2ff3e3ee4997c240baf4f49d16",
    "91eb7bef6b7268e6c76899c35fcf0490fb21f699e3e2a8a16559d3f8e14d2120",
)
ADDITIONS = {"lexical_pr_preflight", "registration_provenance"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
MODULES = {PREFIX + name for name in (
    "FiniteMemoryPolicy", "FiniteSupportFixedPoint", "SupportMemoryController",
    "SupportMemoryCheck", "FiniteMemorySeparation", "FiniteMemoryCheckWitness")}


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


def digest(data):
    return sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def replace_once(text, before, after):
    require(text.count(before) == 1, "PATCH_ANCHOR_NOT_UNIQUE: " + before[:120])
    return text.replace(before, after, 1)


def module_from_bytes(path, data):
    module = types.ModuleType("finite_memory_proposed_reuse")
    module.__file__ = str(path)
    exec(compile(data, str(path), "exec"), module.__dict__)
    return module


def test_methods(code):
    return {node.name: ast.dump(node, include_attributes=False)
            for node in ast.walk(ast.parse(code))
            if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--native-archive", required=True,
                        help="Repository-relative actual-execution/native-NN registration archive")
    parser.add_argument("--output", required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    repo = Path(args.repo).resolve(strict=True)
    output = Path(args.output).resolve()
    archive = (repo / args.native_archive).resolve(strict=True)
    require(archive.is_relative_to(repo / PACKET), "NATIVE_ARCHIVE_OUTSIDE_INCREMENT")
    require(output != repo and not any((repo / p).is_relative_to(output) for p in PATHS),
            "OUTPUT_OVERLAPS_LIVE_CONSUMERS")
    reads = {}

    def read(path):
        path = Path(path)
        require(path.is_file() and not path.is_symlink(), "MISSING_OR_SYMLINK_INPUT: " + str(path))
        if path not in reads:
            reads[path] = path.read_bytes()
        return reads[path]

    def load(path):
        return json.loads(read(path))

    old = {}
    for path, expected in zip(PATHS, BASE_SHA256S):
        data = subprocess.run(["git", "show", BASE + ":" + path], cwd=repo,
                              check=True, capture_output=True).stdout
        require(digest(data) == expected, "BASE_CONSUMER_DRIFT: " + path)
        old[path] = data.decode()

    reuse = module_from_bytes(repo / PATHS[0], old[PATHS[0]].encode())
    prior = reuse.load(verify_source=False)
    require(len(prior["overlays"]) == 9 and len(prior["modules"]) == 678 and
            len(prior["graph"]) == 4237, "WRONG_PRIOR_CONSUMER_SCOPE")
    old_edges = sum(len(json.loads(row["source_theorem_deps_json"]))
                    for row in prior["graph"].values())
    require(old_edges == 5567, "WRONG_PRIOR_GRAPH")

    overlay = load(repo / REUSE / OVERLAY)
    raw = load(archive / OVERLAY)
    native = load(repo / REUSE / NATIVE)
    receipt = load(archive / "REGISTRATION_RECEIPT.json")
    status = load(archive / "STATUS.json")
    pre = load(archive / "SOURCE_PREFLIGHT.json")
    require(receipt["schema"] == "FINITE_MEMORY_REGISTRATION_RECEIPT_V1" and
            receipt["state"] == "PASS_METADATA_ONLY_CONSUMER_UNCHANGED", "REGISTRATION_NOT_PASSED")
    require(status["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION", "NATIVE_NOT_PASSED")
    require(pre["status"] == "PENDING_ACTUAL_NATIVE_EXECUTION", "PREFLIGHT_HISTORY_CHANGED")
    require(overlay["baseline_ref"] == receipt["baseline_ref"] == status["baseline_ref"] == BASE,
            "AUTHORIZATION_BASE_MISMATCH")
    require(overlay["source_checkpoint"] == "worktree-sha256:" + SOURCE and
            overlay["source_checkpoint_kind"] == "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT" and
            receipt["source_tree_sha256"] == pre["source_tree_sha256"] == SOURCE,
            "FROZEN_SOURCE_MISMATCH")
    require(set(overlay) - set(raw) == ADDITIONS and
            {k: v for k, v in overlay.items() if k not in ADDITIONS} == raw and
            set(receipt["added_top_level_keys"]) == ADDITIONS and
            receipt["stripped_registered_json_equals_raw"] is True,
            "REGISTRATION_CHANGED_RAW_PAYLOAD")
    require(receipt["candidate_ref"] is None and
            receipt["git_object_pr_preflight"] == "NOT_PERFORMED_SEPARATE_GATE",
            "REGISTRATION_CLAIMS_SEPARATE_GATE")
    overlay_bytes = read(repo / REUSE / OVERLAY)
    require(receipt["registered_overlay"] == {"path": REUSE + OVERLAY,
            "sha256": digest(overlay_bytes)} and
            receipt["raw_overlay_sha256"] == digest(read(archive / OVERLAY)) and
            read(archive / "REGISTERED_OVERLAY.json") == overlay_bytes,
            "REGISTERED_BYTES_MISMATCH")
    provenance = overlay["registration_provenance"]
    require(provenance["inputs"] == receipt["input_files"] and
            provenance["source_tree_sha256"] == SOURCE and
            provenance["baseline_ref"] == BASE and
            provenance["consumer_registry_modified"] is False,
            "REGISTRATION_PROVENANCE_MISMATCH")
    roles_and_paths = [(row["role"], row["path"]) for row in provenance["inputs"]]
    require(len(set(roles_and_paths)) == len(roles_and_paths), "DUPLICATED_REGISTRATION_INPUT_ROLE")
    for row in provenance["inputs"]:
        path = (repo / row["path"]).resolve(strict=True)
        require(path.is_relative_to(repo) and digest(read(path)) == row["sha256"],
                "REGISTRATION_INPUT_DRIFT: " + row["path"])
    build_rows = [row for row in provenance["inputs"] if row["role"] == "actual_full_build"
                  and row["path"].endswith("/FULL_BUILD_RECEIPT.json")]
    require(len(build_rows) == 1, "FULL_BUILD_RECEIPT_NOT_UNIQUE")
    build = load(repo / build_rows[0]["path"])
    require(build["baseline_ref"] == BASE and build["full_build"]["exit_code"] == 0 and
            digest(read(repo / build_rows[0]["path"])) == overlay["native_execution"]["build_receipt_sha256"],
            "FULL_BUILD_NOT_BOUND")
    require(overlay["native_export_evidence"] == {"path": REUSE + NATIVE,
            "sha256": digest(read(repo / REUSE / NATIVE))}, "NATIVE_HASH_MISMATCH")
    require(read(repo / REUSE / NATIVE) == read(archive / NATIVE) and
            read(repo / REUSE / VERIFIER) == read(archive / VERIFIER) and
            native == load(archive / "observed_first_native.json"), "ACTUAL_REPLAY_MISMATCH")
    execution = overlay["native_execution"]
    require(execution["native_export_exit_code"] == execution["fixed_certificate_exit_code"] == 0 and
            execution["fixed_export_equals_initial_native_export"] is True and
            execution["source_tree_sha256"] == SOURCE and
            execution["fixed_certificate_sha256"] == digest(read(repo / REUSE / VERIFIER)),
            "ACTUAL_EXECUTION_NOT_PASSED")
    require(overlay["base_snapshot_modules"] == 678 and
            {row["module"] for row in overlay["added_modules"]} == MODULES and
            len(overlay["added_modules"]) == 6 and pre["complete_source_modules"] == 684 and
            overlay["added_modules"] == pre["added_modules"], "SOURCE_MODULE_SCOPE_MISMATCH")
    require("historical_public_repairs" not in overlay and
            "existing_proof_dependency_repairs" not in overlay, "UNEXPECTED_HISTORICAL_REPAIR")
    require(overlay["scientific_role"] == "UNCOUNTED_FINITE_SUPPORT_MEMORY_CONTROL" and
            overlay["counted_core_impact"] == "NONE" and
            overlay["scientific_closure"] == "NOT_ESTABLISHED", "SCIENTIFIC_ROLE_MISMATCH")

    public = {row["name"]: row for row in overlay["public_theorems"]}
    native_public = {row["name"]: row for row in native["public_source_theorems"]}
    scope = native["all_native_theorem_constants"]
    by_name = {row["name"]: row for row in scope}
    require(len(public) == len(overlay["public_theorems"]) == len(native_public) == 35 and
            set(public) == set(native_public) and len(by_name) == len(scope), "NATIVE_PUBLIC_SCOPE_MISMATCH")
    require(native["schema"] == "FINITE_MEMORY_NATIVE_EXPORT_V1" and native["collisions"] == [] and
            {row["source_module"] for row in scope} == MODULES and
            all(set(row["axioms"]) <= AXIOMS for row in scope), "NATIVE_OWNER_OR_AXIOM_MISMATCH")
    registered = set(prior["graph"]) | set(public)
    require(len(registered) == 4272, "REGISTERED_NAME_COLLISION")
    for name, row in public.items():
        full = by_name[name]
        actual = sorted((set(full["direct_constants"]) & registered) - {name})
        require(not full["is_private"] and row["source_module"] == full["source_module"] and
                sorted(row["source_theorem_deps"]) == actual and
                sorted(row["source_theorem_deps"]) == sorted(native_public[name]["source_theorem_deps"]),
                "PUBLIC_NATIVE_EDGE_MISMATCH: " + name)
    distinct = overlay["type_distinctness"]
    deps = overlay["proof_dependency_certification"]
    require(distinct["status"] == deps["status"] == overlay["native_axiom_census"]["status"] == "PASS" and
            distinct["registered_prior_theorems"] == 4237 and
            distinct["cross_isDefEq_comparisons"] == 35 * 4237 and
            distinct["internal_isDefEq_comparisons"] == 35 * 34 // 2 and
            distinct["definitionally_equal_matches"] == 0, "TYPE_OR_EDGE_CERTIFICATE_MISMATCH")
    edge_pairs = {(name, target) for name, row in public.items() for target in row["source_theorem_deps"]}
    edge_count = sum(len(row["source_theorem_deps"]) for row in public.values())
    require(edge_count == len(edge_pairs) == deps["registered_direct_edges"] == len(deps["edges"]) and
            edge_pairs == {(row["source"], row["target"]) for row in deps["edges"]}, "EDGE_CENSUS_MISMATCH")
    lexical = overlay["lexical_pr_preflight"]
    hinted = sum(bool(row["reuse_candidates"]) for row in pre["lexical_reuse_hints"])
    require(hinted == lexical["new_theorems_with_lexical_reuse_candidates"] == 6 and
            lexical["candidate_ref"] is None, "LEXICAL_SCOPE_MISMATCH")
    prior_status = reuse.status(prior)
    total_edges = old_edges + edge_count
    overlay_edges = prior_status["overlay_registered_direct_edges"] + edge_count
    private_count = sum(row["is_private"] for row in scope)
    context = {"BASE": BASE, "SOURCE": SOURCE,
               "NATIVE_SHA256": digest(read(repo / REUSE / NATIVE)),
               "VERIFIER_SHA256": digest(read(repo / REUSE / VERIFIER)),
               "OVERLAY_SHA256": digest(overlay_bytes), "NATIVE_COUNT": len(scope),
               "PRIVATE_COUNT": private_count, "OTHER_COUNT": len(scope) - private_count - len(public),
               "NEW_EDGES": edge_count, "TOTAL_EDGES_FORMATTED": f"{total_edges:,}",
               "OVERLAY_EDGES": overlay_edges}

    new = dict(old)
    code = old[PATHS[0]]
    for before, after in (
        ('    HERE / "LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json",',
         '    HERE / "LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json",\n    HERE / "' + OVERLAY + '",'),
        ('    HERE / "VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean",',
         '    HERE / "VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean",\n    HERE / "' + VERIFIER + '",'),
        ('    "' + reuse.OVERLAY_SHA256S[-1] + '",',
         '    "' + reuse.OVERLAY_SHA256S[-1] + '",\n    "' + context["OVERLAY_SHA256"] + '",'),
        ('    "' + reuse.OVERLAY_TYPE_CHECK_SHA256S[-1] + '",',
         '    "' + reuse.OVERLAY_TYPE_CHECK_SHA256S[-1] + '",\n    "' + context["VERIFIER_SHA256"] + '",'),
        ("registered-interfaces and longterm-control-statistics overlays",
         "registered-interfaces, longterm-control-statistics and finite-memory overlays"),
    ):
        code = replace_once(code, before, after)
    new[PATHS[0]] = code
    proposed_reuse = module_from_bytes(repo / PATHS[0], code.encode())
    current = proposed_reuse.load()
    actual_status = proposed_reuse.status(current)
    require(actual_status["module_source_hashes_verified"] == 684 and
            actual_status["ueot_maintained_modules"] == 673 and actual_status["vendor_modules"] == 11 and
            actual_status["public_source_theorems_with_direct_proof_graph"] == 4272 and
            actual_status["overlay_count"] == 10 and actual_status["overlay_public_theorems"] == 479 and
            actual_status["overlay_registered_direct_edges"] == overlay_edges and
            actual_status["overlay_lexical_reuse_candidates"] == 108, "PROPOSED_CONSUMER_CENSUS_MISMATCH")
    for path_name in ("OVERLAY_PATHS", "OVERLAY_TYPE_CHECKS", "OVERLAY_SHA256S", "OVERLAY_TYPE_CHECK_SHA256S"):
        require(getattr(proposed_reuse, path_name)[:-1] == getattr(reuse, path_name),
                "PRIOR_REGISTRY_REWRITTEN: " + path_name)
    require(all(current["graph"][name] == row for name, row in prior["graph"].items()),
            "PRIOR_PROOF_GRAPH_REWRITTEN")

    tests = old[PATHS[1]]
    for before, after in (
        ('res["module_source_hashes_verified"], 678', 'res["module_source_hashes_verified"], 684'),
        ('res["ueot_maintained_modules"], 667', 'res["ueot_maintained_modules"], 673'),
        ('res["public_source_theorems_with_direct_proof_graph"], 4237', 'res["public_source_theorems_with_direct_proof_graph"], 4272'),
        ('res["overlay_public_theorems"], 444', 'res["overlay_public_theorems"], 479'),
        ('res["overlay_lexical_reuse_candidates"], 102', 'res["overlay_lexical_reuse_candidates"], 108'),
        ('res["overlay_count"], 9', 'res["overlay_count"], 10'),
        ('res["overlay_registered_direct_edges"], 680', f'res["overlay_registered_direct_edges"], {overlay_edges}'),
        ('for row in self.data["graph"].values()), 5567)', f'for row in self.data["graph"].values()), {total_edges})'),
        ('len(self.data["overlays"]), 9', 'len(self.data["overlays"]), 10'),
        ('len(live), 678', 'len(live), 684'),
    ):
        tests = replace_once(tests, before, after)
    block = Template(read(HERE / "regressions.py.in").decode()).substitute(context)
    anchor = "    def test_historical_apostrophe_registration_and_existing_incoming_edge(self):"
    tests = replace_once(tests, anchor, block + "\n" + anchor)
    before_tests, after_tests = test_methods(old[PATHS[1]]), test_methods(tests)
    allowed_count_changes = {"test_evidence_and_sources_exact_baseline",
                             "test_calibrated_defect_overlay_chain_and_kernel_graph",
                             "test_new_lean_module_cannot_be_omitted_from_index"}
    require(len(before_tests) == 47 and len(after_tests) == 50 and
            set(before_tests) <= set(after_tests) and
            all(after_tests[name] == body for name, body in before_tests.items()
                if name not in allowed_count_changes), "HISTORICAL_REGRESSION_REWRITTEN")
    new[PATHS[1]] = tests

    clone = old[PATHS[2]]
    clone = replace_once(clone, "678 modules (667 maintained and 11 adapted upstream)",
                         "684 modules (673 maintained and 11 adapted upstream)")
    clone = replace_once(clone, "base plus nine governed overlays", "base plus ten governed overlays")
    clone = replace_once(clone, "and long-term/control/statistics.", "long-term/control/statistics,\nand finite-memory.")
    require(ast.dump(ast.Module(body=ast.parse(clone).body[1:], type_ignores=[]), include_attributes=False) ==
            ast.dump(ast.Module(body=ast.parse(old[PATHS[2]]).body[1:], type_ignores=[]), include_attributes=False),
            "CLONE_SCANNER_LOGIC_CHANGED")
    new[PATHS[2]] = clone

    knowledge = old[PATHS[3]]
    start = knowledge.index("The current long-term/control/statistics source census")
    end = knowledge.index("\n\n", start)
    knowledge = replace_once(knowledge, knowledge[start:end],
        f"The current finite-memory source census contains **684 bundled Lean modules: 673 UEOT-maintained and 11 adapted upstream modules**, with ten additive overlays. The registered public proof graph contains **4,272 nodes and {total_edges:,} direct edges**. The six new modules establish finite support fixed points, complete autonomous support memory, an executable bounded decision and exact memory-separation witnesses. The actual full `lake build UEOT`, native export and fixed-certificate replay passed against the frozen source fingerprint `{SOURCE}`; the two native executions produced equal complete exports. Independent review, consumer tests, canonical Git, CI, publication and resulting-main states retain their separate actual receipts.")
    knowledge = replace_once(knowledge, "The eighth overlay retains its historical",
        "The ninth overlay retains its historical 678-module long-term/control/statistics census, its 12 new modules and its own full-build/native results. The eighth overlay retains its historical")
    new_section = (
        f"The tenth layer adds [FINITE_MEMORY_NATIVE_V1.json](reuse/FINITE_MEMORY_NATIVE_V1.json): **{len(scope)} compiler-owned theorem constants in six physical modules**, comprising **35 public source candidates, {private_count} private constants and {len(scope) - private_count - 35} other nonprivate constants**. The full native scope includes generated theorem constants from `FiniteMemoryPolicy`, which contributes no explicit public source theorem candidate. Every record retains actual physical ownership, stored universes, displayed types, complete direct proof constants and a standard-only axiom closure. The 35 new public types were compared with all 4,237 prior registrations (**148,295 cross-layer and 595 internal comparisons**) with zero raw stored-type collisions. The new graph adds **{edge_count} direct registered edges**, giving **4,272 nodes and {total_edges:,} edges**, including 479 overlay nodes and {overlay_edges} outgoing overlay edges. The eighth layer's separate old-node repair is retained, and six new lexical hint groups bring the cumulative count to 108. The [layer-ten evidence table](reuse/README.md#layer-10--finite-support-fixed-points-and-complete-finite-memory) records the exact native, verifier and metadata-registration digests.\n\n"
        "The finite support arena stabilizes by its cardinality `M`, and the complete support controller has `M + 1 ≤ 2 ^ |X|` memory states, including the empty support. Every nonwinning memory uses one fixed fallback PMF. Exact initial-support, transition-support and certification matching connect the executable finite criterion to this controller's own all-times zero uncertified occupancy. The actual numeric kernels may vary with time while their support relation stays fixed. The Boolean program uses the existing finite-horizon recursion at `2 ^ |X| - 1`; this increment does not implement support elimination, a complexity bound, or a computable winning-action table. The two-state singleton-initial witness separates autonomous memory from stationary randomized observation feedback. Its mixed-support negative witness uses a separate explicit uniform initial law. Zero uncertified occupancy does not itself prove physical safety or compress the reference process's fallback checks. The [finite-memory results and boundaries](../unified_closure/finite_memory_v1/RESULTS_AND_BOUNDARIES.md) retain these hypotheses and the unchanged frozen counted classifications and `NOT_ESTABLISHED` status.\n\n"
    )
    knowledge = replace_once(knowledge, "## Required startup/recovery protocol (every new chat/agent)",
                             new_section + "## Required startup/recovery protocol (every new chat/agent)")
    new[PATHS[3]] = knowledge

    readme = old[PATHS[4]]
    readme = replace_once(readme,
        "The current nine-layer census is **678 modules = 667 UEOT-maintained + 11\nadapted upstream**, with **4,237 registered public theorem nodes** and\n**5,567 registered direct proof edges**.",
        f"The current ten-layer census is **684 modules = 673 UEOT-maintained + 11\nadapted upstream**, with **4,272 registered public theorem nodes** and\n**{total_edges:,} registered direct proof edges**.")
    layer = Template(read(HERE / "layer_ten.md.in").decode()).substitute(context)
    readme = replace_once(readme, "## Run from repository root", layer + "\n## Run from repository root")
    readme = replace_once(readme,
        "    lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean",
        "    lake env lean docs/compression/theory_completion/knowledge/reuse/" + VERIFIER)
    readme = replace_once(readme, "nine governed overlays extend the live census to 678 = 667 + 11.",
                         "ten governed overlays extend the live census to 684 = 673 + 11.")
    readme = replace_once(readme,
        "3,793 immutable-base public source theorem proofs + 444 governed registrations\n  (including one historical public-name repair) = 4,237 live graph nodes, with\n  5,567 direct registered-source theorem",
        f"3,793 immutable-base public source theorem proofs + 479 governed registrations\n  (including one historical public-name repair) = 4,272 live graph nodes, with\n  {total_edges:,} direct registered-source theorem")
    readme = replace_once(readme, "The ninth adds 149 edges, giving 680 outgoing edges from overlay nodes;",
        f"The ninth adds 149 edges and the tenth adds {edge_count}, giving {overlay_edges} outgoing edges from overlay nodes;")
    readme = replace_once(readme, "The current scanner recomputes all 678 modules", "The current scanner recomputes all 684 modules")
    readme = replace_once(readme, "against the exact 678-module live source census", "against the exact 684-module live source census")
    new[PATHS[4]] = readme

    for path in PATHS[:3]:
        ast.parse(new[path])
    for path in PATHS:
        live = read(repo / path)
        require(live == old[path].encode() or live == new[path].encode(), "LIVE_CONSUMER_UNEXPECTED_CHANGE: " + path)
    patch = "".join("".join(difflib.unified_diff(old[path].splitlines(keepends=True),
        new[path].splitlines(keepends=True), fromfile="a/" + path, tofile="b/" + path)) for path in PATHS)
    report = {"schema": "FINITE_MEMORY_CONSUMER_PROPOSAL_V1", "state": "PREPARED_NOT_APPLIED",
              "baseline_ref": BASE, "source_tree_sha256": SOURCE,
              "registration_receipt": {"path": (archive / "REGISTRATION_RECEIPT.json").relative_to(repo).as_posix(),
                                       "sha256": digest(read(archive / "REGISTRATION_RECEIPT.json"))},
              "prior_overlay_count_preserved": 9, "existing_regression_methods_preserved": 47,
              "new_regression_methods": sorted(set(after_tests) - set(before_tests)),
              "current_test_method_count": 50, "actual_native_context": context,
              "actual_proposed_consumer_status": actual_status,
              "patch_sha256": digest(patch.encode()),
              "files": [{"path": path, "before_sha256": digest(old[path].encode()),
                         "after_sha256": digest(new[path].encode())} for path in PATHS],
              "new_tests_executed": False, "clone_rescan_executed": False,
              "heavy_gates_executed": False}
    outputs = {output / "consumer.patch": patch.encode(),
               output / "PREPARED_CONSUMER_UPDATE.json": encoded(report)}
    outputs.update({output / "proposed" / path: new[path].encode() for path in PATHS})
    outputs.update({output / "baseline" / path: old[path].encode() for path in PATHS})
    for path, data in outputs.items():
        require(not path.exists() or path.read_bytes() == data, "PROPOSAL_DESTINATION_DIFFERS: " + str(path))
    for path, data in reads.items():
        require(path.read_bytes() == data, "INPUT_CHANGED_DURING_PREPARATION: " + str(path))
    for path, data in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists():
            path.write_bytes(data)
    if args.apply:
        for path in PATHS:
            (repo / path).write_text(new[path])
        applied = {**report, "state": "APPLIED_FIVE_CONSUMERS_TESTS_PENDING"}
        (output / "APPLIED_CONSUMER_UPDATE.json").write_bytes(encoded(applied))
    print(json.dumps({"state": "APPLIED_FIVE_CONSUMERS_TESTS_PENDING" if args.apply else report["state"],
                      "output": str(output), "patch_sha256": report["patch_sha256"],
                      "files": len(PATHS), "current_test_method_count": 50,
                      "native_constants": len(scope), "new_registered_edges": edge_count}, indent=2))


if __name__ == "__main__":
    main()
