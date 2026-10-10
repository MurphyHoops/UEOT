#!/usr/bin/env python3
"""Read-only FKRG theorem reuse navigator over pinned Lean audit evidence.

It does not prove logical equivalence from text, change Lean files, or become
an authoritative theorem ledger. Exact-type groups were verified separately
by 40/40 Lean Meta.isDefEq checks at the pinned UEOT environment.
"""
from __future__ import annotations

import argparse
import csv
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent / "audits" / "2026-10-10"
REPO = HERE.parents[6]
SCHEMA = "FKRG_REUSE_NAVIGATOR_V1"
SOURCE_BASELINE = "48b582beabec2ebae61ab0d51081b83356fcb3e1"

# Independent immutable digests calculated from main after merged PR #314.
# Changing a CSV and its claimed source hash together must fail closed.
EVIDENCE_SHA = {
    "EVERY_FILE_633_DETAILED_METRICS.csv": "3abeba50709ab1dd06e5245e81615ecee604995976a28ae945c5430de2343162",
    "EVERY_DECLARATION_5553_COMPACT.csv": "8baa41ef67a8cba4560f1ed22c510e212af728dcb88c921c17345f052e4e6ac9",
    "all_3793_theorem_direct_reuse_graph.csv": "1a52b06b9bae3efd92aea18b64ccc2c29ff314fe7571420d334bcc1b43d9d6a3",
    "ALL_binder_normalized_equal_type_clusters.json": "4b6f83592ae9002b3bd88e669d7ab3a0527f5915acd60cbb89b4907f17482f03",
    "NEAR_TYPE_15_DISTINCT_HEURISTIC_PAIRS.json": "3b6878de62b336e361c7d658edce00c2925c10f8d11a7cbd73ee29e7cd19721b",
    "SOURCE_PROVENANCE_BREAKDOWN.json": "968f4b8e16fe743c1a7e54d1fbe3c086585cd2c858c97b1490c08bc595c41079",
    "FOCUSED_14_REUSE_TRIAGE.md": "26e8ebb25049f65a81a6e5990b91ec2befad30b2a2d7f3f49836427b45241946",
}
# Triage labels are evidence classifications, not proof of unique scientific
# minimality. Only ledger-counted M-TC/M-OI source-facing mappings use that label.
ROLES = {
    "UEOT.V3.Compression.OccupationLimitInvariance.p_goa_01_via_occupationLimit": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.OccupationLimitInvariance.feller_invariant_of_occupation_tendsto": "COUNTED_GENERATOR_FAMILY_SUPPORT_LEMMA",
    "UEOT.V3.Compression.OccupationLimitInvariance.p_per_02_via_occupationLimit": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.processInterface_approx_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.processInterface_exact_source_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.dynamicsCrossScale_approx_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.dynamicsCrossScale_exact_via_factor": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.p_dyn_03_via_multiplicative_chain": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.ValueAlignment.p_ali_02_core_via_mva": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ValueAlignment.p_ali_02_via_mva": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ContractiveFixedPoint.bellman_valueError_le_residual_via_mcf": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ContractiveFixedPoint.bellman_fixedPoint_unique_via_mcf": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.flip_physical_seed_cannot_select_two_programs": "SAME_NO_GO_INTERFACE_ALIAS",
}
CANONICAL_TV_HELPER = "UEOT.V3.InformationPacking.tvDist_symm"
DUPLICATED_TV_HELPER = "UEOT.V3.StatisticalDefect.tvDist_symm"


CLONE_SHA256 = "e369d3eee8fe5383532bf68c18ed08ec961d9710b4d600da3edc11a243ebc064"
LEDGER = REPO / "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"
LEDGER_SHA256 = "621da1e3c2a9b87aab0a07ca0624fe192fe15cc9bcd1c5aa6f5e669526a4d948"



def read_csv(path: Path) -> list[dict]:
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def _parse_data() -> dict:
    modules = read_csv(AUDIT / "EVERY_FILE_633_DETAILED_METRICS.csv")
    declarations = read_csv(AUDIT / "EVERY_DECLARATION_5553_COMPACT.csv")
    proof_rows = read_csv(AUDIT / "all_3793_theorem_direct_reuse_graph.csv")
    groups = json.loads((AUDIT / "ALL_binder_normalized_equal_type_clusters.json").read_text())
    near = json.loads((AUDIT / "NEAR_TYPE_15_DISTINCT_HEURISTIC_PAIRS.json").read_text())
    clones = json.loads((HERE / "CLONE_CANDIDATES_68.json").read_text())
    if (len(modules), len(declarations), len(proof_rows), len(groups), len(near), len(clones)) != (
        633, 5553, 3793, 37, 15, 68
    ):
        raise RuntimeError("AUDIT_ROW_COUNT_MISMATCH")
    graph = {}
    incoming: dict[str, list[str]] = {}
    for row in proof_rows:
        name = row["name"]
        if name in graph:
            raise RuntimeError("DUPLICATED_THEOREM_NAME: " + name)
        graph[name] = row
        for dep in json.loads(row["source_theorem_deps_json"]):
            incoming.setdefault(dep, []).append(name)
    duplicate_members: dict[str, dict] = {}
    for group in groups:
        for entry in group["group_member_declarations"]:
            name = entry["name"]
            if name in duplicate_members:
                raise RuntimeError("OVERLAPPING_DUPLICATE_TYPE_GROUP: " + name)
            duplicate_members[name] = group
    if len(duplicate_members) != 77:
        raise RuntimeError("AUDIT_TYPE_GROUP_MEMBER_COUNT_MISMATCH")
    return {
        "modules": modules, "declarations": declarations, "graph": graph,
        "incoming": incoming, "groups": groups, "duplicates": duplicate_members,
        "near": near, "clones": clones
    }


def verify_evidence_files():
    if sha256(LEDGER.read_bytes()).hexdigest() != LEDGER_SHA256:
        raise RuntimeError("CANONICAL_COMPRESSION_LEDGER_CHANGED_RECLASSIFY_FIRST")
    if sha256((HERE / "CLONE_CANDIDATES_68.json").read_bytes()).hexdigest() != CLONE_SHA256:
        raise RuntimeError("AUDIT_CLONE_EVIDENCE_DRIFT")
    for name, expected in EVIDENCE_SHA.items():
        actual = sha256((AUDIT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"AUDIT_EVIDENCE_DRIFT: {name}: {actual} != {expected}")


def verify_sources(modules: list[dict]):
    mismatches = []
    for row in modules:
        p = REPO / row["path"]
        if not p.is_file():
            mismatches.append({"path": row["path"], "reason": "MISSING"})
        elif sha256(p.read_bytes()).hexdigest() != row["content_sha256"]:
            mismatches.append({"path": row["path"], "reason": "SOURCE_CHANGED"})
    if mismatches:
        raise RuntimeError("STALE_AUDIT_SOURCE: "+json.dumps(mismatches[:12]))
    return len(modules)


def load(*, verify_source=True):
    verify_evidence_files()
    data = _parse_data()
    if verify_source:
        verify_sources(data["modules"])
    return data


def role(name: str):
    if name == DUPLICATED_TV_HELPER:
        return "LOW_RISK_DUPLICATE_HELPER_IMPLEMENTATION"
    if name == CANONICAL_TV_HELPER:
        return "PREFERRED_TV_HELPER_IMPLEMENTATION"
    return ROLES.get(name, "NO_TRIAGE_CLASSIFICATION")


def explain(data: dict, name: str) -> dict:
    row = data["graph"].get(name)
    if not row:
        raise RuntimeError(
            "UNKNOWN_PUBLIC_SOURCE_THEOREM: no exact fully-qualified match; "
            "use FKRG v1 find/show and confirm in Lean"
        )
    group = data["duplicates"].get(name)
    peers = []
    direct_group_edges = []
    if group:
        peers = [x for x in group["group_member_declarations"] if x["name"] != name]
        direct_group_edges = group["verified_direct_proof_dep_edges"]
    dependents = data["incoming"].get(name, [])
    near = [x for x in data["near"] if name in (x["a"], x["b"])]
    return {
        "symbol": name, "origin": row["source_origin"],
        "file": row["path"], "line": int(row["line"]),
        "role": role(name),
        "direct_existing_source_theorem_uses": json.loads(row["source_theorem_deps_json"]),
        "direct_source_theorem_user_count": len(dependents),
        "direct_source_theorem_users": sorted(dependents)[:50],
        "type_relation": "LEANTYPE_DEF_EQ_VERIFIED_SNAPSHOT_40_PAIRS" if group else "NO_TYPE_EQUIVALENCE_CERTIFICATE",
        "definitionally_equal_type_peers": peers,
        "equal_type_group_direct_proof_edges": direct_group_edges,
        "near_type_heuristic_candidates_not_defeq": [
            {"other": x["b"] if x["a"] == name else x["a"],
             "score": x["score"]} for x in near
        ],
        "caution": "Lean type identity is a 40/40 pinned compilation result; "
                   "API relevance, hypotheses of unrelated results and "
                   "scientific independence require additional review."
    }


def search(data: dict, query: str, limit: int):
    parts = [x.lower() for x in re.findall(r"[A-Za-z0-9_]+", query) if len(x) > 1]
    if not parts:
        raise RuntimeError("EMPTY_SEARCH_QUERY")
    scores = []
    for name, row in data["graph"].items():
        hay = (name + " " + row["path"]).lower()
        base = name.rsplit(".", 1)[-1].lower()
        score = sum((12 if part == base else 5 if part in base else 2 if part in hay else 0)
                    for part in parts)
        if score:
            scores.append((score, name))
    scores.sort(key=lambda item: (-item[0], item[1]))
    return [{"score": score, "symbol": n, "file": data["graph"][n]["path"],
             "role": role(n), "has_equal_type_peers": n in data["duplicates"]}
            for score, n in scores[:limit]]


def clone_candidates(data: dict, threshold: int):
    rows = [x for x in data["clones"] if int(x["equal_nonblank_code_lines"]) >= threshold]
    return {
        "count": len(rows),
        "threshold_nonblank_code_lines": threshold,
        "entries": rows,
        "not_a_proof": "Equal source spans do not imply identical theorem type or safe refactoring"
    }


def status(data: dict):
    return {
        "schema": SCHEMA, "baseline_source_commit": SOURCE_BASELINE,
        "module_source_hashes_verified": len(data["modules"]),
        "bundled_modules": len(data["modules"]),
        "ueot_maintained_modules": sum(row["source_origin"] == "UEOT_MAINTAINED"
                                       for row in data["modules"]),
        "vendor_modules": sum(row["source_origin"] == "VENDORED_ADAPTED_UPSTREAM"
                              for row in data["modules"]),
        "public_source_theorems_with_direct_proof_graph": len(data["graph"]),
        "verified_equal_type_groups": len(data["groups"]),
        "equal_type_statement_names": len(data["duplicates"]),
        "near_type_not_defeq_candidate_pairs": len(data["near"]),
        "crossfile_exact_code_clone_candidates": len(data["clones"]),
        "source_of_truth": "Lean proof kernel, source Git commit, and canonical "
                           "Core/Compression ledgers; this is a derived read-only audit",
        "scientific_closure": "NOT_ESTABLISHED"
    }


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--json", action="store_true", help="machine-readable output")
    sub = cli.add_subparsers(dest="command", required=True)
    sub.add_parser("status")
    p = sub.add_parser("show"); p.add_argument("symbol")
    p = sub.add_parser("search"); p.add_argument("words"); p.add_argument("--limit", type=int, default=15)
    p = sub.add_parser("clones"); p.add_argument("--min-lines", type=int, default=15)
    options = cli.parse_args()
    if options.command == "search" and not (1 <= options.limit <= 100):
        raise RuntimeError("INVALID_SEARCH_LIMIT")
    if options.command == "clones" and options.min_lines < 8:
        raise RuntimeError("CLONE_MIN_LINES_AT_LEAST_8")
    data = load()
    if options.command == "status":
        result = status(data)
    elif options.command == "show":
        result = explain(data, options.symbol)
    elif options.command == "search":
        result = search(data, options.words, options.limit)
    else:
        result = clone_candidates(data, options.min_lines)
    if options.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    elif options.command == "search":
        for item in result:
            print(f"{item['score']:2d} {item['symbol']} "
                  f"[{item['role']}] {item['file']}")
        print(f"MATCHES {len(result)}: SOURCE_DISCOVERY_NOT_PROOF_EQUIVALENCE")
    elif options.command == "clones":
        for row in result["entries"]:
            print(f"{row['equal_nonblank_code_lines']} code lines"
                  f" {row['file_a']}:{row['start_line_a']}"
                  f" <-> {row['file_b']}:{row['start_line_b']}")
        print(f"CLONES {result['count']}: NOT_PROOF_EQUIVALENCE")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print("FKRG_REUSE_ERROR", exc, file=sys.stderr)
        sys.exit(2)
