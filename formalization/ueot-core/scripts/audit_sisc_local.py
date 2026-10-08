#!/usr/bin/env python3
"""SISC local-only exact-head reproducibility gate. Never pushes or rewrites data."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
CORE = ROOT / "formalization/ueot-core"
EVIDENCE = CORE / "docs/compression/theory_completion/scientific_closure/evidence"
RAW = EVIDENCE / "c7_sisc_sqlite_method_v1"
BASE = "f744194dabdbb8632e69b1d9cbc1f0e347877571"
BRANCH = "research/sisc-local-20261008"


def require(ok, message):
    """Security-relevant checks must also run under `python -O`."""
    if not ok:
        raise RuntimeError(message)


def run(args, cwd=ROOT, output=False):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode != 0:
        print("FAILED:", " ".join(args), file=sys.stderr)
        print((result.stdout + result.stderr)[-6000:], file=sys.stderr)
        raise SystemExit(result.returncode)
    if output:
        print((result.stdout + result.stderr).strip()[-500:])
    return result.stdout


def main():
    require(run(["git", "branch", "--show-current"]).strip() == BRANCH, "wrong branch")
    require(run(["git", "rev-parse", "main"]).strip() == BASE, "main moved")
    require(run(["git", "merge-base", "main", "HEAD"]).strip() == BASE, "base changed")
    require(run(["git", "rev-parse", "origin/main"]).strip() == BASE, "origin/main changed")
    require(not run(["git", "status", "--porcelain=v1", "-uno"]).strip(),
            "tracked edits present")
    require(not run(["git", "diff", "--check", "main...HEAD"]).strip(), "diff check failed")

    subjects = run(["git", "log", "--reverse", "--format=%s", "main..HEAD"]).splitlines()
    expected = ["sisc(si-0):", "sisc(si-1):", "sisc(si-2):", "sisc(si-3):",
                "sisc(si-4):", "sisc(c5):", "sisc(c6):", "sisc(c7-a):",
                "sisc(c7-b):", "sisc(local-gate):"]
    require(len(subjects) >= len(expected), "missing initial ten stage commits")
    require(all(x.startswith(y) for x, y in zip(subjects, expected)),
            "initial ten stage commits not preserved")
    extras = subjects[len(expected):]
    allowed_extra = {
        "audit-v2", "bridge-v2", "c7-review-v2", "protocol-v2", "path-v2", "gate-v2", "gate-v2-fix",
        "future-core", "global-inventory", "finite-validation", "gate-v3",
        "n1-descent", "stoch-kernel", "n1-observable", "n1-reconcile",
        "stoch-trace-nogo", "n1-robust", "linear-lift", "n1-belief", "stoch-rank-test", "gate-v4",
        "emission-timing", "gate-v5",
    }
    extra_stages = []
    for subject in extras:
        match = re.fullmatch(r"sisc\(([a-z0-9-]+)\): [^\n]+", subject)
        require(match is not None, "unexpected non-SISC appended commit")
        extra_stages.append(match.group(1))
    require(set(extra_stages) <= allowed_extra, "unexpected SISC stage label")
    require(len(extra_stages) == len(set(extra_stages)), "duplicate audit stage")

    paths = run(["git", "diff", "--name-only", "main...HEAD"]).splitlines()
    allowed_root = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure.lean"
    allowed_src = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISC"
    allowed_docs = "formalization/ueot-core/docs/compression/theory_completion/scientific_closure/"
    allowed_audit = "formalization/ueot-core/scripts/audit_sisc_local.py"
    allowed_inventory = "formalization/ueot-core/scripts/audit_sisc_global_inventory.py"
    require(bool(paths), "no changed paths")
    require(all(p == allowed_root or p.startswith(allowed_src) or
                p.startswith(allowed_docs) or p in {allowed_audit, allowed_inventory}
                for p in paths),
            "path outside additive SISC scope")
    print(f"PASS: frozen main, {len(subjects)} additive local commits, clean tracked state")

    print("VERIFY: exact-head lake build UEOT")
    build = run(["lake", "build", "UEOT"], cwd=CORE)
    require("Build completed successfully" in build, "Lean reported no successful build")
    print("PASS:", [line for line in build.splitlines() if "Build completed" in line][-1])

    names = [
        "response_cannot_identify_sameObject_semantics",
        "certified_unique_successor_of_witness",
        "noisy_admissible_successor_unique",
        "finite_mechanism_derives_directed_coverage",
        "finite_mechanism_to_fbt_continuation",
        "finite_directed_history_with_bound",
        "reject_exact_common_twoD_from_same_jacobian",
        "resource_mechanism_alone_does_not_select_objective",
        "finite_mechanism_unique_formed_successor",
        "finite_channel_formed_history_with_realization_bound",
        "zero_formation_error_does_not_identify_parent",
        "empty_protocol_forms_every_candidate",
        "formed_has_nonnegative_budget",
        "formation_path_budget_closed_form",
        "accumulated_error_uniform_of_contraction",
        "contracted_finite_mechanism_realization_bound",
        "futureResponse_inputFiberCompatible",
        "unique_canonical_future_update",
        "recursive_summary_predicts_all_futures",
        "canonical_future_minimal_among_recursive_summaries",
        "exact_future_summary_unique_up_to_relabeling",
        "instant_observation_can_hide_future_difference",
        "complete_future_response_can_merge_distinct_tokens",
        "chosenWord_separates_different_future",
        "finite_probes_identify_canonical_future_classes",
        "finite_complete_probe_card_le",
        "stable_iff_unique_stochastic_descent",
        "stable_quotient_transition_nonnegative",
        "strong_lumpability_iff_existsUnique_stochastic_quotient",
        "massIntoClass_sum_one",
        "test_spanning_forces_controlled_lumpability",
        "measured_tests_unique_markov_quotient",
        "equal_observed_tests_do_not_force_stability",
        "model_strongLumpability_iff_stable",
        "reconciliation_both_unique_quotients",
        "approx_block_mass_from_tests",
        "robust_class_mass_from_approx_observable_tests",
        "all_future_trace_equivalence_not_markov_lumpable",
        "all_future_trace_quotient_kernel_does_not_exist",
        "controlled_trace_span_shift_invariant",
        "controlled_trace_span_finrank_le_card",
        "trace_noGo_but_belief_filter_well_defined",
        "lifted_belief_update_conflict_iff_zero",
        "one_word_trace_is_pre_transition_observation",
        "point_belief_observes_post_transition",
        "pre_and_post_emission_are_not_interchangeable",
    ]
    ns = "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC."
    with tempfile.TemporaryDirectory(prefix="sisc-axioms-") as scratch:
        source = Path(scratch) / "Audit.lean"
        source.write_text("import UEOT\n" + "".join(
            "#print axioms " + ns + name + "\n" for name in names))
        axioms = run(["lake", "env", "lean", str(source)], cwd=CORE)
        require(axioms.count("depends on axioms") +
                axioms.count("does not depend on any axioms") == len(names),
                "axiom result count mismatch")
        require("sorryAx" not in axioms and "unknown constant" not in axioms,
                "proof escape or unknown constant")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for bracket in re.findall(r"depends on axioms: \[([^]]*)\]", axioms):
            require(set(s.strip() for s in bracket.split(",")) <= allowed,
                    "non-standard axiom in proof surface")
    print("PASS: all selected axiom surfaces, standard Lean axioms only")

    # Scan each *new* source file as well as representative terminal theorems.
    # A plain-text check is intentionally conservative and complements kernel
    # axiom checks (it never substitutes for them).
    # Require a Lean token boundary, not merely a regex word boundary.
    # Example: a prose comment line beginning `axiom.` is NOT `axiom foo`.
    proof_escape = re.compile(r"^[ \t]*(sorry|admit|axiom|opaque)(?:[ \t]+|$)", re.MULTILINE)
    require(proof_escape.search("axiom. An explanatory sentence") is None,
            "scanner must not flag a prose token followed by punctuation")
    require(proof_escape.search("theorem t := by\n  sorry\n") is not None,
            "scanner must detect explicit Lean proof escape")
    new_sources = [ROOT / path for path in paths if path.startswith(allowed_src)
                   and path.endswith(".lean")]
    for path in new_sources:
        require(proof_escape.search(path.read_text()) is None,
                f"prohibited proof declaration in {path}")
    print(f"PASS: no prohibited proof declarations in {len(new_sources)} new Lean modules")

    print("VERIFY: all first-party Lean files hashed, imported and source-inventoried")
    first_inventory = CORE / "docs/compression/theory_completion/scientific_closure/SISC_GLOBAL_LEAN_INVENTORY_V1.json"
    previous_inventory = CORE / "docs/compression/theory_completion/scientific_closure/SISC_GLOBAL_LEAN_INVENTORY_V2.json"
    full_inventory = CORE / "docs/compression/theory_completion/scientific_closure/SISC_GLOBAL_LEAN_INVENTORY_V3.json"
    previous = full_inventory.read_bytes()
    run([sys.executable, str(CORE / "scripts/audit_sisc_global_inventory.py")], output=True)
    require(full_inventory.read_bytes() == previous, "global Lean source inventory drift")
    inventory = json.loads(previous)
    require(inventory["total_files"] == 584, "new first-party source inventory unexpectedly changed")
    require(inventory["reachable_from_public_root"] == 582,
            "new public root source reachability unexpectedly small")
    require(not inventory["missing_local_ueot_imports"] and not inventory["import_cycles"],
            "broken internal module graph")
    old_inventory = json.loads(first_inventory.read_bytes())
    require(old_inventory["total_files"] == 574,
            "historic V1 inventory modified")
    for name, old_source in old_inventory["modules"].items():
        if name == "UEOT.V3.Compression.TheoryCompletion.ScientificClosure":
            continue  # public root legitimately acquires additive imports
        require(name in inventory["modules"] and
                inventory["modules"][name]["sha256"] == old_source["sha256"],
                "previously audited first-party Lean source changed: " + name)
    v2_inventory = json.loads(previous_inventory.read_bytes())
    require(v2_inventory["total_files"] == 583, "historic V2 inventory modified")
    for name, v2_source in v2_inventory["modules"].items():
        if name == "UEOT.V3.Compression.TheoryCompletion.ScientificClosure":
            continue
        require(name in inventory["modules"] and
                inventory["modules"][name]["sha256"] == v2_source["sha256"],
                "previous V2 first-party Lean source changed: " + name)

    print("VERIFY: deterministic exhaustive finite predictive quotient benchmark")
    run([sys.executable, str(EVIDENCE / "sisc_finite_future_refinement_benchmark.py")], output=True)
    print("VERIFY: six-state exact-rational stochastic trace/rank cross-check")
    run([sys.executable, str(EVIDENCE / "sisc_stochastic_predictive_rank_test.py")], output=True)

    manifest = json.loads((RAW / "manifest.json").read_text())
    require(hashlib.sha256((RAW / "events.jsonl").read_bytes()).hexdigest() ==
            manifest["raw_sha256"], "C7 manifest does not match raw archive")
    print("VERIFY: C7 frozen evidence and mutation regression")
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_verify.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_negative_tests.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_review_v2.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_review_v2_tests.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_si3_finite_channel_benchmark.py")])

    print("VERIFY: three existing compression / finalization governance regressions")
    for script in ("test_validate_compression_research.py", "test_validate_compression.py",
                   "test_validate_finalization_receipt.py"):
        run([sys.executable, str(CORE / "scripts" / script)], output=True)

    print("LOCAL_GATE_PASS; NO_REMOTE_ACTION; SCIENTIFIC_C7_EXTERNAL_AND_INDEPENDENT_GATES_OPEN")


if __name__ == "__main__":
    main()
