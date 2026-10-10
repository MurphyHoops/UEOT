#!/usr/bin/env python3
"""Compile-only, non-destructive witness that fourteen typed terminal results
can be derived from an already existing theorem, under pinned source imports.

This intentionally proves no scientific originality, generator adequacy or safe
deletion property. Generated sources stay OUTSIDE the Git repository.
"""
import csv
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

AUDIT_DIR = Path(__file__).resolve().parent
CORE = AUDIT_DIR.parents[5]  # this is resolved below using known UEOT directory
for parent in AUDIT_DIR.parents:
    if (parent / "lakefile.lean").is_file() and (parent / "UEOT" / "V3").is_dir():
        CORE = parent
        break
else:
    raise RuntimeError("No UEOT Lean workspace found")

METRICS = {}
with (AUDIT_DIR / "EVERY_FILE_633_DETAILED_METRICS.csv").open() as stream:
    for row in csv.DictReader(stream):
        METRICS[row["path"]] = row["content_sha256"]

# Each typed goal is text-identical to the original source declaration's
# theorem statement. ONLY the proof body is replaced in a generated /tmp file.
# The original Lean module, its status ledger and the 106-theorem registry
# remain untouched throughout the test.
CASES = {
    "StatisticalDefect.lean": {
        "imports": ["UEOT.V3.InformationPacking"],
        "theorems": [
            ("tvDist_symm", "UEOT.V3.InformationPacking.tvDist_symm μ ν",
             "/-- Perturbing")],
    },
    "Compression/OccupationLimitInvariance.lean": {
        "imports": [],
        "theorems": [
            ("p_goa_01_via_occupationLimit",
             "UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP μ0",
             "end FiniteCesaro"),
            ("feller_invariant_of_occupation_tendsto",
             "UEOT.V3.PersistenceOccupation.FellerOccupationSystem.invariant_of_occupation_tendsto S Tseq hTseq ν hconv",
             "/-- Full P-PER"),
            ("p_per_02_via_occupationLimit",
             "UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02 S hTight Tseq hTseq",
             "end FellerOccupation"),
        ],
    },
    "Compression/TransportCertificate.lean": {
        "imports": ["UEOT.V3.DynamicsCrossScale"],
        "theorems": [
            ("processInterface_approx_via_twoStage",
             "UEOT.V3.ProcessInterface.p_api_01_approx AB BC PA PB PC hPA hPB hPC εAB εBC hAB hBC",
             "/--"),
            ("processInterface_exact_source_via_twoStage",
             "UEOT.V3.ProcessInterface.p_api_01_exact AB BC PA PB PC hAB hBC",
             "open UEOT.V3.TransportDefect"),
            ("dynamicsCrossScale_approx_via_twoStage",
             "UEOT.V3.DynamicsCrossScale.p_dyn_04_cross_scale_tv P Ps Pr fs fr c hfs hfr hc hcomp hP hPs hPr εs εr hs hr",
             "/-- Exact P-DYN"),
            ("dynamicsCrossScale_exact_via_factor",
             "UEOT.V3.DynamicsCrossScale.p_dyn_04_exact_intertwining P Ps Pr fs fr c hfs hc hcomp hs hr",
             "end UEOT.V3.Compression.TransportCertificate"),
        ],
    },
    "Compression/TransportPathError.lean": {
        "imports": [],
        "theorems": [
            ("p_dyn_03_via_multiplicative_chain",
             "UEOT.V3.PathError.p_dyn_03_finite_path_error p₀ K L ε hε0 hε1 hTV",
             "end UEOT.V3.Compression.TransportCertificate")],
    },
    "Compression/ValueAlignment.lean": {
        "imports": [],
        "theorems": [
            ("p_ali_02_core_via_mva",
             "UEOT.V3.AlignmentParentValue.p_ali_02_core alpha g e halpha",
             "/-- Exact source-facing"),
            ("p_ali_02_via_mva",
             "UEOT.V3.AlignmentParentValue.p_ali_02 alpha JP Ji a t g childGrad halpha hJP hJi ha",
             "end ParentSum")],
    },
    "Compression/ContractiveFixedPoint.lean": {
        "imports": [],
        "theorems": [
            ("bellman_valueError_le_residual_via_mcf",
             "M.valueError_le_residual v",
             "/-- Bellman fixed-point"),
            ("bellman_fixedPoint_unique_via_mcf",
             "M.fixedPoint_unique hv",
             "/-- Explicit geometric")],
    },
    "Compression/TheoryCompletion/UnifiedClosure/FiniteFormationBoundary.lean": {
        "imports": ["UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ProgramPurposeInformationBoundary"],
        "theorems": [
            ("flip_physical_seed_cannot_select_two_programs",
             "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_physical_seed_program_reconstruction_no_go",
             "end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure")],
    },
}

def run():
    rec = {
        "base": "original Lean source modules as fingerprinted in full-library scan at main 48b582beabec2ebae61ab0d51081b83356fcb3e1",
        "scope": "direct terminal theorem reuse in disposable sources only; not scientific independent-generation proof",
        "file_count": len(CASES),
        "candidate_theorem_count": sum(len(case["theorems"]) for case in CASES.values()),
        "results": [],
    }
    with tempfile.TemporaryDirectory(prefix="ueot-reuse-14-") as tempdir:
        tmp = Path(tempdir)
        for filename, case in CASES.items():
            original = CORE / "UEOT" / "V3" / filename
            blob = original.read_bytes()
            tracked_path = "formalization/ueot-core/UEOT/V3/" + filename
            expected = METRICS[tracked_path]
            current_sha = hashlib.sha256(blob).hexdigest()
            if current_sha != expected:
                raise RuntimeError(f"STALE_SCAN_SOURCE: {tracked_path}: {current_sha} != {expected}")
            code = blob.decode("utf-8")
            for imported in case["imports"]:
                code = f"import {imported}\n" + code
            for name, target, endpoint in case["theorems"]:
                pattern = (
                    r"(^theorem " + re.escape(name) + r"\b[\s\S]*?:=)"
                    + r"[\s\S]*?(?=^\s*" + re.escape(endpoint) + r")"
                )
                hits = list(re.finditer(pattern, code, re.MULTILINE))
                if len(hits) != 1:
                    raise RuntimeError(f"DECL_PARSE_FAILED: {filename} {name}: {len(hits)} matches")
                found = hits[0]
                preserved_header = found.group(1)
                new_body = " by\n  exact " + target + "\n\n"
                code = code[:found.start()] + preserved_header + new_body + code[found.end():]
            sample = tmp / filename.replace("/", "__")
            sample.write_text(code, encoding="utf-8")
            check = subprocess.run(
                ["lake", "lean", str(sample)],
                cwd=CORE, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=150)
            errors = [line for line in check.stdout.splitlines() if "error:" in line][:8]
            row = {
                "source": tracked_path,
                "source_sha256": current_sha,
                "replaced_theorems": [name for name, _, _ in case["theorems"]],
                "added_imports": case["imports"],
                "original_source_lines": len(blob.decode("utf-8").splitlines()),
                "disposable_source_lines": len(code.splitlines()),
                "lake_lean_exit": check.returncode,
                "compiler_errors": errors,
            }
            rec["results"].append(row)
            print("PROBE", filename, "THEOREMS", len(case["theorems"]),
                  "EXIT", check.returncode, "ERRORS", errors, flush=True)
            if check.returncode != 0:
                raise RuntimeError(f"REUSE_PROBE_COMPILE_FAILED: {filename}: {errors}")
    if len(rec["results"]) != 7 or rec["candidate_theorem_count"] != 14:
        raise RuntimeError("CENSUS_MISMATCH")
    if any(row["lake_lean_exit"] != 0 for row in rec["results"]):
        raise RuntimeError("NOT_ALL_LEAN_PROBES_PASSED")
    receipt = AUDIT_DIR / "FOCUSED_14_REUSE_PROBE_RECEIPT.json"
    receipt.write_text(json.dumps(rec, ensure_ascii=False, indent=2) + "\n")
    print("ALL_14_REUSE_PROBES_COMPILED", "7_FILES", "RECEIPT", receipt)

if __name__ == "__main__":
    run()
