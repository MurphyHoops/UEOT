"""Master deterministic verification runner for physics/unification."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

SUITES = [
    ("quantum_selection", HERE / "quantum_selection/verify_selection.py", HERE / "quantum_selection/result.json"),
    ("local_control_ctp", HERE / "local_control_ctp/verify_control_ctp.py", HERE / "local_control_ctp/result.json"),
    ("matter_gauge_flavor", HERE / "matter_gauge_flavor/verify_matter_flavor.py", HERE / "matter_gauge_flavor/result.json"),
    ("cosmology_perturbation", HERE / "cosmology_perturbation/verify_perturbation_holdout.py", HERE / "cosmology_perturbation/result.json"),
    ("rg_eft_bridge", HERE / "rg_eft_bridge/verify_rg_eft.py", HERE / "rg_eft_bridge/result.json"),
    ("thermodynamics_memory", HERE / "thermodynamics_memory/verify_thermo_memory.py", HERE / "thermodynamics_memory/result.json"),
    ("spacetime_gravity_bounds", HERE / "spacetime_gravity_bounds/verify_spacetime_gravity.py", HERE / "spacetime_gravity_bounds/result.json"),
    ("topological_index_spectrum", HERE / "topological_index_spectrum/verify_topo_index.py", HERE / "topological_index_spectrum/result.json"),
    ("flavor_spam_identifiability", HERE / "flavor_spam_identifiability/verify_flavor_spam.py", HERE / "flavor_spam_identifiability/result.json"),
    ("superselection_born_contextuality", HERE / "superselection_born_contextuality/verify_superselection_born.py", HERE / "superselection_born_contextuality/result.json"),
    ("micro_gaussian_tail_galerkin", HERE / "micro_gaussian_tail_galerkin/verify_gaussian_tail.py", HERE / "micro_gaussian_tail_galerkin/result.json"),
    ("spin_statistics_qed", HERE / "spin_statistics_qed/verify_spin_qed.py", HERE / "spin_statistics_qed/result.json"),
    ("electroweak_neutrino_seesaw", HERE / "electroweak_neutrino_seesaw/verify_ew_seesaw.py", HERE / "electroweak_neutrino_seesaw/result.json"),
    ("dimension_inflation_dm_qg", HERE / "dimension_inflation_dm_qg/verify_dim_cosmo_qg.py", HERE / "dimension_inflation_dm_qg/result.json"),
    ("pi_phi_god_goa_gates", HERE / "pi_phi_god_goa_gates/verify_piphi_goa.py", HERE / "pi_phi_god_goa_gates/result.json"),
    ("lieb_robinson_lightcone", HERE / "lieb_robinson_lightcone/verify_lieb_robinson.py", HERE / "lieb_robinson_lightcone/result.json"),
    ("gpt_self_dual_reconstruction", HERE / "gpt_self_dual_reconstruction/verify_gpt_reconstruction.py", HERE / "gpt_self_dual_reconstruction/result.json"),
    ("clock_uv_renormalization", HERE / "clock_uv_renormalization/verify_clock_uv.py", HERE / "clock_uv_renormalization/result.json"),
]


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="Check against committed result.json files without rewriting")
    ap.add_argument("--output", type=Path, default=HERE / "verification.json")
    args = ap.parse_args()

    env = os.environ.copy()
    env.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1")

    rows = []
    for name, script, result_json in SUITES:
        cmd = [sys.executable, "-B", str(script)]
        if args.check:
            cmd.append("--check")
        t0 = time.monotonic()
        proc = subprocess.run(cmd, cwd=REPO, env=env, capture_output=True, text=True, timeout=180)
        dur = round(time.monotonic() - t0, 3)
        if proc.returncode != 0:
            sys.stderr.write(f"FAIL [{name}]:\n{proc.stdout}\n{proc.stderr}\n")
            return 1
        cert = json.loads(result_json.read_bytes())
        assert cert.get("status") == "PASS" and cert.get("physical_unification") == "OPEN"
        assert cert.get("source_sha256") == sha256_bytes(script.read_bytes())
        rows.append({
            "suite": name,
            "script": script.relative_to(REPO).as_posix(),
            "script_sha256": sha256_bytes(script.read_bytes()),
            "certificate": result_json.relative_to(REPO).as_posix(),
            "certificate_sha256": sha256_bytes(result_json.read_bytes()),
            "duration_seconds": dur,
            "status": "PASS",
        })
        print(proc.stdout.strip(), flush=True)

    dep_check = REPO / "formalization/ueot-physics-unification/scripts/check_dependencies.py"
    proc_dep = subprocess.run([sys.executable, "-B", str(dep_check)], cwd=REPO, env=env, capture_output=True, text=True)
    if proc_dep.returncode != 0:
        sys.stderr.write(proc_dep.stdout + proc_dep.stderr)
        return 1
    print(proc_dep.stdout.strip(), flush=True)

    receipt = {
        "schema": "ueot-physics-unification-verification/1",
        "status": "PASS",
        "checked_mode": bool(args.check),
        "suites": rows,
        "lean_formalization_package": "formalization/ueot-physics-unification",
        "lean_modules": [
            "UEOTPhysicsUnification.RealQuotientSelection",
            "UEOTPhysicsUnification.CorrelatedBathIdentifiability",
            "UEOTPhysicsUnification.GaugeFlavorSelection",
            "UEOTPhysicsUnification.ConformalControlGravityGates",
            "UEOTPhysicsUnification.RGBridgeAndEFTMatching",
            "UEOTPhysicsUnification.ThermodynamicsAndLandauerBounds",
            "UEOTPhysicsUnification.SpacetimeEquivalenceAndGravityBounds",
            "UEOTPhysicsUnification.TopologicalCarrierAndIndex",
            "UEOTPhysicsUnification.FlavorCyclicAndSPAMContract",
            "UEOTPhysicsUnification.QuantumSuperselectionAndBorn",
            "UEOTPhysicsUnification.CorrelatedGaussianTailAndGalerkin",
            "UEOTPhysicsUnification.SymplecticSpinStatisticsAndQED",
            "UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw",
            "UEOTPhysicsUnification.SpacetimeDimensionAndEarlyLateCosmology",
            "UEOTPhysicsUnification.ActionSelectionAndAttractorRates",
            "UEOTPhysicsUnification.CoreTransportToLiebRobinsonCone",
            "UEOTPhysicsUnification.GPTSelfDualConeReconstruction",
            "UEOTPhysicsUnification.RenormalizedClockContinuum",
        ],
        "physical_unification": "OPEN",
        "rendezvous_compatibility": {
            "pr_468_disjoint_paths": True,
            "frozen_predecessor_qm_files_untouched": True,
        },
    }
    if not args.check or not args.output.is_file():
        args.output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
    else:
        committed = json.loads(args.output.read_text())
        for s_old, s_new in zip(committed["suites"], receipt["suites"]):
            for key in ("suite", "script", "script_sha256", "certificate", "certificate_sha256", "status"):
                assert s_old[key] == s_new[key], f"Drift in {s_new['suite']}.{key}"
    print(f"PASS: all {len(rows)} physics/unification suites verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
