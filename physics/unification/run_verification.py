"""Master deterministic verification runner for physics/unification."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
AH_RUNNER = REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/run_verification.py"

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
    ("horizon_minimum_scale", HERE / "horizon_minimum_scale/verify_horizon_scale.py", HERE / "horizon_minimum_scale/result.json"),
    ("all_harmonic_elliptic", HERE / "all_harmonic_elliptic/verify_all_harmonic.py", HERE / "all_harmonic_elliptic/result.json"),
    ("localized_clock_dirac", HERE / "localized_clock_dirac/verify_localized_dirac.py", HERE / "localized_clock_dirac/result.json"),
    ("discrete_quantum_geometry", HERE / "discrete_quantum_geometry/verify_discrete_qg.py", HERE / "discrete_quantum_geometry/certificate.json"),
    ("chiral_gauge_overlap_clock", HERE / "chiral_gauge_overlap_clock/verify_chiral_clock.py", HERE / "chiral_gauge_overlap_clock/certificate.json"),
    ("core_dimensionless_constants", HERE / "core_dimensionless_constants/verify_core_constants.py", HERE / "core_dimensionless_constants/certificate.json"),
    ("mesoscopic_decoherence_gravimetry", HERE / "mesoscopic_decoherence_gravimetry/verify_meso_decoherence.py", HERE / "mesoscopic_decoherence_gravimetry/certificate.json"),
    ("math_v42_closed_tests_bridge", HERE / "math_v42_closed_tests_bridge/verify_math_v42_bridge.py", HERE / "math_v42_closed_tests_bridge/certificate.json"),
    ("philosophy_v31_omega_bridge", HERE / "philosophy_v31_omega_bridge/verify_phil_v31_bridge.py", HERE / "philosophy_v31_omega_bridge/certificate.json"),
    ("lorentzian_causal_qg_limit", HERE / "lorentzian_causal_qg_limit/verify_lorentzian_qg_limit.py", HERE / "lorentzian_causal_qg_limit/certificate.json"),
    ("nonabelian_chiral_constructive", HERE / "nonabelian_chiral_constructive/verify_nonabelian_chiral.py", HERE / "nonabelian_chiral_constructive/certificate.json"),
    ("unimodular_vacuum_selection", HERE / "unimodular_vacuum_selection/verify_unimodular_lambda.py", HERE / "unimodular_vacuum_selection/certificate.json"),
    ("unified_causal_chiral_unimodular", HERE / "unified_causal_chiral_unimodular/verify_unified_synthesis.py", HERE / "unified_causal_chiral_unimodular/certificate.json"),
]


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def verify_pr468_all_harmonic_horizon_readonly(env: dict[str, str]) -> dict:
    """Read-only regression check of PR #468's 345-entry all_harmonic_horizon chain."""
    spec = importlib.util.spec_from_file_location("_ueot_ah_readonly", AH_RUNNER)
    assert spec is not None and spec.loader is not None
    ah_mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ah_mod)

    reuse = ah_mod.frozen()
    sources = ah_mod.manifest_now()
    committed_ah = json.loads((ah_mod.HERE / "verification.json").read_text())
    assert reuse["entry_count_reused"] == 332
    assert reuse["inherited_scientific_file_count"] == 1231
    assert sources == committed_ah["current_source_manifest"]
    entries = list(ah_mod.ENTRIES)
    assert len(entries) == 13 and entries[-1] == "review"

    def run_entry(entry_name: str) -> tuple[str, int, str]:
        p = subprocess.run(
            [sys.executable, "-B", str(ah_mod.HERE / f"{entry_name}.py"), "--check"],
            cwd=REPO,
            env=env,
            capture_output=True,
            text=True,
            timeout=180,
        )
        return entry_name, p.returncode, p.stdout + p.stderr

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(run_entry, entries))
    for entry_name, rc, out in results:
        if rc != 0:
            raise RuntimeError(f"FAIL [all_harmonic_horizon/{entry_name}]:\n{out}")

    assert ah_mod.frozen() == reuse, "PR #468 inherited null_source files mutated during check"
    assert ah_mod.manifest_now() == sources, "PR #468 all_harmonic_horizon/ROUTES files mutated during check"
    print(
        f"PASS: pr468_all_harmonic_horizon read-only regression "
        f"({reuse['entry_count_reused']} reused + {len(entries)} executed = "
        f"{reuse['entry_count_reused'] + len(entries)} entries, {len(sources)} cohort/route files byte-identical)",
        flush=True,
    )
    return {
        "cohort": "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon",
        "entry_count_reused": reuse["entry_count_reused"],
        "executed_cohort_entries": len(entries),
        "total_chain_entries": reuse["entry_count_reused"] + len(entries),
        "inherited_scientific_file_count": reuse["inherited_scientific_file_count"],
        "cohort_manifest_file_count": len(sources),
        "entries": entries,
        "readonly_byte_identical": True,
        "status": "PASS",
    }


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
        proc = subprocess.run(cmd, cwd=REPO, env=env, capture_output=True, text=True, timeout=300)
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

    pr468_reg = verify_pr468_all_harmonic_horizon_readonly(env)

    receipt = {
        "schema": "ueot-physics-unification-verification/1",
        "status": "PASS",
        "checked_mode": bool(args.check),
        "suites": rows,
        "pr468_all_harmonic_horizon_regression": pr468_reg,
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
            "UEOTPhysicsUnification.OperationalHorizonMinimumScale",
            "UEOTPhysicsUnification.AllHarmonicConstraintEllipticity",
            "UEOTPhysicsUnification.LocalizedClockAndDiracAlgebra",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt",
            "UEOTPhysicsUnification.ChiralGaugeOverlapClockBridge",
            "UEOTPhysicsUnification.CoreUnitGaugeAndDimensionlessConstants",
            "UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry",
            "UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge",
            "UEOTPhysicsUnification.PhilosophyV31OmegaObserverBridge",
            "UEOTPhysicsUnification.LorentzianCausalQuantumGravityLimit",
            "UEOTPhysicsUnification.NonAbelianChiralConstructiveBoundary",
            "UEOTPhysicsUnification.UnimodularVacuumConstantSelection",
            "UEOTPhysicsUnification.UnifiedCausalChiralUnimodularSynthesis",
        ],
        "physical_unification": "OPEN",
        "rendezvous_compatibility": {
            "pr_468_disjoint_paths": True,
            "frozen_predecessor_qm_files_untouched": True,
            "pr_468_345_entry_chain_verified_readonly": True,
        },
    }
    if not args.check or not args.output.is_file():
        args.output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
    else:
        committed = json.loads(args.output.read_text())
        assert len(committed["suites"]) == len(receipt["suites"]), "Suite count drift in verification.json"
        for s_old, s_new in zip(committed["suites"], receipt["suites"]):
            for key in ("suite", "script", "script_sha256", "certificate", "certificate_sha256", "status"):
                assert s_old[key] == s_new[key], f"Drift in {s_new['suite']}.{key}"
        assert committed.get("lean_modules") == receipt["lean_modules"], "Lean module list drift in verification.json"
        assert (
            committed.get("pr468_all_harmonic_horizon_regression") == receipt["pr468_all_harmonic_horizon_regression"]
        ), "PR #468 regression metadata drift in verification.json"
    print(f"PASS: all {len(rows)} physics/unification suites + 345-entry PR #468 regression verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
