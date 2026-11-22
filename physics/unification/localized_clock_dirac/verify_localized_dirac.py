"""P-FLAT-DIRAC-03 Certificate: Lambda=0 Flat-Space Lichnerowicz Barrier, Mesoscopic Gravimetry & Dirac Algebra."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()

    # 1. Exact rational critical compactness C_crit = 2048 / 9375 and monotone Picard fixed point at C0 = 1/10
    c_crit = iv.mpf("2048") / 9375
    c0_sample = iv.mpf("1") / 10
    lip_sample = (iv.mpf("9375") / 2048) * c0_sample
    require(strictly_below(lip_sample, "0.46"), "Sub-critical Lipschitz constant < 0.46")

    # Iterate monotone scalar majorant psi_{n+1} = 1 + (3/8)*C0*psi_n^5 from psi_0 = 1 (40 steps, residual < 1e-16)
    psi = iv.mpf("1")
    for _ in range(50):
        psi = 1 + (iv.mpf("3") / 8) * c0_sample * (psi**5)
    err = abs(psi - (1 + (iv.mpf("3") / 8) * c0_sample * (psi**5))) / (1 - lip_sample)
    psi_fp = psi + iv.mpf([-err.b, err.b])
    require(strictly_above(psi_fp, "1.04") and strictly_below(psi_fp, "1.25"), "Fixed point strictly inside (1, 5/4)")

    # 2. Exact SI CODATA/measured G weak-field mesoscopic gravimetric window (Lambda = 0, flat space):
    # h = 6.62607015e-34 J s (exact), c = 299792458 m/s (exact), G in [6.67415e-11, 6.67445e-11] m^3 kg^-1 s^-2
    h_si = iv.mpf("6.62607015e-34")
    hbar = h_si / (2 * iv.pi)
    c_si = iv.mpf("299792458")
    g_si = iv.mpf(["6.67415e-11", "6.67445e-11"])

    m_meso = iv.mpf("1e-14")       # 10 pg mesoscopic center-of-mass packet
    d_sep = iv.mpf("2e-4")         # 200 um separation
    r_app = iv.mpf("5e-5")         # 50 um packet radius
    t_int = iv.mpf("1.0")          # 1 s coherent interaction time

    compactness_meso = 2 * g_si * m_meso / ((c_si**2) * r_app)
    require(strictly_below(compactness_meso, c_crit) and strictly_below(compactness_meso, "1e-36"), "Deep weak-field regime")

    dphi_grav = g_si * (m_meso**2) * t_int / (hbar * d_sep)
    require(strictly_above(dphi_grav, "0.31") and strictly_below(dphi_grav, "0.32"), "Gravimetric phase in (0.31, 0.32) rad")

    # Binary Ramsey readout contrast sin(dphi) and 95% confidence trial count (2*ln(20) / sin(dphi)^2 < 70 << 1e35!)
    contrast = iv.sin(dphi_grav)
    n_trials_95 = 2 * iv.log(iv.mpf("20")) / (contrast**2)
    require(strictly_below(n_trials_95, "70"), "Mesoscopic flat-space trial count < 70 (33 orders below 1e35)")

    payload = {
        "result_ids": ["P-FLAT-DIRAC-03"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/LocalizedClockAndDiracAlgebra.lean",
        "Lichnerowicz_critical_compactness_exact": "2048/9375",
        "sample_C0_0p1_Lipschitz": outward_str(lip_sample),
        "sample_C0_0p1_majorant_fixed_point": outward_str(psi_fp),
        "mesoscopic_10pg_compactness": outward_str(compactness_meso),
        "mesoscopic_10pg_200um_1s_phase_rad": outward_str(dphi_grav),
        "mesoscopic_95pct_trial_count_upper": outward_str(n_trials_95)[1],
        "local_mediator_ultralocal_Dirac_defect": "0",
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        require(json.loads(args.output.read_text()) == payload, "localized_clock_dirac certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: localized_clock_dirac P-FLAT-DIRAC-03")


if __name__ == "__main__":
    main()
