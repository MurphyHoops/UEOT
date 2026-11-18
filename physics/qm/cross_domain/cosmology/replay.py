"""Replay the fixed background and tracer-growth holdout, offline."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.stats import chi2

HERE = Path(__file__).resolve().parent
C_KMS = 299792.458


def read(name):
    data = (HERE / name).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()


def e(z, m):
    return np.sqrt(m * (1 + z)**3 + 1 - m)


def x(z, m):
    return quad(lambda t: 1 / e(t, m), 0, z, epsabs=1e-13)[0]


def growth_ode(m):
    def rhs(n, y):
        om = m / (m + (1 - m) * np.exp(3*n))
        return [y[1], 1.5*om*y[0] - (2 - 1.5*om)*y[1]]

    ai = 1e-4
    sol = solve_ivp(rhs, (np.log(ai), 0.), [ai, ai], method="DOP853",
                    dense_output=True, rtol=2e-12, atol=1e-15)
    if not sol.success:
        raise RuntimeError(sol.message)
    return lambda a: sol.sol(np.log(a)) / sol.sol(0)[0]


def heath(a, m):
    ea = np.sqrt(m/a**3 + 1 - m)
    # Integral in a form regular at the lower endpoint.
    integral = quad(lambda b: (b/(m+(1-m)*b**3))**1.5, 0, a,
                    epsabs=1e-15, epsrel=2e-13)[0]
    d = 2.5*m*ea*integral
    dn = -1.5*(m/a**3)/ea**2*d + 2.5*m/(a*ea)**2
    return np.array([d, dn])


def interfaces(m):
    grid = np.geomspace(.1, 1, 23)
    ode, eds = growth_ode(m), growth_ode(1.)
    independent = np.array([heath(a, m) / heath(1., m)[0] for a in grid])
    direct = np.array([ode(a) for a in grid])
    np.testing.assert_allclose(direct, independent, rtol=2e-10, atol=1e-12,
                               err_msg="GR dust growth vs independent Heath integral")
    d_eds = np.array([eds(a) for a in grid])
    np.testing.assert_allclose(d_eds.T, np.tile(grid, (2, 1)), rtol=1e-10,
                               err_msg="matter-only growing solution D = D_N = a")
    dz = 1e-5
    z = np.array([.067, .6, 1.48])
    dx = np.array([(x(t+dz,m)-x(t-dz,m))/(2*dz) for t in z])
    np.testing.assert_allclose(dx, 1/e(z,m), rtol=1e-9, err_msg="flat distance derivative")

    # Reconstruct the canonical scalar in units of today's critical density.
    ell = 1-m
    u = np.arcsinh(np.sqrt(ell/m)*grid**1.5)
    phi = 2/np.sqrt(3)*np.log(np.tanh(u/2))  # in reduced Planck units
    v = ell*(1+.5*np.sinh(np.sqrt(3)*phi/2)**2)
    kinetic = m/(2*grid**3)
    np.testing.assert_allclose(kinetic+v, m/grid**3+ell, rtol=1e-13)
    np.testing.assert_allclose(kinetic-v, -ell, atol=1e-12)
    if not np.all(direct > 0):
        raise ValueError("growing solution must have positive amplitude and growth")
    return {"growth_max_abs_ODE_vs_integral": float(np.max(abs(direct-independent))),
            "EdS_max_abs": float(np.max(abs(d_eds.T-grid))),
            "distance_derivative_max_abs":float(max(abs(dx-1/e(z,m)))),
            "scalar_pressure_max_abs":float(max(abs(kinetic-v+ell)))}


def predict(data):
    model = data["candidate"]
    m = model["Omega_m0"]
    if not model["flat"] or m != .30 or model["Omega_Lambda0"] != 1-m:
        raise ValueError("candidate disagrees with the fixed baseline")
    checks = interfaces(m)
    w, low, target = data["WiggleZ"], data["6dFGS"], data["target"]
    z, zl, zt = w["z"], low["z"], target["z"]
    b = (z*x(z,m)**2/e(z,m))**(1/3)
    ode = growth_ode(m)
    gl, gt = (ode(1/(1+t))[1] for t in (zl, zt))
    design = np.array([[x(zt,m)/b, 0.], [1/(e(zt,m)*b), 0.], [0., gt/gl]])
    inputs = np.array([w["DV_times_rd_fid_over_rd_Mpc"]/w["rd_fid_Mpc"], low["fsigma8"]])
    errors = np.array([w["error_Mpc"]/w["rd_fid_Mpc"], low["error"]])
    mf = low["fid_Omega_m0"]
    return {"interface_checks":checks, "calibration":inputs.tolist(), "input_sd":errors.tolist(),
            "scale_and_sigma8":(inputs / [b,gl]).tolist(),
            "scale_and_sigma8_sd":(errors / [b,gl]).tolist(),
            "B_WiggleZ_G_6dF_G_QSO":[b,gl,gt], "transfer":design.tolist(),
            "predicted":(design @ inputs).tolist(), "order":target["ordered_observables"],
            "low_z_AP_true_over_fid_h_units":[x(zl,m)/x(zl,mf), e(zl,mf)/e(zl,m)],
            "sigma8_filter_Mpc":8/model["h_for_sigma8_convention"]}


def score(r, cov):
    return float(r @ np.linalg.solve(cov, r))


def compare(pred, hold, data):
    if pred["order"] != hold["order"] or data["target"]["z"] != hold["z"]:
        raise ValueError("held-out observable order or redshift mismatch")
    mean, measured = np.array(pred["predicted"]), np.array(hold["observed"])
    cov = np.array(hold["covariance"])
    np.testing.assert_array_equal(cov, cov.T)
    np.linalg.cholesky(cov)
    design = np.array(pred["transfer"]) * pred["input_sd"]
    cov0 = cov + design @ design.T
    bound = 3*cov0
    r = measured-mean
    alpha = data["rule"]["alpha"]
    critical = float(chi2.isf(alpha,3))
    q, q0 = score(r,bound), score(r,cov0)
    injection = np.array([0., 0., 10*np.sqrt(bound[2,2])])
    control = score(injection,bound)
    if control <= critical:
        raise AssertionError("10-sigma injection should reject the held-out model")
    bg = score(r[:2], 2*cov0[:2,:2])
    gsd = np.sqrt(cov[2,2])+abs(design[2,1])
    g = (r[2]/gsd)**2
    shape = mean[0]/mean[1]
    v = np.array([1., -shape, 0.])
    fid = hold["fiducial"]
    return {"observed": measured.tolist(), "residual":r.tolist(), "C_target":cov.tolist(),
            "C_residual_assuming_cross_survey_independence":cov0.tolist(),
            "C_residual_upper_bound":bound.tolist(),
            "joint":{"Q":q,"critical":critical,"p_upper_gaussian":chi2.sf(q,3),
                     "reject":q>critical, "variance_only_critical":3/alpha,
                     "variance_only_p_upper": min(1.,3/q) if q else 1.},
            "if_cross_survey_independent":{"Q":q0,"p_gaussian":chi2.sf(q0,3)},
            "sector_Bonferroni":{"background_Q":bg,"critical_bg":chi2.isf(alpha/2,2),
                                 "growth_Q":g,"critical_growth":chi2.isf(alpha/2,1),
                                 "growth_residual_sd_upper":gsd},
            "AP_ruler_free":{"model_DM_over_DH":shape,"observed_DM_over_DH":measured[0]/measured[1],
                             "DM_minus_F_DH":float(v@measured),"sd":np.sqrt(v@cov@v)},
            "QSO_predicted_alpha_perp_parallel":[mean[0]*fid["rd_Mpc"]/fid["DM_Mpc"],
                     mean[1]*fid["rd_Mpc"]*fid["H_km_s_Mpc"]/C_KMS],
            "velocity_bias_ratio_absorbing_growth_residual":measured[2]/mean[2],
            "injection_Q":control}


def verify_archive(actual, reference, path="root"):
    if isinstance(actual, dict):
        if actual.keys() != reference.keys():
            raise AssertionError(f"{path}: receipt field mismatch")
        for key, value in actual.items():
            verify_archive(value, reference[key], f"{path}.{key}")
    elif isinstance(actual, (bool, str)) or (isinstance(actual, list) and isinstance(actual[0], str)):
        if actual != reference:
            raise AssertionError(f"{path}: {actual!r} != {reference!r}")
    else:
        np.testing.assert_allclose(actual, reference, rtol=1e-9, atol=1e-10, err_msg=path)


def review_matter():
    """Independent complex CKM fit to tree coordinates; no import from matter."""
    from scipy.optimize import brentq

    # KLOE, LHCb baryons, Belle BGL, LHCb charged-B Dalitz, respectively.
    t, r, cb, gamma_deg = .2323, .083, .0406, 68.7
    s12, c12 = t/np.hypot(1,t), 1/np.hypot(1,t)
    s13 = r*cb
    c13 = np.sqrt(1-s13**2)
    s23 = cb/c13
    c23 = np.sqrt(1-s23**2)
    r12 = np.array([[c12,s12,0],[-s12,c12,0],[0,0,1]])
    r23 = np.array([[1,0,0],[0,c23,s23],[0,-s23,c23]])

    def matrix(delta):
        ub = s13*np.exp(-1j*delta)
        u13 = np.array([[c13,0,ub],[0,1,0],[-ub.conjugate(),0,c13]])
        return r23 @ u13 @ r12

    def angle(v):
        return np.angle(-v[0,0]*v[0,2].conjugate()/(v[1,0]*v[1,2].conjugate()))

    delta = brentq(lambda d: angle(matrix(d))-np.deg2rad(gamma_deg), .001, 3.14,
                   xtol=1e-15)
    v = matrix(delta)
    np.testing.assert_allclose(v.conj().T@v,np.eye(3),atol=3e-15)
    np.testing.assert_allclose([abs(v[0,1]/v[0,0]),abs(v[0,2]/v[1,2]),abs(v[1,2]),
                                np.rad2deg(angle(v))],[t,r,cb,gamma_deg],rtol=4e-15)
    ratio = abs(v[2,0]/v[2,1])
    frequency_ratio = 5279.58/5366.90*(ratio/1.206)**2
    prediction = frequency_ratio*17.7683
    # The calibration/prediction is now closed. Read the author's receipt for comparison.
    authors = json.loads((HERE.parent/"matter"/"observed.json").read_text())
    for key,value in [("abs_Vtd_over_Vts",ratio),("dm_d",prediction)]:
        lo,hi = authors["prediction"]["0"][key]
        if not lo <= value <= hi:
            raise AssertionError(f"independent {key}={value:.12g} outside [{lo}, {hi}]")

    # Exact counterexample to a per-component interpretation of the 2% rule.
    from fractions import Fraction as F
    lead = 1-F(99,100)
    residual_d, residual_s = F(1,50), F(0)
    factor = abs((lead+residual_d)/(lead+residual_s))
    assert factor == 3 and factor > F(51,49)
    assert abs(residual_d/lead) == 2
    cp = np.array([.0568+.0655j, -.0930-.0125j])  # measured x,y in Eq. (11)
    raw_angle = np.rad2deg(np.angle(cp[1]/cp[0]))/2 % 180
    return {"delta_deg":np.rad2deg(delta), "gamma_deg":np.rad2deg(angle(v)),
            "gamma_from_central_cartesians_only_deg":raw_angle,
            "Vtd_over_Vts":ratio,"Delta_md_over_Delta_ms_predicted":frequency_ratio,
            "Delta_md_predicted_ps_inverse":prediction,
            "Delta_md_over_Delta_ms_measured":.5050/17.7683,
            "conditional_ratio_envelope":[49/51,51/49],
            "counterexample_total_lead":float(lead),"counterexample_residual_over_net":2.,
            "counterexample_frequency_ratio_factor":float(factor)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--predict-only",action="store_true")
    modes.add_argument("--check",action="store_true")
    modes.add_argument("--review-matter",action="store_true",
                       help="independent tree-CKM and destructive-interference check")
    args = parser.parse_args()
    if args.review_matter:
        print(json.dumps(review_matter(), indent=2, allow_nan=False))
        return
    data, sha = read("calibration.json")
    pred = predict(data)
    result = {"calibration_sha256":sha,"prediction":pred}
    if not args.predict_only:
        hold, sha = read("qso_holdout.json")
        result.update(holdout_sha256=sha, score=compare(pred,hold,data))
    if args.check:
        verify_archive(result, read("observed.json")[0])
        print("PASS: interfaces, calibration, held-out covariance, rejection control and archived fields.")
    else:
        print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
