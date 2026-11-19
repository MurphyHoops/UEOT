"""Minimal-field reference seed, exact finite-rank stress and response coefficients.

The static seed is on the auxiliary S^3 preparation geometry, not the physical
contracting finite sphere. No dynamically renormalized absolute stress or
finite-hbar backreaction error is claimed. Run --check to reproduce the receipt.
"""
import argparse
import hashlib
import importlib.util
import inspect
import json
import math
from pathlib import Path
import sys

import numpy as np
import sympy as sp
from mpmath import iv
from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
TIMELIKE = HERE.parents[1]
sys.path.insert(0, str(TIMELIKE / "instrument"))
_spec = importlib.util.spec_from_file_location(
    "_ueot_reference_instrument", TIMELIKE / "instrument" / "instrument.py")
reference = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(reference)


def outward(x):
    """Enclose arbitrary-precision interval endpoints in binary64."""
    return [math.nextafter(float(x.a), -math.inf),
            math.nextafter(float(x.b), math.inf)]


def interval_seed(last=1024):
    """A rigorous positive-binomial tail, not a cutoff convergence estimate."""
    iv.dps = 70
    one = iv.mpf(1)
    pi2 = iv.pi ** 2
    # k=1 is the archived Gaussian zero mode, zeta=1, not a k=0 vacuum.
    residual = one / 8
    for k in range(2, last + 1):
        k = iv.mpf(k)
        residual += k*k*iv.sqrt(k*k-1) - k**3 + k/2 + one/(8*k)
    # For k>=2: -[16 k^3(1-k^-2)]^-1 <= r_k <= -[16 k^3]^-1.
    # Integral comparison bounds sum_{k>N} k^-3 between 1/(2(N+1)^2)
    # and 1/(2N^2).
    tail_lo = -one/(32*last**2)/(1-one/(last+1)**2)
    tail_hi = -one/(32*(last+1)**2)
    tail = iv.mpf([tail_lo.a, tail_hi.b])
    a4 = iv.mpf(9)
    # Anderson-Eaker (1999), Eq. (12), K=1, m=xi=0, mu=1.
    logterm = iv.log(iv.mpf(3)/4) + 2*iv.euler
    rho_an = (-iv.mpf(3)/160 - logterm/64)/(pi2*a4)
    rho = (residual+tail)/(4*pi2*a4) + rho_an
    pressure = rho/3 + one/(12*pi2*a4) + one/(96*pi2*a4)
    effective = (rho+3*pressure)/2
    trace = -rho+3*pressure
    # Known conformal static seed is an independent normalization check.
    conformal = one/(480*pi2*a4)
    conformal_zeta = iv.mpf(1)/120/(4*pi2*a4)
    assert max(abs(v) for v in outward(conformal-conformal_zeta)) < 1e-65
    # The finite seed is scheme dependent; its scale derivative is fixed.
    scale_derivative = -one/(32*pi2*a4)
    assert outward(rho)[1] < 0 < outward(pressure)[0]
    assert outward(rho)[1]-outward(rho)[0] < 1.7e-13
    return {
        "background": "auxiliary_static_S3_only",
        "a_squared": 3,
        "last_mode": last,
        "zero_mode_zeta": 1,
        "renormalization": "Anderson_Eaker_1999_Eq12_mu1_no_extra_finite_terms",
        "finite_residual_sum_plus_certified_tail": outward(residual+tail),
        "tail_interval": outward(tail),
        "rho_analytic_correction": outward(rho_an),
        "rho": outward(rho),
        "pressure": outward(pressure),
        "effective_SEC": outward(effective),
        "trace_minus_plus_plus_plus": outward(trace),
        "rho_zero_mode_before_state_independent_subtractions":
            outward(one/(8*pi2*a4)),
        "conformal_vacuum_rho_normalization_check": outward(conformal),
        "d_rho_d_log_mu": outward(scale_derivative),
        "physical_sphere_absolute_stress_certified": False,
    }


def symbolic_checks():
    z, hs, qs, q1, q2, q3 = sp.symbols("z hs qs q1 q2 q3")
    W = 1/z + qs*z/2 - (qs*qs+q2)*z**3/8
    Wprime = q1*z/2 - (2*qs*q1+q3)*z**3/8
    common = hs*Wprime/(2*W**2)+Wprime**2/(8*W**3)
    Ew = W/2+(1/z**2+hs*hs-1)/(2*W)+common
    Pw = W/2+(-1/(3*z**2)+hs*hs+sp.Rational(1,3))/(2*W)+common
    Eexpected = 1/z+(hs*hs-1)*z/2+(qs*qs-2*(hs*hs-1)*qs+2*hs*q1)*z**3/8
    Pexpected = (1/(3*z)+(qs/3+hs*hs/2+sp.Rational(1,6))*z
                 +(-qs*qs/8-q2/12-(3*hs*hs+1)*qs/12+hs*q1/4)*z**3)
    assert sp.simplify(sp.series(Ew,z,0,4).removeO()-Eexpected) == 0
    assert sp.simplify(sp.series(Pw,z,0,4).removeO()-Pexpected) == 0
    eta = sp.symbols("eta", real=True)
    h = sp.Function("h")(eta)
    q = -1-sp.diff(h,eta)-h*h
    E1 = (h*h-1)/2
    P1 = q/3+h*h/2+sp.Rational(1,6)
    E3 = (q*q-2*(h*h-1)*q+2*h*sp.diff(q,eta))/8
    P3 = (-q*q/8-sp.diff(q,eta,2)/12
          -(3*h*h+1)*q/12+h*sp.diff(q,eta)/4)
    assert sp.simplify(sp.diff(E1,eta)+h*(-E1+3*P1)) == 0
    assert sp.simplify(sp.diff(E3,eta)+h*(-E3+3*P3)) == 0

    a = sp.sqrt(3*sp.cos(2*eta))
    hh = sp.diff(a,eta)/a
    qq = -1-sp.diff(a,eta,2)/a
    assert sp.trigsimp(qq-1/sp.cos(2*eta)**2) == 0
    F = sp.sqrt(3)*sp.sin(2*eta)/2
    assert sp.trigsimp(sp.diff(F,eta,2)+2*hh*sp.diff(F,eta)+8*F) == 0
    c = sp.cos(2*eta)
    rho = 1/c-c/2
    pressure = sp.Rational(5,6)*c-1/(3*c)
    assert sp.trigsimp((sp.diff(F,eta)**2+8*F**2)/(2*a*a)-rho) == 0
    assert sp.trigsimp((sp.diff(F,eta)**2-8*F**2/3)/(2*a*a)-pressure) == 0
    assert sp.trigsimp(sp.diff(rho,eta)+3*hh*(rho+pressure)) == 0
    assert sp.simplify((rho+3*pressure)/2-c) == 0
    assert sp.simplify(sp.zeta(-3)-sp.Rational(1,120)) == 0

    # Minimal zero-mode energy and uncertainty, using precisely the archived data.
    a0 = sp.sqrt(3)
    zeta = sp.symbols("zeta", positive=True)
    qvar = 1/(2*a0*a0*zeta)
    pvar = a0*a0*zeta/2
    assert sp.simplify(qvar*pvar-sp.Rational(1,4)) == 0
    rho0 = a0*a0*zeta/(8*sp.pi**2*a**6)
    assert sp.simplify(sp.diff(rho0,eta)+6*hh*rho0) == 0
    return {
        "minimal_mode_potential": "k^2+sec(2eta)^2",
        "UV_power_and_log_terms_separately_conserved": True,
        "finite_rank_shell_KG_equation": True,
        "finite_rank_shell_stress_and_conservation": True,
        "zero_mode_canonical_uncertainty_and_stiff_scaling": True,
        "finite_rank_state_difference_UV_tail": "exactly_zero",
    }


def finite_rank_numeric():
    """Independent first-order Hamilton system verifies the exact shell formula."""
    a0 = math.sqrt(3)
    radii = np.array([.99,.97,.94])*a0
    times = np.arccos((radii/a0)**2)/2
    def ode(eta, y):
        a = reference.scale(eta)
        return [y[1]/a**2, -8*a*a*y[0]]
    sol = solve_ivp(ode, (0,float(times[-1])), [0.,3*a0],
                    method="DOP853", t_eval=times, rtol=3e-13, atol=3e-14,
                    max_step=.002)
    assert sol.success
    rows = []
    err = 0.
    for eta,a,(F,p) in zip(times,radii,sol.y.T):
        c = math.cos(2*eta)
        rho = 1/c-c/2
        pressure = 5*c/6-1/(3*c)
        dFdt = p/a**3
        rho_ode = (dFdt*dFdt+8*F*F/a**2)/2
        p_ode = (dFdt*dFdt-8*F*F/(3*a**2))/2
        err = max(err,abs(rho-rho_ode),abs(pressure-p_ode))
        H = -math.sqrt(9/a**6-1/a**2)
        zero_rho = 3/(8*math.pi**2*a**6)
        coefficient = rho/(3*H)
        # Check the derivative of the radius constraint only; this is not a
        # full finite-hbar coupled evolution.
        eps = 1e-8
        constraint = lambda e: -math.sqrt(H*H+(2/3)*e*rho)
        fd = (constraint(eps)-constraint(-eps))/(2*eps)
        assert abs(fd-coefficient) < 3e-8
        rows.append({
            "radius_fraction": float(a/a0),
            "radius": float(a), "eta_on_classical_background": float(eta),
            "H_classical": H, "shell_delta_rho_per_epsilon": rho,
            "shell_delta_pressure_per_epsilon": pressure,
            "shell_delta_effective_SEC_per_epsilon": c,
            "shell_delta_H_coefficient_of_hbar_epsilon": coefficient,
            "zero_mode_delta_rho_per_delta_zeta": zero_rho,
            "zero_mode_delta_H_coefficient_of_hbar_delta_zeta":
                zero_rho/(3*H),
        })
    assert err < 4e-12
    return {
        "independent_ODE_max_stress_error": err,
        "rows": rows,
        "same_physical_radius_derivative_only": True,
        "finite_hbar_remainder_certified": False,
        "full_nonlinear_semiclassical_solution": False,
    }


def reference_identity():
    src = inspect.getsource(reference.state_scale)
    assert reference.state_scale(-1/8) == math.sqrt(3)
    assert reference.state_scale(-1/4) == math.sqrt(3)
    assert reference.state_scale(-1/16) == reference.scale(-1/16)
    assert reference.state_scale(0) == math.sqrt(3)
    # The instrument's k=1 data: p=-i*a0/sqrt(2); its frequency is zero.
    a0 = math.sqrt(3)
    u = 1/(a0*math.sqrt(2))
    p = -1j*a0/math.sqrt(2)
    assert abs(-2*(u.conjugate()*p).imag-1) < 1e-15
    return {
        "canonical_source": "physics/qm/null_source/timelike/instrument/instrument.py",
        "state_scale_function_sha256": hashlib.sha256(src.encode()).hexdigest(),
        "instrument_file_sha256": hashlib.sha256((TIMELIKE/"instrument"/"instrument.py").read_bytes()).hexdigest(),
        "static_until_eta": -1/8,
        "physical_scale_from_eta": -1/16,
        "zero_mode_is_regular_Gaussian_not_static_vacuum": True,
        "nonzero_mode_static_frequency": "sqrt(k^2-1), k>=2",
        "different_valid_reference_in_quantum_README":
            "static <= -1/2, physical >= -1/4; not this absolute seed",
    }


def result():
    return {
        "baseline": "a3ae75078ae903163bf0759fbd302e836aeeea84",
        "claim": "minimal_reference_seed_and_exact_relative_source_response",
        "reference": reference_identity(),
        "symbolic": symbolic_checks(),
        "static_absolute_seed": interval_seed(),
        "finite_rank_response": finite_rank_numeric(),
        "sources": [
            "https://arxiv.org/pdf/gr-qc/9906055",
            "https://arxiv.org/pdf/gr-qc/0512118",
        ],
        "remaining_open": [
            "controlled_dynamic_UV_remainder_after_reference_interpolation",
            "absolute_minimal_stress_on_the_physical_finite_sphere",
            "full_self_consistent_feedback_with_finite_error",
            "global_semiclassical_initial_constraints_and_instrument_stress",
        ],
    }


def compare(a,b,path="root"):
    if isinstance(b,dict):
        assert a.keys()==b.keys(), path
        for k in b:
            compare(a[k],b[k],path+"."+k)
    elif isinstance(b,list):
        assert len(a)==len(b), path
        for j,(x,y) in enumerate(zip(a,b)):
            compare(x,y,path+f"[{j}]")
    elif isinstance(b,(str,bool)) or b is None:
        assert a==b, (path,a,b)
    else:
        assert math.isclose(a,b,rel_tol=2e-12,abs_tol=5e-13),(path,a,b)


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Verification requires assertions; do not use python -O.")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    report=result()
    if args.write:
        (HERE/"result.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
    if args.check:
        compare(report,json.loads((HERE/"result.json").read_text()))
        print("PASS: same reference; rigorous static minimal seed; exact finite-rank stress; first-order radius response. Dynamic absolute stress remains OPEN.")
    else:
        print(json.dumps(report,ensure_ascii=False,indent=2))
