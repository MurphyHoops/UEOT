"""Bind the existing two detector implementations to one explicit incoming state.

This verifies preparation identity and analytic mode identities.  It does not
certify the dynamic renormalized stress tensor, a numerical ultraviolet tail,
or any experimental implementation.
"""
from pathlib import Path
import importlib.util
import json
import math
import sys

import numpy as np
import sympy as s

HERE = Path(__file__).resolve().parent
TIMELIKE = HERE.parent
BASELINE = "a3ae75078ae903163bf0759fbd302e836aeeea84"


def import_file(label, path):
    spec = importlib.util.spec_from_file_location(label, path)
    module = importlib.util.module_from_spec(spec)
    old = list(sys.path)
    try:
        sys.path.insert(0, str(path.parent))
        spec.loader.exec_module(module)
    finally:
        sys.path[:] = old
    return module


def smooth_step(x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    exponent = 1 / x - 1 / (1 - x)
    if exponent > 700:
        return 0.0
    if exponent < -700:
        return 1.0
    return 1 / (1 + math.exp(exponent))


def scale_for_state(eta, start=-1/8, stop=-1/16):
    a0 = math.sqrt(3)
    if eta <= start:
        return a0
    target = math.sqrt(3 * math.cos(2 * eta))
    return a0 + (target - a0) * smooth_step((eta-start)/(stop-start))


def verify():
    instrument = import_file("bound_instrument", TIMELIKE / "instrument/instrument.py")
    reference = import_file("bound_reference", TIMELIKE / "identification/reference.py")
    points = np.linspace(-1/8, 1/4, 289)
    first = max(abs(instrument.state_scale(float(t))-scale_for_state(float(t))) for t in points)
    second = max(abs(reference.scale_squared(float(t))-scale_for_state(float(t))**2) for t in points)
    assert first < 5e-15 and second < 8e-15
    # The former quantum discussion allowed a different auxiliary preparation.
    # Its state-independent finite-rank differences remain valid, but it is not
    # the absolute state used for the two numerical detector implementations.
    old_points = np.linspace(-1/2, -1/16, 225)
    old_gap = max(abs(scale_for_state(float(t), -.5, -.25)-scale_for_state(float(t))) for t in old_points)
    assert old_gap > .05
    eta = s.symbols("eta", real=True)
    a = s.sqrt(3*s.cos(2*eta))
    potential = s.trigsimp(-1-s.diff(a,eta,2)/a)
    assert s.trigsimp(potential-1/s.cos(2*eta)**2) == 0
    # k=n+1: spatial eigenvalue k^2-1; v=a u obeys v''+(k^2+sec^2(2eta))v=0.
    qvar, pvar = s.Rational(1,6), s.Rational(3,2)
    assert qvar*pvar == s.Rational(1,4)
    field_qvar = qvar/(2*s.pi**2)
    total_pvar = 2*s.pi**2*pvar
    assert s.simplify(field_qvar*total_pvar-s.Rational(1,4)) == 0
    zero_energy = total_pvar/(8*s.pi**4*a**6)
    assert s.simplify(zero_energy-3/(8*s.pi**2*a**6)) == 0
    result = {
        "scientific_base": BASELINE,
        "reference": "instrument.state_scale and identification.scale_squared",
        "auxiliary_static_past": "eta <= -1/8; a0=sqrt(3)",
        "auxiliary_transition": "-1/8 < eta < -1/16; interpolate a, then square it",
        "physical_patch": "a=sqrt(3 cos(2 eta)); chi+|eta|<asin(1/sqrt(3))",
        "nonzero_modes": "k>=2; omega=sqrt(k*k-1); u=1/(sqrt(3)*sqrt(2 omega)); pi=-i sqrt(3)*sqrt(omega/2)",
        "zero_mode": {"basis": "Y0=1/sqrt(2 pi^2)", "q_variance": "1/6", "canonical_p_variance": "3/2", "field_Q_variance": str(field_qvar), "integrated_P_variance": str(total_pvar), "rho_equals_pressure": "3/(8 pi^2 a^6)"},
        "comparison_max_absolute_error": {"instrument_scale": first, "identification_scale_squared": second},
        "old_alternate_preparation_max_scale_difference": old_gap,
        "mode_equation": "v_k'' + (k^2 + sec(2 eta)^2) v_k = 0",
        "dynamic_absolute_RSET": "OPEN: same-state dynamic sum, local finite terms and certified tail still required",
        "same_radius_nonlinear_feedback": "OPEN",
        "empirical": "NO_NEW_MATCHED_DEVICE_DATA"
    }
    return result


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O; analytic and numerical assertions are required")
    print(json.dumps(verify(), indent=2))
