#!/usr/bin/env python3
"""Conditional, finite-window source identification on the declared FLRW source.

No observed/synthetic measurements are generated. The receipt contains analytic
basis functions, quadrature enclosures, rank certificates, error amplification,
and algebraic negative controls. The geometry apparatus is an added contract.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent
TIMELIKE = HERE.parents[1]
mp.mp.dps = 60
mp.iv.dps = 35
IV = mp.iv
WINDOWS = ((mp.mpf(1)/32, mp.mpf(1)/16),
           (mp.mpf(5)/32, mp.mpf(3)/16))
CHOSEN = (1, 2, 3)  # E_1, rho_2, E_2; rho_1 is the held-out relation.
N_CERT = 1024


def row(c, sec=False):
    if sec:
        return [c, 2*c**-3, 12*c**-4-15*c**-6]
    return [c**-1-c/2, c**-3, 4*c**-4-3*c**-6]


def row_derivatives(c, sec=False):
    if sec:
        return ([1, -6*c**-4, -48*c**-5+90*c**-7],
                [0, 24*c**-5, 240*c**-6-630*c**-8])
    return ([-c**-2-mp.mpf("0.5"), -3*c**-4,
             -16*c**-5+18*c**-7],
            [2*c**-3, 12*c**-5, 80*c**-6-126*c**-8])


def q_mp(z, shape):
    if shape == "polynomial":
        return 30*z*z*(1-z)**2
    if not 0 < z < 1:
        return mp.mpf(0)
    # Exactly the instrument.py bump(2*z-1), not exp[-1/(z(1-z))].
    return mp.exp(-1/(4*z*(1-z)))


def numerical_matrix(windows=WINDOWS, shape="smooth"):
    norm = mp.quad(lambda z: q_mp(z, shape), [0, mp.mpf(".5"), 1])
    ans = []
    for lo, hi in windows:
        for sec in (False, True):
            ans.append([
                mp.quad(lambda z: q_mp(z, shape) *
                        row(mp.cos(2*(lo+(hi-lo)*z)), sec)[j],
                        [0, mp.mpf(".5"), 1]) / norm for j in range(3)])
    return mp.matrix(ans)


def iv_exact(x):
    # x here is a terminating dyadic endpoint. Decimal serialization is exact.
    return IV.mpf(str(x))


def abs_upper(x):
    return max(abs(x.a), abs(x.b))


def widened(x, radius):
    return x + IV.mpf([-1, 1])*radius


def bounds(x):
    # Outward binary64 rounding only affects serialization, not the proof.
    return [math.nextafter(float(x.a), -math.inf),
            math.nextafter(float(x.b), math.inf)]


def q_iv(z, shape):
    s = z*(1-z)
    if shape == "polynomial":
        return 30*s*s, 60*s*(1-2*z), 60*((1-2*z)**2-2*s)
    beta = IV.mpf(1)/4
    q = IV.exp(-beta/s)
    a = beta*(1-2*z)/s**2
    ap = -2*beta/s**2 - 2*beta*(1-2*z)**2/s**3
    return q, q*a, q*(a*a+ap)


def certified_matrix(windows=WINDOWS, shape="smooth", n=N_CERT):
    """Composite midpoint with interval second-derivative remainder.

    For smooth bump, the two endpoint cells are bounded by monotonicity of
    q rather than differentiated across its flat endpoint. All other cells
    have outward interval evaluation of (q*row)''. q's normalization is
    independently enclosed by the same rule.
    """
    h = IV.mpf(1)/n
    total = [[IV.mpf(0) for _ in range(3)] for _ in range(2*len(windows))]
    errors = [[IV.mpf(0) for _ in range(3)] for _ in total]
    normal = IV.mpf(0)
    normal_error = IV.mpf(0)
    cells = range(1, n-1) if shape == "smooth" else range(n)
    for i in cells:
        z = IV.mpf([str(mp.mpf(i)/n), str(mp.mpf(i+1)/n)])
        zm = IV.mpf(2*i+1)/(2*n)
        q, qp, qpp = q_iv(z, shape)
        qm = q_iv(zm, shape)[0]
        normal += h*qm
        normal_error += h**3*abs_upper(qpp)/24
        for k, (low, high) in enumerate(windows):
            lo, width = iv_exact(low), iv_exact(high-low)
            arg = 2*(lo+width*z)
            c, cp = IV.cos(arg), -2*width*IV.sin(arg)
            cpp = -4*width**2*c
            cm = IV.cos(2*(lo+width*zm))
            for sec in (False, True):
                target = 2*k+int(sec)
                rs, ds = row(c, sec), row_derivatives(c, sec)
                rsm = row(cm, sec)
                for j in range(3):
                    total[target][j] += h*qm*rsm[j]
                    d2 = qpp*rs[j]+2*qp*ds[0][j]*cp
                    d2 += q*(ds[1][j]*cp**2+ds[0][j]*cpp)
                    errors[target][j] += h**3*abs_upper(d2)/24
    if shape == "smooth":
        # q is increasing on [0,h] and symmetric at 1. Missing-cell integral
        # lies in [0, 2*h*q(h)]; symmetric absolute enclosure is conservative.
        endpoint_mass = 2*h*q_iv(h, shape)[0]
        normal_error += endpoint_mass
        for k, (low, high) in enumerate(windows):
            carg = IV.mpf([str(2*low), str(2*high)])
            c = IV.cos(carg)
            for sec in (False, True):
                for j, value in enumerate(row(c, sec)):
                    errors[2*k+int(sec)][j] += endpoint_mass*abs_upper(value)
    normal = widened(normal, normal_error)
    assert normal.a > 0
    result = [[widened(total[i][j], errors[i][j])/normal
               for j in range(3)] for i in range(len(total))]
    return result, normal


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def inverse3(a):
    determinant = det3(a)
    assert not (determinant.a <= 0 <= determinant.b), "rank not certified"
    cof = []
    for i in range(3):
        cof.append([])
        for j in range(3):
            rr = [r for r in range(3) if r != i]
            cc = [c for c in range(3) if c != j]
            cof[i].append(((-1)**(i+j))*(a[rr[0]][cc[0]]*a[rr[1]][cc[1]]
                           - a[rr[0]][cc[1]]*a[rr[1]][cc[0]]))
    return [[cof[j][i]/determinant for j in range(3)] for i in range(3)]


def as_numpy(m):
    return np.array(m.tolist(), dtype=float)


def column_condition(m):
    return float(np.linalg.cond(m/np.linalg.norm(m, axis=0)))


def design_report(m):
    array = as_numpy(m)
    choices = []
    for omit in range(4):
        ids = [i for i in range(4) if i != omit]
        a = array[ids]
        inverse = np.linalg.inv(a)
        prediction = array[omit]@inverse
        choices.append({
            "omitted_row": omit,
            "used_rows": ids,
            "determinant": float(np.linalg.det(a)),
            "condition_2_column_normalized": column_condition(a),
            "epsilon_weights": inverse[0].tolist(),
            "epsilon_error_gain_l1": float(np.linalg.norm(inverse[0], 1)),
            "all_parameters_inverse_norm_inf": float(np.linalg.norm(inverse, np.inf)),
            "heldout_prediction_weights": prediction.tolist(),
            "heldout_residual_equal_error_gain":
                1+float(np.linalg.norm(prediction, 1)),
        })
    r = array[[0, 2]]
    null = np.r_[1., -np.linalg.solve(r[:, 1:], r[:, 0])]
    fixed_alpha_bias = np.linalg.solve(r[:, :2], r[:, 2])
    return {
        "matrix_row_order": ["rho_1", "E_1", "rho_2", "E_2"],
        "matrix": array.tolist(),
        "condition_2_column_normalized_four_rows": column_condition(array),
        "three_row_options": choices,
        "two_density_rank": int(np.linalg.matrix_rank(r)),
        "two_density_nuisance_determinant": float(np.linalg.det(r[:, 1:])),
        "two_density_null_direction_epsilon_one": null.tolist(),
        "two_density_null_residual": (r@null).tolist(),
        "false_alpha_zero_fit_bias_per_unit_v": fixed_alpha_bias.tolist(),
        "independently_known_u_epsilon_gain":
            float(np.linalg.norm(np.linalg.inv(r[:, [0, 2]])[0], 1)),
    }


def known_stiff_report(matrix, enclosure):
    """Two geometry density windows suffice when the combined stiff term is calibrated."""
    a = as_numpy(matrix)[[0,2]][:,[0,2]]
    inv = np.linalg.inv(a)
    ci = [[enclosure[i][j] for j in (0,2)] for i in (0,2)]
    determinant = ci[0][0]*ci[1][1]-ci[0][1]*ci[1][0]
    assert not determinant.a <= 0 <= determinant.b
    wi = [ci[1][1]/determinant, -ci[0][1]/determinant]
    gain = sum(abs_upper(x) for x in wi)
    stiff_sensitivity = wi[0]*enclosure[0][1]+wi[1]*enclosure[2][1]
    numerical_sensitivity = inv[0] @ as_numpy(matrix)[[0,2],1]
    assert float(gain.b) < 9.354
    return {
        "calibration_contract":"u known exactly; bounded u error adds the recorded sensitivity",
        "coefficient_order":["epsilon","v_6alpha"],
        "rows":["rho_1","rho_2"],
        "matrix":a.tolist(),
        "condition_2_column_normalized":column_condition(a),
        "epsilon_weights":inv[0].tolist(),
        "epsilon_error_gain_l1":float(np.linalg.norm(inv[0],1)),
        "stiff_calibration_error_sensitivity":float(abs(numerical_sensitivity)),
        "determinant_interval":bounds(determinant),
        "epsilon_weight_intervals":[bounds(x) for x in wi],
        "epsilon_equal_row_error_gain_upper":bounds(gain)[1],
        "stiff_calibration_error_sensitivity_upper":bounds(abs_upper(stiff_sensitivity))[1],
        "unit_gap_midpoint_total_row_error_max":
            math.nextafter(0.5/bounds(gain)[1],-math.inf),
    }


def symbolic_checks():
    c = sp.symbols("c", positive=True)
    f, r, h = row(c, False)
    ef, er, eh = row(c, True)
    for value, sec in zip((f, r, h), (ef, er, eh)):
        assert sp.simplify(-value-c*sp.diff(value, c)-sec) == 0
    z, y = h/r, f/r
    wz = sp.factor(sp.diff(z, c)*sp.diff(y, c, 2)
                   - sp.diff(z, c, 2)*sp.diff(y, c))
    assert sp.simplify(wz-40*(c*c-3)*(c*c-sp.Rational(3,4))/c**4) == 0
    zsec, ysec = (4/c-5/c**3), c**4
    wsec = sp.factor(sp.diff(zsec,c)*sp.diff(ysec,c,2)
                    -sp.diff(zsec,c,2)*sp.diff(ysec,c))
    assert sp.simplify(wsec-20*(21-4*c*c)/c**2) == 0
    # Conventional -+++ curvature along the background; dot = d/dtau.
    t = sp.symbols("eta", real=True)
    a = sp.sqrt(3*sp.cos(2*t))
    hp = sp.diff(a,t)/a**2
    curvature = 6*(sp.diff(a,t,2)/a**3+1/a**2)
    rnn = -3*(sp.diff(a,t,2)*a-sp.diff(a,t)**2)/a**4
    dr = sp.diff(curvature,t)/a
    hnn_df = -2*curvature*rnn-6*hp*dr-curvature**2/2
    hnn_ae = (-36*sp.diff(a,t,3)*sp.diff(a,t)/a**6
              +72*sp.diff(a,t,2)*sp.diff(a,t)**2/a**7
              +18*sp.diff(a,t,2)**2/a**6
              +36*sp.diff(a,t)**2/a**6-18/a**4)
    target = 6*(4*sp.cos(2*t)**2-3)/sp.cos(2*t)**6
    for expr in (hnn_df-target, hnn_ae-target):
        assert sp.trigsimp(sp.expand_trig(sp.simplify(expr))) == 0
    trace_ae = -6*(sp.diff(dr,t)/a+3*hp*dr)
    trtarget = -48*(2*sp.cos(2*t)**2-3)/sp.cos(2*t)**6
    assert sp.trigsimp(sp.expand_trig(sp.simplify(trace_ae-trtarget))) == 0
    # Euler and Weyl-squared first variations imply H2=H1/3, H3=H1/3.
    x2,x3 = sp.symbols("x2 x3")
    sol = sp.solve([1-4*x2+x3, x3-2*x2+sp.Rational(1,3)], [x2,x3])
    assert sol == {x2:sp.Rational(1,3),x3:sp.Rational(1,3)}
    return {
        "conservation_three_basis_functions": True,
        "H1_density_AE_and_DF_agree": True,
        "H1_density": "6*(4*c^2-3)/c^6",
        "H1_SEC": "18*(4*c^2-5)/c^6",
        "H1_trace_AE_rho_minus_3p": "-48*(2*c^2-3)/c^6",
        "finite_curvature_effective_coefficients": ["1", "1/3", "1/3"],
        "density_curvature_Wronskian_after_dividing_by_stiff": str(wz),
        "SEC_curvature_Wronskian_after_dividing_by_stiff": str(wsec),
    }


def source_hashes():
    paths = [
        TIMELIKE/"instrument"/"instrument.py",
        TIMELIKE/"continuation"/"SOURCE.md",
        TIMELIKE/"continuation"/"quantum"/"minimal_response.py",
    ]
    return {str(p.relative_to(TIMELIKE)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in paths}


def make_receipt():
    symbolic = symbolic_checks()
    smooth, poly = numerical_matrix(), numerical_matrix(shape="polynomial")
    smooth_report, poly_report = design_report(smooth), design_report(poly)
    enclosure, normal = certified_matrix()
    for i in range(4):
        for j in range(3):
            assert enclosure[i][j].a <= IV.mpf(str(smooth[i,j])) <= enclosure[i][j].b
    a_interval = [enclosure[i] for i in CHOSEN]
    inverse = inverse3(a_interval)
    w = inverse[0]
    gain = sum(abs_upper(x) for x in w)
    heldout = [sum(enclosure[0][k]*inverse[k][j] for k in range(3))
               for j in range(3)]
    heldout_gain = 1+sum(abs_upper(x) for x in heldout)
    determinant = det3(a_interval)
    point = mp.matrix([row(mp.cos(2*(lo+hi)/2), sec)
                       for lo,hi in WINDOWS for sec in (False,True)])
    third_window = ((mp.mpf(7)/32, mp.mpf(1)/4),)
    extra = numerical_matrix(windows=third_window)
    three_density = np.array([as_numpy(smooth)[0], as_numpy(smooth)[2],
                              as_numpy(extra)[0]])
    td_inv = np.linalg.inv(three_density)
    center_mismatch = as_numpy(smooth)-as_numpy(point)
    # The coefficient nuisance may be arbitrarily unknown within the declared
    # finite-order family: setting it to zero creates this algebraic bias.
    assert abs(smooth_report["false_alpha_zero_fit_bias_per_unit_v"][0]) > 1
    assert np.max(np.abs(smooth_report["two_density_null_residual"])) < 1e-12
    assert float(gain.b) < 16
    assert float(heldout_gain.b) < 2.01
    return {
        "schema": 1,
        "status": "conditional_identification_not_experiment",
        "source_sha256": source_hashes(),
        "coefficient_order": ["epsilon_nine_mode",
                              "u_combined_stiff_density_A_over_27",
                              "v_effective_finite_curvature_6alpha"],
        "row_normalization": "rho=(Gnn/2); E=(Rnn/2); 4*pi*G=1; baseline and reference subtracted before averaging",
        "supports_eta_background_labels": [[float(x) for x in p] for p in WINDOWS],
        "new_geometry_contract_required": True,
        "finite_hbar_remainder_bound_proved": False,
        "dynamic_reference_window_error_proved_here": False,
        "symbolic_checks": symbolic,
        "known_stiff_two_density_windows": known_stiff_report(smooth,enclosure),
        "smooth_full_windows": smooth_report,
        "polynomial_full_windows_diagnostic": poly_report,
        "point_centers_diagnostic": design_report(point),
        "point_replacement_matrix_bias": center_mismatch.tolist(),
        "certified_smooth_selected_design": {
            "method": "interval midpoint + second derivative remainder + monotone endpoint-cell enclosure",
            "cells": N_CERT,
            "iv_decimal_digits": IV.dps,
            "normalization_integral_q": bounds(normal),
            "matrix_intervals": [[bounds(x) for x in r] for r in enclosure],
            "selected_rows": list(CHOSEN),
            "selected_determinant": bounds(determinant),
            "epsilon_weight_intervals": [bounds(x) for x in w],
            "epsilon_equal_absolute_error_gain_upper": bounds(gain)[1],
            "heldout_prediction_weight_intervals": [bounds(x) for x in heldout],
            "heldout_residual_equal_error_gain_upper": bounds(heldout_gain)[1],
            "unit_gap_midpoint_classification_total_row_error_max":
                math.nextafter(0.5/bounds(gain)[1], -math.inf),
        },
        "additional_third_density_window": {
            "support": [float(x) for x in third_window[0]],
            "additional_radius_time_trigger_required": True,
            "matrix": three_density.tolist(),
            "condition_2_column_normalized": column_condition(three_density),
            "epsilon_weights": td_inv[0].tolist(),
            "epsilon_error_gain_l1": float(np.linalg.norm(td_inv[0],1)),
        },
        "negative_controls": {
            "two_density_epsilon_direction_hidden_by_nuisances": True,
            "false_alpha_zero_can_create_false_nine_mode_signal": True,
            "point_centers_are_not_full_window_coefficients": True,
            "geometry_does_not_separate_classical_P_squared_and_zero_mode_variance": True,
            "no_old_Ramsey_output_relabelled_as_geometry": True,
        },
    }


def assert_close(actual, recorded, trail="receipt"):
    if isinstance(actual, dict):
        assert isinstance(recorded,dict) and actual.keys()==recorded.keys(), trail
        for key in actual:
            assert_close(actual[key],recorded[key],trail+"."+key)
    elif isinstance(actual,list):
        assert isinstance(recorded,list) and len(actual)==len(recorded), trail
        for i,(a,b) in enumerate(zip(actual,recorded)):
            assert_close(a,b,trail+f"[{i}]")
    elif isinstance(actual,float):
        assert isinstance(recorded,(float,int)) and math.isclose(
            actual,recorded,rel_tol=2e-10,abs_tol=2e-10), (trail,actual,recorded)
    else:
        assert actual==recorded,(trail,actual,recorded)


def main():
    if not __debug__:
        raise RuntimeError("Certificate requires assertions; do not use -O")
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    receipt=make_receipt()
    path=HERE/"receipt.json"
    if args.write:
        path.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n")
    if args.check:
        assert_close(receipt,json.loads(path.read_text()))
    cert=receipt["certified_smooth_selected_design"]
    print(json.dumps({
        "status":receipt["status"], "check_passed":args.check,
        "selected_determinant":cert["selected_determinant"],
        "known_stiff_epsilon_gain_upper":receipt["known_stiff_two_density_windows"]["epsilon_equal_row_error_gain_upper"],
        "uncalibrated_stiff_epsilon_gain_upper":cert["epsilon_equal_absolute_error_gain_upper"],
        "heldout_residual_gain_upper":cert["heldout_residual_equal_error_gain_upper"],
        "receipt":str(path)},ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
