#!/usr/bin/env python3
"""Exact TT Weyl/Bach algebra on closed FLRW; no ODE or numerical cutoff."""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sympy as s

BASE = "c57e2f411e58dc1dae60de8f3c97fbd680e46d8b"
HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / ".git").exists())
OLD = tuple("physics/qm/null_source/timelike/operational_response/" + n
            for n in ("CONTRACT.md", "review.py", "review.json")) + (
    "physics/qm/null_source/timelike/compatibility/CONTRACT.md",
    "physics/qm/null_source/timelike/evolution/stress/README.md",
    "physics/qm/null_source/timelike/continuation/quantum/README.md")

def require(ok, label):
    if not ok:
        raise AssertionError(label)

def zero(expr):
    return s.expand(expr) == 0

def sha(data):
    return hashlib.sha256(data).hexdigest()

def frozen_inputs():
    out = {}
    for rel in OLD:
        archived = subprocess.run(["git", "show", BASE + ":" + rel],
            cwd=ROOT, check=True, capture_output=True).stdout
        current = (ROOT / rel).read_bytes()
        require(current == archived, "frozen predecessor changed: " + rel)
        out[rel] = sha(current)
    for name in ("check.py", "README.md"):
        p = HERE / name
        out[p.relative_to(ROOT).as_posix()] = sha(p.read_bytes())
    return out

def delta(i, j):
    return int(i == j)

def eps(i, j, k):
    p = (i, j, k)
    if len(set(p)) < 3:
        return 0
    return (-1) ** sum(p[a] > p[b] for a in range(3) for b in range(a+1, 3))

def riemann(e, a, c, d):
    return delta(e, c)*delta(a, d) - delta(e, d)*delta(a, c)

def matrix_basis():
    mats = []
    for i in range(3):
        for j in range(i, 3):
            m = [[0]*3 for _ in range(3)]
            m[i][j] = m[j][i] = 1
            mats.append(m)
    return mats

def tracefree_basis():
    out = [[[1,0,0],[0,-1,0],[0,0,0]],
           [[1,0,0],[0,0,0],[0,0,-1]]]
    for i, j in ((0,1), (0,2), (1,2)):
        m = [[0]*3 for _ in range(3)]
        m[i][j] = m[j][i] = 1
        out.append(m)
    return out

def weyl_from_electric_magnetic(E, B):
    C = {}
    def put(a,b,c,d,v):
        for key, value in (((a,b,c,d),v), ((b,a,c,d),-v),
                           ((a,b,d,c),-v), ((b,a,d,c),v),
                           ((c,d,a,b),v), ((d,c,a,b),-v),
                           ((c,d,b,a),-v), ((d,c,b,a),v)):
            require(key not in C or C[key] == value, "Weyl pair symmetry")
            C[key] = value
    for i,j in itertools.product(range(3), repeat=2):
        put(0,i+1,0,j+1,E[i][j])
    for i,j,k in itertools.product(range(3), repeat=3):
        put(0,i+1,j+1,k+1,-sum(eps(j,k,m)*B[m][i] for m in range(3)))
    for i,k,j,l in itertools.product(range(3), repeat=4):
        put(i+1,k+1,j+1,l+1,
            delta(i,j)*E[k][l] + delta(k,l)*E[i][j]
            - delta(i,l)*E[k][j] - delta(k,j)*E[i][l])
    return lambda a,b,c,d: C.get((a,b,c,d), 0)

def calculate():
    require(__debug__, "Scientific assertions must remain enabled")
    for X in matrix_basis():
        tr = sum(X[i][i] for i in range(3))
        for i,j in itertools.product(range(3), repeat=2):
            comm = -sum(riemann(e,k,k,i)*X[e][j]
                        + riemann(e,j,k,i)*X[k][e]
                        for k,e in itertools.product(range(3), repeat=2))
            require(comm == 3*X[i][j]-delta(i,j)*tr,
                    "[D^k,D_i] X_kj = 3 X_ij - gamma_ij tr X")
    for i,k,m,n in itertools.product(range(3), repeat=4):
        require(sum(eps(i,k,l)*eps(l,m,n) for l in range(3))
                == delta(i,m)*delta(k,n)-delta(i,n)*delta(k,m),
                "curl contraction")
    # Basis and pair sums also check all quadratic cross terms by polarization.
    basis = tracefree_basis()
    matrices = [[[0]*3 for _ in range(3)]] + basis
    matrices += [[[U[i][j]+V[i][j] for j in range(3)] for i in range(3)]
                 for U,V in itertools.combinations(basis,2)]
    signs = (-1,1,1,1)
    for E,B in itertools.product(matrices, repeat=2):
        C = weyl_from_electric_magnetic(E,B)
        for a,b,c,d in itertools.product(range(4), repeat=4):
            require(C(a,b,c,d)+C(a,c,d,b)+C(a,d,b,c) == 0,
                    "algebraic Bianchi identity")
        for b,d in itertools.product(range(4), repeat=2):
            require(sum(signs[a]*C(a,b,a,d) for a in range(4)) == 0,
                    "Weyl trace")
        norm = sum(signs[a]*signs[b]*signs[c]*signs[d]*C(a,b,c,d)**2
                   for a,b,c,d in itertools.product(range(4), repeat=4))
        require(norm == 8*sum(E[i][j]**2-B[i][j]**2
                             for i,j in itertools.product(range(3), repeat=2)),
                "Lorentzian C squared = 8(E squared - B squared)")
    x,d,k,ell = s.symbols("x d k ell")
    A = -d + 2*k
    electric = -(x+d-2*k)/4
    double_divergence = x*electric + (d-3*k)*x + (d-3*k)*electric
    HC = 4*double_divergence + 4*k*electric
    W = (x-d+2*k)**2 + 4*k*x
    require(zero(HC+W), "direct double-divergence Bach operator")
    from_action = (x-A)**2 + 4*x*(A+k)
    require(zero(from_action-W), "independent electric/magnetic action operator")
    spectral = W.subs(d, -k*(ell*(ell+2)-2))
    require(zero(spectral-(x+k*ell**2)*(x+k*(ell+2)**2)),
            "all-l exact spectral factorization")
    require(zero(HC.subs(k,0)+(x-d)**2), "prescribed flat sign")
    require(zero(W.subs({k:1,d:-6})-(x*x+20*x+64)), "l=2 coefficient")
    euclidean_continued = (-x+d)**2-4*k*(-2*x+d)+4*k*k
    require(zero(euclidean_continued-W), "Euclidean/Lorentzian sign cross-check")
    t, S, P = s.symbols("t S P", real=True)
    u,v = s.Function("u")(t),s.Function("v")(t)
    def op(f):
        return s.diff(f,t,4)+2*S*s.diff(f,t,2)+P*f
    boundary = (u*s.diff(v,t,3)-s.diff(u,t)*s.diff(v,t,2)
        + s.diff(u,t,2)*s.diff(v,t)-s.diff(u,t,3)*v
        + 2*S*(u*s.diff(v,t)-s.diff(u,t)*v))
    require(zero(s.diff(boundary,t)-u*op(v)+op(u)*v), "fourth-order Green boundary")
    delta_lagrangian = s.diff(u,t,2)*s.diff(v,t,2)-2*S*s.diff(u,t)*s.diff(v,t)+P*u*v
    action_boundary = s.diff(v,t)*s.diff(u,t,2)-v*(s.diff(u,t,3)+2*S*s.diff(u,t))
    require(zero(delta_lagrangian-v*op(u)-s.diff(action_boundary,t)),
            "quadratic-action variational boundary")
    aa,mm = s.Function("a")(t),s.Function("m")(t)
    weighted = aa**2*(mm*(s.diff(u,t,2)+2*s.diff(aa,t)/aa*s.diff(u,t)+P*u)
                        + s.diff(mm,t)*s.diff(u,t))
    require(zero(weighted-s.diff(aa**2*mm*s.diff(u,t),t)-aa**2*mm*P*u),
            "weighted second-order divergence form")
    hubble = s.diff(aa,t)/aa
    scalar_R = 6*(s.diff(aa,t,2)/aa**3 + 1/aa**2)
    rho_HR = (-6*scalar_R*s.diff(hubble,t) + aa**2*scalar_R**2/2
              + 6*hubble*s.diff(scalar_R,t))/aa**2
    rho_AE = (-36*s.diff(aa,t,3)*s.diff(aa,t)/aa**6
              +72*s.diff(aa,t,2)*s.diff(aa,t)**2/aa**7
              +18*s.diff(aa,t,2)**2/aa**6
              +36*s.diff(aa,t)**2/aa**6 -18/aa**4)
    require(s.simplify(rho_HR+rho_AE) == 0, "AE H1 = -HR: general FLRW density")
    cmat,grav,shift,kappa = s.symbols("c_mat gamma_C shift kappa", nonzero=True)
    require(s.cancel((cmat+shift)-(grav+kappa*shift)/kappa-(cmat-grav/kappa)) == 0,
            "net coupling under compensated prescription shift")
    require(s.cancel((cmat+shift)-grav/kappa-(cmat-grav/kappa)) == shift,
            "uncompensated shift changes net coupling")
    v0 = s.cos(2*t)-s.cos(4*t)
    v1 = s.sin(2*t)/2-s.sin(4*t)/4
    def w2(f):
        return s.diff(f,t,4)+20*s.diff(f,t,2)+64*f
    require(s.expand(w2(v0)) == 0 and s.expand(w2(v1)) == 0,
            "extra homogeneous data examples")
    jets0 = [s.diff(v0,t,j).subs(t,0) for j in range(4)]
    jets1 = [s.diff(v1,t,j).subs(t,0) for j in range(4)]
    require(jets0 == [0,0,12,0] and jets1 == [0,0,0,12], "two missing initial data")
    require(W.subs({k:1,d:-6,x:-4}) == 0, "l=2 frequency 2")
    require(((x-d+2*k)**2).subs({k:1,d:-6,x:-4}) == 16,
            "negative control detects missing 4 partial_eta squared")
    return {
        "schema": "ueot-closed-flrw-local-tt-weyl/1",
        "status": "EXACT_GENERAL_TT_WEYL_BACH_OPERATOR_VERIFIED",
        "base_git_commit": BASE,
        "arithmetic": "exact integer/rational symbolic algebra; no ODE, quadrature, or cutoff",
        "convention": "g=a^2(-deta^2+gamma+h), h spatial TT, unit S3, l>=2",
        "HC_definition": "4 nabla^c nabla^d C_acbd + 2 R^cd C_acbd",
        "operator": {
            "covariant": "delta HC_ij = -a^-2 W h_ij",
            "mixed": "delta HC^i_j = -a^-4 W h^i_j",
            "W": "(partial_eta^2-Delta_gamma+2)^2+4 partial_eta^2",
            "spectrum": "W_l=(partial_eta^2+l^2)(partial_eta^2+(l+2)^2)",
            "l2_coefficients_descending_even_derivative": [1,20,64],
            "explicit_c_family": "D_T + (4c/a^2) W; 4piG=1; no change to inherited c_extra=0"
        },
        "checks": {name: "PASS" for name in (
            "sphere_curvature_commutator", "TT_curl_square", "Weyl_norm_and_Bianchi",
            "direct_double_divergence", "independent_quadratic_action",
            "arbitrary_l_factorization", "flat_sign", "curvature_negative_control",
            "Green_boundary", "variational_boundary", "weighted_divergence_form",
            "compensated_net_c", "AE_sign_translation", "extra_initial_data")},
        "initial_data_negative_controls_l2": {
            "cos_2eta_minus_cos_4eta_jets": [int(z) for z in jets0],
            "sin_2eta_over_2_minus_sin_4eta_over_4_jets": [int(z) for z in jets1]},
        "inherited_prescription": {
            "physical_mu": 1, "alpha_AE": 0, "b_extra": 0, "c_extra": 0, "Einstein_z": 1,
            "AE_tensor_relation": "H1_AE=-H_R; b_extra=-alpha_AE",
            "reference_TT_contacts_set_to_zero": False,
            "note": "extra means added to the frozen reference; its fixed local contacts remain to be calculated"},
        "scope": {
            "proved": "complete linear local Weyl/Bach TT operator and its algebraic/variational contracts",
            "not_determined": ["inhomogeneous TT kernel and fixed contact terms of the inherited reference prescription",
                "full overlapping retarded RSET response", "complete semiclassical feedback"],
            "requires_for_fourth_order_evolution": "four TT Cauchy data for the explicit c!=0 parameter family; not extra data imposed on the fixed c_extra=0 point",
            "prior_evidence_modified": False,
            "new_mode_ODE": 0,
            "Core_read_only_GI_excluded": True},
        "input_sha256": frozen_inputs()
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not (args.write or args.check):
        parser.error("use --write and/or --check")
    text = json.dumps(calculate(), ensure_ascii=False, indent=2, sort_keys=True)+"\n"
    target = HERE / "result.json"
    if args.write:
        target.write_text(text, encoding="utf-8")
    if args.check:
        require(target.read_text(encoding="utf-8") == text, "result.json mismatch")
    print("PASS: exact closed-FLRW TT Weyl/Bach operator; archived input bytes unchanged")

if __name__ == "__main__":
    main()
