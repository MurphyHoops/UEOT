"""Exact witnesses and two comparisons to published parameter estimates. Run with python -B."""
import hashlib
from itertools import combinations, combinations_with_replacement, product
import json
import math
from pathlib import Path
import platform
import subprocess

import sympy as s

BASE = "67aa5c4d9a7e77da3f2a74dfb717a711f885cca9"
HERE = Path(__file__).resolve().parent
F = s.Rational


def cone():
    # Build the same 18 spatial displacements; change only first-arrival times.
    points = []
    for i in range(3):
        for sign in (-1, 1):
            x = [0]*3
            x[i] = sign
            points.append(x)
    for i, j in combinations(range(3), 2):
        for a, b in product((-3, 3), (-4, 4)):
            x = [0]*3
            x[i], x[j] = a, b
            points.append(x)

    def design(arrival):
        rows = []
        for x in points:
            ray = [arrival(x), *x]
            rows.append([ray[i]*ray[j]*(1 if i == j else 2)
                         for i,j in combinations_with_replacement(range(4), 2)])
        return s.Matrix(rows)

    round_front = design(lambda x: s.sqrt(sum(a*a for a in x)))
    diamond_front = design(lambda x: sum(abs(a) for a in x))
    expected = s.Matrix([-1,0,0,0,1,0,0,1,0,1])
    assert round_front.nullspace() == [expected]
    pivots = diamond_front.T.rref()[1]
    assert len(pivots) == 10
    witness = diamond_front[list(pivots), :]
    inv = witness.inv()
    inv_norm = max(sum(abs(v) for v in inv.row(i)) for i in range(10))
    timing_error = F(1,1000)
    row_error = (28+timing_error)*timing_error
    assert inv_norm*row_error < 1
    metric = s.diag(-1,1,1,1)
    boost = s.eye(4)
    boost[:2,:2] = s.Matrix([[F(5,4),-F(3,4)],[-F(3,4),F(5,4)]])
    assert boost.T*metric*boost == metric
    preferred_frame = s.eye(4)
    preferred_frame[1,0] = -F(3,5)
    ray = preferred_frame*s.Matrix([1,1,0,0])
    wrong_null = (ray.T*metric*ray)[0]
    assert wrong_null == -F(21,25)
    return dict(displacements=len(points), round_rank=round_front.rank(),
                normalized_quadratic_coefficients=list(map(int,expected)),
                diamond_rank=len(pivots), independent_rows_zero_based=list(pivots),
                inverse_infinity_norm=str(inv_norm), arrival_time_error=str(timing_error),
                perturbation_product_upper=str(inv_norm*row_error), boosted_medium_ray_norm=str(wrong_null))


def coupling():
    incoming = s.Matrix([5,3,0,0]), s.Matrix([5,-3,0,0])
    outgoing = s.Matrix([5,0,3,0]), s.Matrix([5,0,-3,0])
    metric = s.diag(-1,1,1,1)
    assert all((p.T*metric*p)[0] == -16 for p in incoming+outgoing)
    da, db = [p-k for p,k in zip(outgoing,incoming)]
    assert da+db == s.zeros(4,1) and da != s.zeros(4,1)
    # Reconstruct the leading pole tensor and contract the actual gauge momentum.
    q = s.Matrix([1,0,0,1])
    def tensor_residual(charges):
        pole = s.zeros(4)
        for initial,final,g in zip(incoming,outgoing,charges):
            for sign,p in [(-1,initial),(1,final)]:
                pole += sign*g*p*p.T / (p.T*metric*q)[0]
        return pole*metric*q
    assert tensor_residual((1,1)) == s.zeros(4,1)
    residual = tensor_residual((2,1))
    assert residual == da and residual[1] != 0  # x-polarized gauge vector is transverse to q
    edges = s.Matrix([[1,-1,0],[0,1,-1]])
    assert edges.nullspace() == [s.ones(3,1)] and len(edges[:1,:].nullspace()) == 2

    earth, ti, pt = F(1,2), F(1,10**12), 0
    a_ti, a_pt = 1+2*earth*ti, 1+2*earth*pt
    eta = 2*(a_ti-a_pt)/(a_ti+a_pt)
    unit = F(1,10**15)
    center, width = -F(15,10)*unit, 3*(F(23,10)+F(15,10))*unit
    assert center-width < 0 < center+width < eta
    return dict(nonuniversal_soft_residual=list(map(int,residual)),
                connected_nullity=1, disconnected_nullity=2, scalar_force_eta=str(eta),
                Ti_Pt_comparison_band=list(map(str,[center-width,center+width])))


def weak_field(baseline):
    alpha, curvature, phi, r, m, gm = s.symbols("alpha R phi r m GM", positive=True)
    action = curvature+alpha*curvature**2
    f_R = s.diff(action,curvature)
    trace = s.expand(f_R*curvature-2*action)
    assert trace == -curvature
    mass2 = 1/(3*s.diff(f_R,curvature))
    # Einstein-frame canonical scalar with reduced Planck mass set to one.
    Fphi = s.exp(s.sqrt(F(2,3))*phi)
    potential = (Fphi-1)**2/(8*alpha*Fphi**2)
    assert s.simplify(s.diff(potential,phi,2).subs(phi,0)-mass2) == 0
    assert mass2.subs(alpha,F(1,6)) == 1 and mass2.subs(alpha,-F(1,6)) == -1
    delta_F = 2*gm*s.exp(-m*r)/(3*r)
    Phi, Psi = -gm/r-delta_F/2, -gm/r+delta_F/2
    def lap(u):
        return s.simplify(s.diff(r*r*s.diff(u,r),r)/r**2)
    assert lap(delta_F) == s.simplify(m*m*delta_F)
    assert lap(2*Psi-delta_F) == 0 and s.simplify(Psi-Phi-delta_F) == 0
    assert s.limit(r*r*s.diff(delta_F,r),r,0) == -2*gm/3
    assert s.limit(r*r*s.diff(2*Psi-delta_F,r),r,0) == 2*gm
    gamma = s.simplify(Psi/Phi)
    long, short = s.limit(gamma,m,0), s.limit(gamma,m,s.oo)
    band = [1+F(21-3*23,10**6), 1+F(21+3*23,10**6)]
    assert long == F(1,2) and short == 1 and long < band[0] < 1 < band[1]
    archived = [baseline["unscreened_constant_slip_long_range_limit"],
                *baseline["Cassini_central_plusminus_3_reported_errors"]]
    ulps = [abs(float(exact)-old)/math.ulp(float(exact))
            for exact,old in zip([long,*band], archived, strict=True)]
    assert max(ulps) <= 1
    return dict(scalar_pole_mass_squared=str(mass2), unscreened_gamma=str(long),
                heavy_scalar_gamma=str(short), archived_display_difference_ulps=ulps, cassini_comparison_band=list(map(str,band)))


def feedback():
    t,x,y,z = coords = s.symbols("t x y z", real=True)
    H,G,N,L = s.symbols("H G N L", positive=True)
    metric = [-1]+[s.exp(2*H*t)]*3
    axes = range(4)
    # Gamma^a_bc and R^a_bcd from the diagonal metric, independent of Euler-density input.
    gamma = {(a,b,c): s.simplify((int(a == c)*s.diff(metric[a],coords[b])
                                  +int(a == b)*s.diff(metric[a],coords[c])
                                  -int(b == c)*s.diff(metric[b],coords[a]))/(2*metric[a]))
             for a,b,c in product(axes,repeat=3)}
    ricci = s.zeros(4)
    riemann_sq = 0
    for a,b,c,d in product(axes,repeat=4):
        component = s.simplify(s.diff(gamma[a,d,b],coords[c])-s.diff(gamma[a,c,b],coords[d])
                       + sum(gamma[a,c,k]*gamma[k,d,b]-gamma[a,d,k]*gamma[k,c,b] for k in axes))
        if a==c:
            ricci[b,d] += component
        riemann_sq += component**2 * metric[a]/(metric[b]*metric[c]*metric[d])
    assert ricci == 3*H**2*s.diag(*metric)
    scalar = sum(ricci[i,i]/metric[i] for i in axes)
    ricci_sq = sum((ricci[i,i]/metric[i])**2 for i in axes)
    euler = s.simplify(riemann_sq-4*ricci_sq+scalar**2)
    anomaly = -N*euler/(5760*s.pi**2)
    assert s.simplify(anomaly-N*(riemann_sq-ricci_sq)/(2880*s.pi**2)) == 0
    rho = -anomaly/4
    assert rho == N*H**4/(960*s.pi**2)
    assert s.simplify(2*scalar*ricci-scalar**2*s.diag(*metric)/2) == s.zeros(4)
    # Independent trace + FLRW continuity construction (scheme with no box R).
    a = s.Function("a")(t)
    h = s.diff(a,t)/a
    C = s.symbols("C")
    beta = N/(960*s.pi**2)
    rho_flrw = beta*h**4 + C/a**4
    trace_flrw = -4*beta*h**2*(h**2+s.diff(h,t))
    p_flrw = (trace_flrw+rho_flrw)/3
    assert s.simplify(s.diff(rho_flrw,t)+3*h*(rho_flrw+p_flrw)) == 0
    # Conserved radiation has nonzero enthalpy on de Sitter and violates the spatial equation.
    enthalpy = s.simplify((rho_flrw+p_flrw).subs(a,s.exp(H*t)).doit())
    assert enthalpy == 4*C*s.exp(-4*H*t)/3

    k = 8*s.pi*G*beta/3
    low = 2*L/(1+s.sqrt(1-4*k*L))
    high = (1+s.sqrt(1-4*k*L))/(2*k)
    for root in (low, high):
        source = rho.subs(H**2,root)
        # 00 and ii/a^2, with Lambda=3L and p=-rho.
        assert s.simplify(3*root-3*L-8*s.pi*G*source) == 0
        assert s.simplify(-3*root+3*L+8*s.pi*G*source) == 0
    assert s.limit(low,G,0,dir='+') == L
    sample = {L:F(1,10**6),G:1,N:1}
    shift = (low/L-1).subs(sample).evalf(25)
    assert 0 < shift < F(1,10**8)
    return dict(curvature_invariants_over_H4=[str(s.simplify(v/H**4)) for v in [riemann_sq,ricci_sq,euler]],
                rho_over_H4=str(beta), radiation_enthalpy=str(enthalpy), classical_x="1/1000000",
                corrected_x=str(low.subs(sample).evalf(25)), relative_curvature_shift=str(shift),
                classical_equation_residual=str((-8*s.pi*G*rho.subs(H**2,L)).subs(sample)),
                discriminant_if_kL_one_third=str(1-4*F(1,3)))


def main():
    if not __debug__:
        raise RuntimeError("Enable assertions for verification")
    ref = "physics/qm/correlated_bath/sectors/geometry-result.json"
    blob = subprocess.check_output(["git","show",f"{BASE}:{ref}"],cwd=HERE)
    results = dict(cone=cone(), coupling=coupling(), weak_field=weak_field(json.loads(blob)), feedback=feedback())
    print(json.dumps(dict(status="PASS", scientific_baseline=BASE, baseline_file=ref,
                          baseline_sha256=hashlib.sha256(blob).hexdigest(),
                          verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          python=platform.python_version(), sympy=s.__version__, results=results),
                     indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
