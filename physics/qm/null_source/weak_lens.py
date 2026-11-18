"""Recover two stress couplings from positions and velocities without estimating acceleration."""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json
import math
import sys

import numpy as np
from mpmath import iv
from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
iv.dps = 36
I = iv.mpf
END = Fraction(3, 4)
N = 2048
SCALE = 10**10
SENSOR = Fraction(1, 10**8)  # absolute error per reported determinant, including quantization


def rational(x):
    x = Fraction(x)
    return I(x.numerator) / x.denominator


def multiply(a, b):
    return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(min(len(a), len(b)))]


def diff(a):
    return [(i+1)*v for i, v in enumerate(a[1:])]


def profile(u, order):
    # Taylor coefficients (derivatives divided by factorial), also on interval arguments.
    x = [u, 1] + [0]*(order+1)
    x2 = multiply(x, x)
    den = [1-x2[0], *[-v for v in x2[1:]]]
    inv = [1/den[0]]
    for k in range(1, len(den)):
        inv.append(-sum(den[i]*inv[k-i] for i in range(1,k+1))/den[0])
    f = [iv.exp(1-inv[0])]
    for k in range(1, len(den)):
        f.append(-sum(i*inv[i]*f[k-i] for i in range(1,k+1))/k)
    F = multiply(f, f)
    return x2, f, F


def kernels(u, order):
    x2, f, F = profile(u, order)
    X = multiply(diff(f), diff(f))
    base = [1-rational(16)*x2[0]/9, *[-rational(16)*v/9 for v in x2[1:]]]
    w = multiply(base,multiply(base,base))
    for power in (0, 2, 4):
        if power:
            w = multiply(w,x2)
        wF = multiply(w,F)
        # L=w*(-z''/2+d), M=w*z*f'^2, B=2*w*F*(-z''/2+d)-w*z*F''
        yield ([-v/2 for v in diff(diff(w))], w,
               multiply(w,X), [-(v+y) for v,y in zip(diff(diff(wF)),multiply(w,diff(diff(F))))],
               [2*v for v in wF])


@lru_cache(maxsize=1)
def quadrature():
    # z=det J, d=det J'. External admissible envelopes: |z,d|<=4,
    # |z'|<=8, |z''|<=24, |d'|<=16, |d''|<=96. See the proof in the report.
    caps = [(4,8,24), (4,16,96), (4,8,24), (4,8,24), (4,16,96)]
    max_curvature = np.zeros((3, 5), dtype=int)
    max_weight = np.zeros((3, 5), dtype=int)
    for cell in range(96):
        endpoints = [rational(-END+2*END*i/96) for i in (cell, cell+1)]
        u = I([endpoints[0].a,endpoints[1].b])
        for k, row in enumerate(kernels(u, 2)):
            for j, (series,(m,m1,m2)) in enumerate(zip(row,caps)):
                bound = abs(series[0])*m2+2*abs(series[1])*m1+2*abs(series[2])*m
                cap = int(float(bound.b))+2
                weight = int(float(abs(series[0]).b))+2
                assert bound < cap and abs(series[0]) < weight
                max_curvature[k,j] = max(max_curvature[k,j],cap)
                max_weight[k,j] = max(max_weight[k,j],weight)
    weights = np.empty((3,5,N+1), dtype=object)
    for i in range(N+1):
        for k, row in enumerate(kernels(rational(-END+2*END*i/N),0)):
            for j, series in enumerate(row):
                v = series[0]*SCALE
                rounded = round(float(v.mid))
                assert abs(v-rounded)<1
                weights[k,j,i] = rounded * (1 if i in (0,N) else 2)
    return weights, max_curvature, max_weight


def certify_regularity(amplitude, xi, perturb):
    """Prove the envelopes needed by quadrature on this particular source and screen."""
    h, xi, extra = rational(amplitude)**2, rational(xi), rational(perturb)
    j, v = I(1), I(0)
    cells = 384
    width = rational(2*END/cells)
    for i in range(cells):
        left = rational(-END + 2*END*i/cells)
        u = I([left.a, (left+width).b])
        _, f, F = profile(u, 2)
        X, Fpp = multiply(diff(f),diff(f)), diff(diff(F))
        den = 1-2*h*xi*F[0]
        assert den > 0
        k = h*(X[0]-xi*Fpp[0])/den
        kp = (h*(X[1]-xi*Fpp[1])+2*h*xi*F[1]*k)/den
        cap = abs(k+extra*(1+u/2))+iv.sqrt(((1+u)/8)**2+(u/10)**2)
        slope = abs(kp+extra/2)+iv.sqrt(rational(1)/64+rational(1)/100)
        assert cap < 2 and slope < 5, (i, amplitude, cap, slope)
        # Majorize the integral equations for the two operator norms on this cell.
        root = iv.sqrt(I(cap.b))
        e = iv.exp(root*width)
        c, s = (e+1/e)/2, (e-1/e)/2
        j, v = c*j+s*v/root, root*s*j+c*v
        assert j < 2 and v < 2


def tidal(u, h, xi, perturb):
    den = 1-u*u
    f = np.exp(1-1/den)
    g = -2*u/den**2
    gp = -2/den**2-8*u*u/den**3
    F = f*f
    k = h*F*(g*g-xi*(4*g*g+2*gp))/(1-2*h*xi*F)
    # Additional isotropic null stress for held-out counterexample only.
    k += perturb*(1+.5*u)
    return np.array([[k+(1+u)/8, u/10],[u/10,k-(1+u)/8]])


def observations(amplitude, xi, perturb=0, single_axis=False):
    def ode(u, y):
        j, v = y.reshape(2,2,2)
        a = tidal(u,amplitude**2,xi,perturb)
        if single_axis:
            a = np.diag([0.,np.trace(a)])  # independent Weyl part cancels first rail
        return np.stack([v,-a@j]).ravel()
    grid = np.linspace(-float(END),float(END),N+1)
    start = np.stack([np.eye(2),np.zeros((2,2))]).ravel()
    def run(rtol, step):
        sol = solve_ivp(ode, [grid[0],grid[-1]], start, t_eval=grid,method="DOP853",
                        rtol=rtol,atol=rtol*.02,max_step=step)
        assert sol.success
        return sol.y.T.reshape(-1,2,2,2)
    trace = run(1e-12,.03125)
    if single_axis:
        assert np.all(trace[:,0,:,0] == [1.,0.]) and np.all(trace[:,1,:,0] == 0.)
    coarse = run(1e-9,.0625)
    agreement = float(np.max(abs(trace-coarse)))
    assert agreement<1e-9
    data = np.rint(np.linalg.det(trace)*SCALE).astype(np.int64).astype(object)
    return data.T, agreement


def moments(traces):
    weights, curv, magn = quadrature()
    z, d = traces
    cols = (z,d,z,z,d)
    length, dx = 2*END, 2*END/N
    out = []
    for row, cr, wg in zip(weights,curv,magn):
        vals = []
        for k, col in enumerate(cols):
            mid = Fraction(int(row[k]@col),2*SCALE**2)*dx
            # Trapezoid, known weight rounding and determinant readout (incl. rounding).
            err = length*(dx**2*int(cr[k])/12 + Fraction(5,SCALE) + int(wg[k])*SENSOR)
            vals.append(rational(mid)+I([-1,1])*rational(err))
        out.append((vals[0]+vals[1],vals[2],vals[3]+vals[4]))
    return out


def fit(rows):
    (l,m,c),(ll,mm,cc) = rows[:2]
    det = m*cc-mm*c
    assert 0 not in det
    h, b = (l*cc-ll*c)/det,(m*ll-mm*l)/det
    return h,b,det


def hull(v):
    # Outward decimal grid.
    lo, hi = math.floor(float(v.a)*1e9)-1, math.ceil(float(v.b)*1e9)+1
    assert rational(Fraction(lo,10**9)) < v and v < rational(Fraction(hi,10**9))
    return [lo/1e9,hi/1e9]


def replay():
    for amplitude, xi, extra in [(Fraction(1,4), Fraction(1,6), 0),
                                 (Fraction(3,8), Fraction(1,6), 0),
                                 (Fraction(3,8), Fraction(1,6), Fraction(45,1000)),
                                 (Fraction(1,4), 0, 0)]:
        certify_regularity(amplitude, xi, extra)
    cal, dc = observations(.25,1/6)
    a, b, det = fit(moments(cal))
    assert rational(Fraction(1,16)) in a and rational(Fraction(1,96)) in b
    assert 0 not in b
    def residuals(data, scale):
        return [l-rational(scale)*(a*m+b*c) for l,m,c in moments(data)]
    self_hold = residuals(cal,1)[2]
    target, dh = observations(.375,1/6)
    pred = residuals(target,Fraction(9,4))
    other,_ = observations(.375,1/6,perturb=.045)
    bad = residuals(other,Fraction(9,4))
    assert 0 in self_hold and all(0 in v for v in pred) and 0 not in bad[0]
    chart, _ = observations(.25,0)
    a0,b0,_ = fit(moments(chart))
    assert 0 in b0 and rational(Fraction(1,16)) in a0
    # A trace-free wave can hide either source on one transverse rail.
    line1,_ = observations(.25,1/6,single_axis=True)
    line2,_ = observations(.375,0,single_axis=True)
    assert not np.array_equal(line1,line2)
    return {"samples_per_trace":N+1,"sensor_half_width":str(SENSOR),
            "rank_determinant":hull(det),"h":hull(a),"b":hull(b),"xi":hull(b/a),
            "unused_fourth_weight_residual":hull(self_hold),"held_amplitude_residuals":[hull(v) for v in pred],
            "extra_trace_source_residuals":[hull(v) for v in bad],
            "minimal_xi":hull(b0/a0),"two_ode_step_controls_max_difference":max(dc,dh),
            "coverage":"deterministic conditional on regularity, clock, profile and sensor envelopes; synthetic trajectory integration has a convergence diagnostic"}


if __name__ == "__main__":
    r = replay()
    if sys.argv[1:] == ["--check"]:
        archived = json.loads((HERE/"lens_result.json").read_text())
        numerical = "two_ode_step_controls_max_difference"
        assert r.pop(numerical)<1e-9 and archived.pop(numerical)<1e-9
        assert r == archived
        print("PASS: weak moments, independent amplitude, minimal and extra trace controls")
    else:
        print(json.dumps(r,indent=2))
