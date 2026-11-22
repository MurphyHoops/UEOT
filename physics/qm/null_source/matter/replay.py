"""One pulse: Einstein source, two probe protocols, and a BESII yield check."""
import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import product
from math import cos, exp, pi
from pathlib import Path

import numpy as np
import sympy as sy
from scipy.integrate import quad, solve_ivp


def field_equations():
    u,v,x,y = coords = sy.symbols("u v x y", real=True)
    k = sy.Function("K")(u)
    h = sy.Function("h")(u)
    metric = sy.Matrix([[-k*(x*x+y*y),-1,0,0],[-1,0,0,0],[0,0,1,0],[0,0,0,1]])
    inv = metric.inv()
    axes = range(4)
    gamma = {(a,b,c): sum(inv[a,d]*(sy.diff(metric[d,b],coords[c])
                   +sy.diff(metric[d,c],coords[b])-sy.diff(metric[b,c],coords[d]))
                   for d in axes)/2 for a,b,c in product(axes,repeat=3)}
    ric = sy.Matrix(4,4,lambda i,j: sum(sy.diff(gamma[a,i,j],coords[a])
          -sy.diff(gamma[a,i,a],coords[j])+sum(gamma[a,a,b]*gamma[b,i,j]
          -gamma[a,j,b]*gamma[b,i,a] for b in axes) for a in axes))
    assert ric == sy.diag(2*k,0,0,0) and (inv*ric).trace()==0
    assert ric*inv*ric==sy.zeros(4)  # Ricci-square tensor in the conformal-vacuum stress
    tidal=sy.Matrix(2,2,lambda i,j:sy.diff(gamma[i+2,0,0],coords[j+2]))
    assert tidal==sy.eye(2)*k  # Weyl is the trace-free part of this plane-wave profile
    potential = [0,0,h,0]
    field = sy.Matrix(4,4,lambda i,j:sy.diff(potential[j],coords[i])-sy.diff(potential[i],coords[j]))
    raised = inv*field*inv
    assert metric.det()==-1 and sum(field.multiply_elementwise(raised))==0
    assert all(sum(sy.diff(raised[i,j],coords[i]) for i in axes)==0 for j in axes)
    stress = field*inv*field.T
    scalar_grad = sy.Matrix([sy.diff(h,c) for c in coords])
    assert stress == scalar_grad*scalar_grad.T and (scalar_grad.T*inv*scalar_grad)[0]==0
    mixed = inv*stress
    assert all(sum(sy.diff(mixed[i,j],coords[i])+sum(gamma[i,i,b]*mixed[b,j]
           -gamma[b,i,j]*mixed[i,b] for b in axes) for i in axes)==0 for j in axes)
    assert gamma[2,0,0]==k*x and gamma[3,0,0]==k*y
    # Improved scalar and Maxwell with the same pulse. Keep track of the
    # Einstein-tensor term in the scalar stress when solving for K.
    power, share, xi = sy.symbols("power share xi")
    def curvature(scalar_power, gauge_power, coupling):
        b = coupling*scalar_power
        return ((scalar_power+gauge_power)*sy.diff(h,u)**2-b*sy.diff(h**2,u,2))/(1-2*b*h**2)
    target = curvature(power,0,xi)
    mixed = curvature((1-share)*power,share*power,xi/(1-share))
    assert sy.cancel(target-mixed)==0
    baseline = {power:sy.Rational(1,16),share:sy.Rational(1,2),xi:sy.Rational(1,6),
                h:1,sy.diff(h,u):0,sy.diff(h,u,2):-2}
    fixed = curvature((1-share)*power,share*power,xi)
    assert target.xreplace(baseline)==sy.Rational(2,47)
    assert fixed.xreplace(baseline)==sy.Rational(2,95)
    return {"Ric_uu":"2 K","T_uu":"(dh/du)^2","trace":0,"divergence":[0]*4,
            "mixed_improved_center_matched_xi":"2/47","mixed_improved_center_fixed_xi":"2/95"}


def pulse(s):
    return exp(1-1/(1-s*s)) if abs(s)<1 else 0.


def slope(s):
    return -2*s*pulse(s)/(1-s*s)**2 if abs(s)<1 else 0.


def geometry(amplitude):
    def rhs(s, y):
        return y[1], -(amplitude*slope(s))**2*y[0]
    solution = solve_ivp(rhs,(-1,1),(1.,0.),method="DOP853",dense_output=True,rtol=3e-13,atol=2e-15)
    assert solution.success
    sep, speed = solution.y[:,-1]
    # Independent first-order system integration and integrated Jacobi equations.
    other = solve_ivp(rhs,(-1,1),(1.,0.),method="RK45",rtol=1e-12,atol=1e-14)
    assert other.success
    np.testing.assert_allclose(other.y[:,-1],[sep,speed],rtol=0,atol=2e-11)
    def acceleration(s):
        return rhs(s,solution.sol(s))[1]
    def integral(fun):
        return quad(fun,-1,1,epsabs=2e-13,epsrel=2e-13)[0]
    np.testing.assert_allclose([sep,speed],[1+integral(lambda s:(1-s)*acceleration(s)),
                               integral(acceleration)],rtol=0,atol=2e-12)
    return [float(sep),float(speed)]


def interference():
    half = quad(pulse,-1,0,epsabs=1e-14)[0]
    gL = 4*pi/half  # length in units of sqrt(4 pi G), coupling held fixed
    phase_per_amplitude = quad(lambda s:gL*pulse(s),-1,0)[0]
    closed = phase_per_amplitude - quad(lambda s:gL*pulse(s),0,1)[0]
    assert abs(closed)<1e-13
    answer = {}
    for n in (3,5):
        h = np.diag([.5,-.5]+[0.]*(n-2))
        assert np.trace(h)==0 and 2*np.trace(h@h)==1
        swap = np.eye(n)
        swap[:2,:2]=[[0,1],[-1,0]]
        np.testing.assert_array_equal(swap@h@swap.T,-h)
        entries = []
        for amp in (.25,-.25,.125):
            theta = amp*phase_per_amplitude
            phases = np.exp(1j*theta*h.diagonal())
            wf = np.mean(phases).real
            wa = (abs(phases.sum())**2-1)/(n*n-1)
            # Adjoint acts on E_ij with phase exp(i theta (h_i-h_j)); remove the scalar.
            adj_trace = (np.outer(phases,phases.conj()).sum().real-1)/(n*n-1)
            np.testing.assert_allclose([wf,wa],[(n-2+2*cos(theta/2))/n,adj_trace],atol=2e-14)
            entries.append([float(wf),float(wa),float((1+wf)/2)])
        np.testing.assert_allclose(entries[0],entries[1],atol=1e-14)
        y_small,y_large = 1-entries[2][0],1-entries[0][0]
        inferred = (4*y_small-y_large)/y_small**2
        assert abs(inferred-n)<1e-11
        wrong_n=8-n
        delta=.003
        wrong_residual=abs(y_large-4*y_small+wrong_n*y_small**2)
        max_change=(5+2*wrong_n*y_small)*delta+wrong_n*delta**2
        assert wrong_residual>max_change
        answer[str(n)] = dict(Wfund_Wadj_pbright=entries, two_amplitude_N=float(inferred),
                              wrong_N_residual=wrong_residual, max_shift_at_003=max_change)
    assert answer["3"]["Wfund_Wadj_pbright"][0][0] < answer["5"]["Wfund_Wadj_pbright"][0][0]
    return {"pulse_half_integral":half,"symmetric_arm_phase":closed,"groups":answer}


def inclusive_ratio():
    center, stat, sys = F("2.18"),F(".02"),F(".08")
    lower,upper = center-2*(stat+sys),center+2*(stat+sys)
    energy,L,selected,bg,trig,eff,isr = 2.60,1.222,24026,193,.998,.6381,1.08
    sigma_mu_pb = 4*pi/(3*137.035999**2*energy**2)*389379365.6
    exposure=L*sigma_mu_pb*trig*isr
    reconstructed=(selected-bg)/(exposure*eff)
    # Expose the central-value mismatch; comparison uses the published result.
    discrepancy=reconstructed-float(center)
    point_rebuilt=abs(discrepancy) <= .005
    assert not point_rebuilt and lower < reconstructed < upper
    counts={}
    for n in (3,5):
        up, down = F(n+1,2*n),F(1-n,2*n)
        born = n*(up**2+2*down**2)
        cf=F(n*n-1,2*n)
        interval=[born*F(9,10)**2,born*F(11,10)**2]
        disjoint=interval[0]>upper or interval[1]<lower
        # Hold the primary ISR/trigger conventions fixed in this yield example.
        efficiency_needed=(selected-bg)/(exposure*float(born))
        assert 0<efficiency_needed<1
        assert abs(exposure*float(born)*efficiency_needed+bg-selected)<1e-9
        assert disjoint==(n==5)
        counts[str(n)]=dict(R0=str(born),alpha_s_over_pi_coefficient=str(3*cf/4),
                            expected_box=list(map(float,interval)),disjoint_if_both_budgets_hold=disjoint,
                            dynamics_times_response_to_match=list(map(float,(lower/born,upper/born))),
                            epsilon_for_exact_selected_yield_at_Born=efficiency_needed)
    assert counts["3"]["R0"]=="2" and counts["5"]["R0"]=="17/5"
    assert upper/F(17,5)==F(7,10)
    return dict(source="arXiv:0903.0900, Table 1 and Eq. (2)",
                sqrt_s_GeV=energy,signal_yield=selected-bg,muon_Born_pb=sigma_mu_pb,
                printed_table_R_alpha0=reconstructed, printed_table_excess=discrepancy,
                reproduces_published_two_decimals=point_rebuilt,reported_R=float(center),two_error_box=[float(lower),float(upper)],
                colors=counts)


def result():
    from review_inference import check, SUMMARY
    geo={str(a):geometry(a) for a in (.25,-.25,.125,0.)}
    assert geo["0.25"]==geo["-0.25"] and geo["0.0"]==[1,0]
    assert geo["0.25"][1]<geo["0.125"][1]<0
    return dict(baseline="3346989339cfbfa2322812448cee336c8633ff89", status="PASS",
                contract_sha256=hashlib.sha256(Path(__file__).with_name("CONTRACT.md").read_bytes()).hexdigest(),
                field=field_equations(), geodesic_exit=geo, probes=interference(), BESII=inclusive_ratio(),
                inference_mixture=check(pulse,slope,SUMMARY))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    if not __debug__:
        raise RuntimeError("Enable assertions")
    fresh=result()
    if args.check:
        archived=json.loads(Path(__file__).with_name("observed.json").read_text())
        def compare(a,b):
            if isinstance(a,dict):
                assert a.keys()==b.keys()
                for k in a:
                    compare(a[k],b[k])
            elif isinstance(a,list):
                assert len(a)==len(b)
                for x,y in zip(a,b):
                    compare(x,y)
            elif isinstance(a,float):
                np.testing.assert_allclose(a,b,rtol=1e-12,atol=2e-12)
            else:
                assert a==b
        compare(fresh,archived)
        print("PASS: null source, geodesic readout, gauge-invariant probes and BESII yield")
    else:
        print(json.dumps(fresh,indent=2,allow_nan=False))
