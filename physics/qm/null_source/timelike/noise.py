"""Different stress fluctuations at identical mean stress and finite Ramsey records."""
from fractions import Fraction
from pathlib import Path
import json
import math
import sys

from mpmath import iv, mp

PARENT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PARENT))
from finite_window import q, switched_mean

mp.dps = 75
STEP = 6
WINDOWS = [(Fraction(1,32), Fraction(1,16)), (Fraction(5,32), Fraction(3,16))]


def frequencies(means):
    a,b = means
    return (a,b,b-a,a+b)


def coefficient_majorant(nodes, degree):
    # Chebyshev coefficient l1 norm is submultiplicative. Bound the Hermite interpolant / N².
    inv_n2 = q(Fraction(1,(degree+1)**2))
    cap = inv_n2+2
    for i,node in enumerate(nodes):
        norm = 4/(1-node)**2
        for k,other in enumerate(nodes):
            if k!=i:
                assert 0 not in node-other
                norm *= (1+abs(other))/abs(node-other)
        cap += (2*inv_n2+abs(1-node))*norm
    integer = math.ceil(float(cap.b))+1
    assert cap < integer
    return integer


def point_gate(left, right):
    left,right = [mp.mpf(v.numerator)/v.denominator for v in (left,right)]
    def integrand(z):
        e = left+(right-left)*z
        field = mp.sqrt(3)/2*mp.log((1+mp.sin(2*e))/mp.cos(2*e))
        return 30*z**2*(1-z)**2*field
    return mp.quad(integrand,[0,1])


def character(law, t):
    return sum(p*mp.cos(j*STEP*t) for j,p in law.items())


def moment(law,n):
    return sum(p*(j*STEP)**n for j,p in law.items())


def bounded_sources(fs):
    # Symmetric signs remove odd moments. Both share mean zero and variance 3/4.
    def first(t):
        return iv.cos(iv.sqrt(3)*t/2)
    def second(t):
        return (2+iv.cos(3*t/2))/3
    gaps=[abs(first(t)-second(t)) for t in fs]
    # Taylor with cancellation through degree 2; wide phase enclosures need this stable form.
    # cos(x) through degree 6 has absolute remainder at most |x|^8/8!.
    def fourth_gap(t):
        m4a,m4b=q(Fraction(9,16)),q(Fraction(27,16))
        m6a,m6b=q(Fraction(27,64)),q(Fraction(243,64))
        m8a,m8b=q(Fraction(81,256)),q(Fraction(2187,256))
        return abs((m4b-m4a)*t**4/24-(m6b-m6a)*t**6/720)+(m8a+m8b)*abs(t)**8/40320
    errors=[min(d.b,fourth_gap(t).b) for d,t in zip(gaps,fs)]
    tv=(errors[0]+errors[1]+max(errors[2],errors[3]))/2
    assert tv < q("0.0008")
    new=q(2)
    assert first(new)<0 and second(new)>0
    min_contrast=min(abs(first(new)).a,second(new).a)/5
    radius=iv.sqrt(iv.ln(40)/20000)
    assert min_contrast/2 > radius+q(".001")
    return dict(support_X=1.5,raw_fourth_gap=1.125,two_gate_distance_upper=math.ceil(float(tv.b)*1e8)/1e8,
                added_phase=2,centered_characteristics=[float(first(new).mid),float(second(new).mid)],
                reference_visibility_min=.2,starts_fixed_phase=10000,
                readout_bias_cap=.001,hoeffding_halfwidth_upper=math.ceil(float(radius.b)*1e8)/1e8)


def replay():
    encl = [switched_mean(*w) for w in WINDOWS]
    means = [point_gate(*w) for w in WINDOWS]
    assert all(iv.mpf(str(v)) in box for v,box in zip(means,encl))
    fs = frequencies(means)
    degree = len(fs)+1
    approx = [iv.cos(STEP*f) for f in frequencies(encl)]
    assert all(1 not in x for x in approx)
    cap = coefficient_majorant(approx,degree)
    small = mp.mpf(3)/(4*STEP**2*sum(j*j for j in range(1,degree+1)))
    base = {j:small for j in range(1,degree+1)}
    base[0] = 1-degree*small
    gamma = small/(2*cap)
    # Solve the value/derivative/interior Hermite equations independently in high precision.
    matrix = mp.matrix([[1]*(degree+1), [j*j for j in range(degree+1)]]+
                       [[mp.cos(j*STEP*f) for j in range(degree+1)] for f in fs])
    trials=[]
    for N in (10000,1000000):
        rhs = mp.matrix([1,N*N]+[mp.cos(N*STEP*f) for f in fs])
        coeff = mp.lu_solve(matrix,rhs)
        tail = gamma/N**2
        law = {j:p-tail*coeff[j] for j,p in base.items()}
        law[N] = tail
        assert min(law.values())>0 and abs(sum(law.values())-1)<mp.mpf('1e-68')
        assert abs(moment(law,2)-mp.mpf(3)/4)<mp.mpf('1e-68')
        assert all(abs(character(law,f)-character(base,f))<mp.mpf('1e-68') for f in fs)
        delta = moment(law,4)-moment(base,4)
        lower = gamma*STEP**4*(N**2-cap*degree**4)
        assert delta >= lower > 1
        trials.append(dict(max_amplitude=N*STEP,tail_probability=float(tail),
                           fourth_moment_increase=float(delta),proven_lower_bound=float(lower)))
    # A finite-frequency readout needs an independently bounded amplitude to bound m4 on both sides.
    t=mp.mpf(1)/(STEP*degree)
    diff=(6-8*character(base,t)+2*character(base,2*t))/t**4
    assert diff <= moment(base,4) <= diff/mp.sinc(t*STEP*degree/2)**4
    return dict(phase_frequencies=[float(f) for f in fs],coefficient_bound=cap,
                reference_mean_square_shift=.75,source_mean_square=1,
                base_fourth_moment=float(moment(base,4)),trials=trials,
                bounded_control=bounded_sources(frequencies(encl)),
                normalized_variance_gap="fourth_moment_increase times squared classical smeared stress")


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("enable assertions")
    print(json.dumps(replay(),indent=2))
