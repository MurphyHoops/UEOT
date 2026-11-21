"""Recompute a delayed local probe in the Chapter 71 field, with outward intervals."""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import sys

from mpmath import iv

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / 'correlated_bath/field'
sys.path.insert(0, str(SOURCE))
import probe

iv.dps = 55
design = json.loads((HERE / 'design.json').read_bytes())
mode = lru_cache(None)(probe.mode)
I = iv.mpc(0, 1)
R = iv.mpf


def q(value):
    value = Fraction(value)
    return R(value.numerator) / value.denominator


def dyadic(parts):
    sign, man, exponent, _ = parts
    return (-1)**sign * Fraction(man) * Fraction(2)**exponent


def interval(value):
    scale = 10**15
    lo, hi = map(dyadic, value._mpi_)
    return [str(Fraction((lo*scale).__floor__(), scale)), str(Fraction((hi*scale).__ceil__(), scale))]


def abs2(z):
    return z.real**2 + z.imag**2


def pulse(w, g, start, width):
    return g / w * iv.exp(I*w*start) * (1-iv.exp(I*w*width))


def influence(a, b, gap, opposite, last):
    phase = R(0)
    noise = R(0)
    coefficients = [R(0) for _ in range(4)]
    fourth_moment = R(0)
    vacuum_high = R(0)
    low = []
    for j in range(last+1):
        w, g = mode(j)
        first = pulse(w, g, 0, a)
        second = pulse(w, (-1)**(j*opposite)*g, a+gap, b)
        kernel = iv.mpc(first.real,-first.imag)*second
        phase += 4*kernel.imag
        noise += 2*abs2(second)
        if j < 2:
            low.append(second)
            continue
        for n in range(4):
            coefficients[n] += 4*(kernel*(I*w)**n).imag/factorial(n)
        fourth_moment += 4*abs(kernel)*w**4
        vacuum_high += 2*abs2(second)
    n, c = (q(design['point'][k]) for k in ('n','c'))
    noise += 4*n*sum(map(abs2,low)) + 8*c*(low[0].real*low[1].real+low[0].imag*low[1].imag)
    return phase, noise, coefficients, fourth_moment, vacuum_high


def htail(M):
    return 2*(80/iv.pi)**8/(10*probe.beta**3*M**10)


def full(a,b,gap,opposite,M,lam):
    phi, noise, *_ = influence(a,b,gap,opposite,M)
    tail = lam**2*htail(M)
    return lam**2*phi + R([-16,16])*tail, lam**2*noise + R([0,8])*tail


def measured(phase, noise):
    return (1-iv.exp(-noise)*iv.sin(phase))/2


def sum_moments(left, right):
    return [sum(comb(n,k)*left[k]*right[n-k] for k in range(n+1))
            for n in range(len(left))]


def position_phase(a,b,gap,lam,order):
    """Independent real-space massive retarded kernel, no light-cone crossings."""
    L = 4*iv.pi/iv.sqrt(5)
    ell = L/160
    support = L/6+4*ell
    assert gap > 2*support and gap+a+b < L-2*support
    powers = range(2*order+1)
    mix = 2*(1-q('3/5')*iv.sqrt(q('3/4'))/(iv.sin(iv.pi/80)/(iv.pi/80))**4)
    step = [((1-mix) if n==0 else 0) + mix*((-L/6)**n+(L/6)**n)/2 for n in powers]
    space = sum_moments(step,step)
    box = [ell**n/(n+1) if n%2==0 else R(0) for n in powers]
    for _ in range(8):
        space = sum_moments(space,box)
    time = [gap**n for n in powers]
    for width in (a,b):
        time = sum_moments(time,[width**n/(n+1) for n in powers])
    mean = R(0)
    for m in range(order+1):
        moment = sum((-1)**j*comb(m,j)*time[2*(m-j)]*space[2*j] for j in range(m+1))
        mean += (-1)**m*moment/(4**m*factorial(m)**2)
    max_y = (gap+a+b)**2/4
    assert max_y < (order+2)**2
    error = max_y**(order+1)/factorial(order+1)**2
    return 2*L*lam**2*a*b*(mean+R([-1,1])*error)


def frequency_matching(M, opposite):
    # Unit source: high-shell retarded susceptibility, without lambda^2.
    coeff = [R(0) for _ in range(3)]
    static_abs = R(0)
    exact_at_one = R(0)
    for j in range(2,M+1):
        w,g = mode(j)
        weight = 2*g**2/w
        static_abs += weight
        sign = (-1)**(opposite*j)
        for k in range(3):
            coeff[k] += sign*weight/w**(2*k)
        exact_at_one += sign*weight/(1-1/w**2)
    remainder_static = 4*(80/iv.pi)**8/(9*probe.beta**2*M**9)
    ratio = q('1/6')  # |nu| <= 1, first omitted pole omega_2 = sqrt(6)
    err = (static_abs*ratio**3+remainder_static)/(1-ratio)
    assert abs(exact_at_one-sum(coeff)) < err and abs(mode(2)[1]) > q('1/100')
    return {'C0_C2_C4':list(map(interval,coeff)), 'abs_error_for_abs_nu_le_1':interval(err),
            'finite_shell_actual_error_at_1':interval(abs(exact_at_one-sum(coeff)))}


def calculate():
    spec=design['scale_matching']
    assert spec['phase_polynomial_degree']==3 and spec['retarded_expansion_highest_power']==4
    assert spec['exact_low_shells']==[0,1] and spec['frequency_window']=='|nu|<=1'
    assert hashlib.sha256((SOURCE/'probe.py').read_bytes()).hexdigest()=='7966b2d2cc2951b89d469d10fa0cf704a2f69e7a32e08dd5d2673f040e63b755'
    M=spec['last_matched_shell']
    check_M=spec['independent_replay_shell']
    lam=q(design['point']['lambda'])
    ceiling=q(design['coupling_domain'][1])
    window=q(spec['certified_delay_half_window'])
    results={}
    for case in design['experiments']:
        name=case['id']
        a,b,gap=map(q,(case['a'],case['b'],case['gap']))
        opposite=case['antipodal']
        phi,Q=full(a,b,gap,opposite,M,lam)
        low_phi,low_Q,*_=influence(a,b,gap,opposite,1)
        row={'field_phase':interval(phi),'Q':interval(Q),'p_plusY':interval(measured(phi,Q)),
             'two_mode_phase':interval(lam**2*low_phi),'two_mode_p_plusY':interval(measured(lam**2*low_phi,lam**2*low_Q))}
        results[name]=row
        if opposite:
            margin=probe.length/2-2*probe.length*(q('1/6')+q('1/40'))-a-b-gap
            assert margin>0 and 0 in phi and lam**2*low_phi>q('0.0001')
            row['spacelike_margin']=interval(margin)
            row['two_mode_signalling_trace_distance']=interval(iv.exp(-lam**2*low_Q)*abs(iv.sin(lam**2*low_phi)))
        if not name.startswith('strict_'):
            continue
        _,_,coeff,fourth,noise_high=influence(a,b,gap,opposite,M)
        phi_bound=ceiling**2*(fourth*window**4/24+16*htail(M))
        noise_bound=8*ceiling**2*htail(M)
        prob_bound=(phi_bound+noise_bound)/2
        assert phi_bound<q(spec['phase_target_rad']) and prob_bound<q(spec['binary_event_target'])
        row.update(coefficients_unit_lambda=list(map(interval,coeff)),matched_high_Q_unit_lambda=interval(noise_high),
                   uniform_phase_error_rad=interval(phi_bound),uniform_binary_error=interval(prob_bound),unfitted={})
        for offset in spec['unfitted_offsets']+[spec['extrapolation_offset']]:
            d=q(offset)
            p0,n0,*_=influence(a,b,gap+d,opposite,1)
            pe=lam**2*(p0+sum(c*d**k for k,c in enumerate(coeff)))
            ne=lam**2*(n0+noise_high)
            true_phi,true_Q=full(a,b,gap+d,opposite,check_M,lam)
            err=abs(pe-true_phi)
            obs=measured(true_phi,true_Q)
            row['unfitted'][offset]={'phase_error':interval(err),'field_p_plusY':interval(obs),
                                      'p_error':interval(abs(measured(pe,ne)-obs))}
            if offset in spec['unfitted_offsets']:
                assert err<phi_bound and abs(measured(pe,ne)-obs)<prob_bound
                if opposite:
                    assert margin>window and 0 in true_phi
                else:
                    real=position_phase(a,b,gap+d,lam,design['independent_position_space_order'])
                    assert real.a<=true_phi.b and true_phi.a<=real.b and 0 not in real
                    row['unfitted'][offset]['position_space_phase']=interval(real)
            else:
                assert err>q(spec['phase_target_rad'])
        row['high_susceptibility']=frequency_matching(M,opposite)
    for k,target in [('chapter71_local','0.209161319519'),('chapter71_antipodal','0')]:
        lo,hi=map(Fraction,results[k]['field_phase'])
        assert lo-Fraction(1,10**11)<=Fraction(target)<=hi+Fraction(1,10**11)
    return {'design_sha256':hashlib.sha256((HERE/'design.json').read_bytes()).hexdigest(),
            'mode_source_sha256':hashlib.sha256((SOURCE/'probe.py').read_bytes()).hexdigest(),
            'interval_encoding':'closed outward rational endpoints, decimal grid 10^-15','results':results}


if __name__=='__main__':
    result=calculate()
    if sys.argv[1:]==['--check']:
        assert result==json.loads((HERE/'result.json').read_bytes())
        print('PASS: four local-field experiments, two matched windows, real-space check, frequency threshold and extrapolation controls')
    else:
        print(json.dumps(result,indent=2))
