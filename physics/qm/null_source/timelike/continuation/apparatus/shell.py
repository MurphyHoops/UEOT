"""Finite-source apparatus constraints and pressure-transfer counterexample.

Exact Fraction/sympy identities plus directed intervals, 4*pi*G=1. Classical
Einstein-scalar Cauchy data; unresolved absolute quantum stress is not solved.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb, factorial
import argparse
import json
from mpmath import iv
import sympy as s

iv.dps = 45
HERE = Path(__file__).resolve().parent
CENTER, WIDTH, HEIGHT = Q(33, 50), Q(1, 100), Q(1, 10)
POWER = 12


def qi(x):
    x = Q(x)
    return iv.mpf(x.numerator) / x.denominator


def interval(x, digits=14):
    scale = 10 ** digits
    lo = int(float(x.a) * scale) - 2
    hi = int(float(x.b) * scale) + 2
    while not qi(Q(lo, scale)) < x.a:
        lo -= 1
    while not x.b < qi(Q(hi, scale)):
        hi += 1
    return [str(Q(lo, scale)), str(Q(hi, scale))]


def exact_definitions():
    r, z = s.symbols('r z', real=True)
    mu = s.Function('mu')(r)
    f = 1 - 2 * mu / r
    ric3 = 2 * (1-f)/r**2 - 2*s.diff(f,r)/r
    assert s.simplify(ric3 - 4*s.diff(mu,r)/r**2) == 0
    taper = 1 - 10*z**3 + 15*z**4 - 6*z**5
    source_mass = s.Rational(1,6) + s.integrate(
        r**2*taper.subs(z,2*(r-1))**2/2,(r,1,s.Rational(3,2)))
    assert source_mass == s.Rational(7565,26208)
    bump = (1-z*z)**POWER
    i0 = Q(s.integrate(bump,(z,-1,1)))
    i2 = Q(s.integrate(z*z*bump,(z,-1,1)))
    assert i0 > 0 and i2 > 0
    assert s.expand(((1-z*z)**6)**2-bump) == 0
    assert all(s.diff((1-z*z)**6,z,k).subs(z,e) == 0
               for k in range(6) for e in (-1,1))
    return Q(source_mass), i0, i2


SOURCE_MASS, I0, I2 = exact_definitions()


def mass(height=HEIGHT,width=WIDTH):
    return height*width*(CENTER**2*I0 + width**2*I2)


def enclosed(radius,height=HEIGHT,width=WIDTH):
    left,right = CENTER-width,CENTER+width
    if radius <= left:
        return Q(0)
    if radius >= right:
        return mass(height,width)
    z = (radius-CENTER)/width
    total = Q(0)
    for k in range(POWER+1):
        coef = Q((-1)**k*comb(POWER,k))
        for j,prefactor in enumerate((CENTER**2,2*CENTER*width,width**2)):
            order = 2*k+j+1
            total += coef*prefactor*(z**order-(-Q(1))**order)/order
    return height*width*total


def sin_lower_upper(x):
    upper = sum(((-1)**k)*x**(2*k+1)/factorial(2*k+1) for k in range(9))
    lower = upper-x**19/factorial(19)
    return lower,upper


def inner_chi_bracket():
    target = (CENTER-WIDTH)**2/3
    left,right = Q(3,8),Q(2,5)
    assert sin_lower_upper(left)[1]**2 < target
    assert sin_lower_upper(right)[0]**2 > target
    for _ in range(70):
        mid = (left+right)/2
        low,high = sin_lower_upper(mid)
        if high**2 < target:
            left = mid
        elif low**2 > target:
            right = mid
        else:
            break
    return left,right


def proper_length_change(count=256):
    left,right = CENTER-WIDTH,CENTER+WIDTH
    step = (right-left)/count
    total = qi(0)
    for i in range(count):
        a,b = left+i*step,left+(i+1)*step
        m0,m1 = enclosed(a),enclosed(b)
        q = iv.mpf([qi(2*m0/b).a,qi(2*m1/a).b])
        f0 = iv.mpf([qi(1-b*b/3).a,qi(1-a*a/3).b])
        assert f0-q > 0
        integrand = q/(iv.sqrt(f0-q)*iv.sqrt(f0)*(iv.sqrt(f0)+iv.sqrt(f0-q)))
        total += qi(step)*integrand
    assert total > 0
    return interval(total)


def symbolic_jet_check():
    pi,lap,rho,trace_s = s.symbols('Pi LapPi rho S',real=True)
    phi3 = lap + (2*pi*pi+rho+trace_s)*pi
    dust = s.expand(phi3.subs(trace_s,0))
    stiff = s.expand(phi3.subs(trace_s,3*rho))
    assert s.simplify(stiff-dust-3*rho*pi) == 0
    assert dust.subs({pi:1,lap:0}) == 2+rho
    assert stiff.subs({pi:1,lap:0}) == 2+4*rho
    return {'source_phi3':'Delta_gamma(Pi) + Pi*(2*Pi² + rho_d + S_d)',
            'dust_source_phi3_at_peak':str(2+HEIGHT),
            'stiff_source_phi3_at_peak':str(2+4*HEIGHT),
            'stiff_minus_dust_phi3':str(3*HEIGHT),
            'center_phi3_both':'2',
            'difference_cubic_coefficient':str(HEIGHT/2),
            'finite_window_prediction':'NOT_PROVIDED: higher-derivative and lifespan bounds required'}


def main():
    left,right = CENTER-WIDTH,CENTER+WIDTH
    dm = mass()
    assert enclosed(left) == 0 and enclosed(right) == dm
    assert 0 < dm < Q(1,1000)
    compactness = Q(3,4)+2*dm/left
    assert compactness < 1 and left < right < 1
    chi_low,chi_high = inner_chi_bracket()
    assert chi_low > Q(3,8)
    eta_gap = iv.mpf([qi(chi_low-Q(3,8)).a,qi(chi_high-Q(3,8)).b])
    chi_iv = iv.mpf([qi(chi_low).a,qi(chi_high).b])
    tau_gap = eta_gap*iv.mpf([iv.sqrt(3*iv.cos(2*chi_iv)).a,
                            iv.sqrt(3*iv.cos(qi(Q(3,4)))).b])
    f0 = 1-right*right/3
    f1 = f0-2*dm/right
    concentration = []
    for h in (1,10,100,1000):
        height,width = Q(h),Q(1,10000*h*h)
        dmass = mass(height,width)
        comp = Q(3,4)+2*dmass/(CENTER-width)
        assert CENTER-width > left and CENTER+width < right and comp < 1
        concentration.append({'height':h,'half_width':str(width),
            'delta_GM':str(dmass),'delta_GM_decimal':float(dmass),
            'delta_phi3_stiff_minus_dust':3*h,
            'initial_compactness_upper':float(comp)})
    assert all(concentration[i+1]['delta_GM_decimal'] < concentration[i]['delta_GM_decimal']
               for i in range(len(concentration)-1))
    return {'status':'CLASSICAL_INITIAL_CONSTRAINTS_AND_LOCAL_TRANSFER_COUNTEREXAMPLE',
        'scientific_base':'a3ae75078ae903163bf0759fbd302e836aeeea84',
        'units':'core radius=1, 4*pi*G=1; masses are Gm',
        'source_GM_ADM':str(SOURCE_MASS),
        'apparatus_profile':{'center_area_radius':str(CENTER),'half_width':str(WIDTH),
            'peak_density':str(HEIGHT),'shape':'(1-z²)^12 for |z|<1, zero elsewhere',
            'I0':str(I0),'I2':str(I2)},
        'delta_GM':str(dm),'delta_GM_decimal':float(dm),
        'total_GM':str(SOURCE_MASS+dm),
        'initial_global_2mu_over_R_upper':str(compactness),
        'initial_radial_metric_ratio_at_outer_edge':interval(qi(f0/f1)),
        'proper_shell_thickness_increment':proper_length_change(),
        'inner_initial_chi_interval':[str(chi_low),str(chi_high)],
        'center_collection_eta':'3/8','conformal_margin':interval(eta_gap),
        'center_proper_margin':interval(tau_gap),
        'center_protection':'same initial data in R<13/20; classical domain of dependence',
        'local_transfer':symbolic_jet_check(),
        'concentration_counterexamples':concentration,
        'not_claimed':['self-consistent absolute quantum reference stress',
            'real detector stress or hardware verification','finite-window local transfer accuracy',
            'non-spherical apparatus protection','unchanged quantum covariance at outer sensor'],
        'references':['https://arxiv.org/abs/gr-qc/0703035',
            'https://doi.org/10.1007/BF01645389','https://doi.org/10.1103/PhysRev.136.B571']}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O; analytic and interval assertions are required')
    parser = argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = main()
    output = HERE/'result.json'
    if args.write:
        output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    if args.check:
        assert json.loads(output.read_text()) == result
    print(json.dumps(result,indent=2,ensure_ascii=False))
