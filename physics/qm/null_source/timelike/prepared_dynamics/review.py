"""Independent symbolic, interval-identity and false-shortcut review."""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import argparse,hashlib,json
import sympy as sp
import phase_quadrature as pq
import phase_extension as ext
import importlib.util
_spec=importlib.util.spec_from_file_location('prepared_dynamics_assembly',Path(__file__).with_name('assemble.py'))
assemble=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(assemble)
I,iv,bg,old=pq.I,pq.iv,pq.bg,pq.old
HERE=Path(__file__).resolve().parent
iv.dps=70

def intersects(x,y):
    return max(bg.lower(x),bg.lower(y))<=min(bg.upper(x),bg.upper(y))

def symbolic():
    d=sp.symbols('d')
    q,q1,q2,q3,q4=sp.symbols('q q1 q2 q3 q4')
    A=1+q*d
    T=-q2/(4*A)+5*d*q1*q1/(16*A*A)
    T1=-q3/(4*A)+7*d*q1*q2/(8*A*A)-5*d*d*q1**3/(8*A**3)
    T2=-q4/(4*A)+9*d*q1*q3/(8*A*A)+7*d*q2*q2/(8*A*A)-29*d*d*q1*q1*q2/(8*A**3)+15*d**3*q1**4/(8*A**4)
    B=A+d*d*T
    Rn=(-T2/(4*B)+d*q2*T/(4*A*B)+5*d*(2*q1*T1+d*T1*T1)/(16*B*B)
        -5*d*d*q1*q1*T*(2*A+d*d*T)/(16*A*A*B*B))
    r=Rn/(2*sp.sqrt(B))
    expected=pq.r_coefficients([q,q1,q2,q3,q4])+[ext.r4([q,q1,q2,q3,q4])]
    for j,coefficient in enumerate(expected):
        assert sp.expand(sp.diff(r,d,j).subs(d,0)/factorial(j)-coefficient)==0
    V=(q+d*T)/(sp.sqrt(B)+1)+d*d*r
    expected_phase=[q/2,-(q*q+q2)/8,(2*q**3+6*q*q2+5*q1*q1+q4)/32,ext.w7([q,q1,q2,q3,q4])]
    for j,coefficient in enumerate(expected_phase):
        assert sp.expand(sp.diff(V,d,j).subs(d,0)/factorial(j)-coefficient)==0
    z=sp.symbols('z')
    p=sp.symbols('p0:4',real=True)
    phase=sum(2*p[j]*z**(2*j+1) for j in range(4))
    coefficients=[sp.Integer(1)]
    for n in range(1,9):
        v=sum((2*j+1)*2*p[j]*coefficients[n-(2*j+1)] for j in range(min(3,(n-1)//2)+1))/n
        coefficients.append(v if n%2 else -v)
    exponential=sp.series(sp.exp(sp.I*phase),z,0,9).removeO().expand()
    for j,c in enumerate(coefficients):
        assert sp.expand(exponential.coeff(z,j)-(sp.I*c if j%2 else c))==0
    # A different derivation of the pressure-derivative normalization.
    k,y,hprime=sp.symbols('k y hprime')
    qrel=-1-hprime
    differentiated_square=-8*(k*k+qrel)*y
    Ptrace=differentiated_square-8*hprime*y
    assert sp.expand(Ptrace+8*(k*k-1)*y)==0
    assert sp.Rational(-8,6*2*9)==sp.Rational(-2,27)
    # Time reversal retains both stresses but reverses the relevant coherence.
    ur,ui,pr,pi=sp.symbols('ur ui pr pi',real=True)
    coherence=ur*pr+ui*pi
    assert sp.expand(coherence.subs({ui:-ui,pr:-pr},simultaneous=True)+coherence)==0
    assert sp.expand((ur*ur+ui*ui).subs(ui,-ui)-(ur*ur+ui*ui))==0
    assert sp.expand((pr*pr+pi*pi).subs(pr,-pr)-(pr*pr+pi*pi))==0
    H=sp.Matrix([[0,-sp.I/2],[sp.I/2,0]])
    assert H.eigenvals()=={sp.Rational(-1,2):1,sp.Rational(1,2):1}
    # Exact even initial jets, including the local AE odd derivative.
    eta,theta=sp.symbols('eta theta',real=True)
    h=-sp.tan(2*eta)+theta*eta
    qfamily=-1-sp.diff(h,eta)-h*h
    expected_jets=[1-theta,0,8+8*theta-2*theta**2,0,256+128*theta,0]
    for j,e in enumerate(expected_jets):
        assert sp.simplify(sp.diff(qfamily,eta,j).subs(eta,0)-e)==0
    return {'inverse_frequency_r_coefficients_0_to_4':True,'phase_coefficients_1_3_5_7':True,
       'complex_phase_polynomial_0_to_8':True,'independent_trace_pressure_derivative_factor':True,
       'time_reversal_odd_coherence_negative_control':True,'quadratic_coherence_norm_is_half':True,
       'all_initial_odd_geometric_jets_zero':True}

def interval_identities():
    for s,closed in [(2,iv.pi**2/6),(4,iv.pi**4/90),(6,iv.pi**6/945)]:
        assert intersects(pq.zeta(s),closed)
    for tau in [Q(1,128),Q(3,32)]:
        t=I(tau)
        Li2=pq.polylog_positive(2,tau)
        assert intersects(Li2.real,iv.pi**2/6-iv.pi*t+t*t)
        Li3=pq.polylog_positive(3,tau)
        assert intersects(Li3.imag,iv.pi**2*t/3-iv.pi*t*t+2*t**3/3)
        N=8;ks=pq.kernels(tau,N,max_s=3,min_s=-3)
        direct=-I(Q(1,2))-sum((iv.cos(2*k*t) for k in range(1,N+1)),I(0))
        assert intersects(ks[0].real,direct)
        derivative_real=-iv.cos((2*N+1)*t)/iv.sin(t)
        # d/dtau Re K1 = Re(2 i K0).
        assert intersects((2j*ks[0]).real,derivative_real)
    return {'Euler_Maclaurin_zeta_exact_even_identities':True,
       'Jonquiere_polylog_exact_real_imaginary_identities':True,
       'negative_order_tail_and_Dirichlet_kernel_identity':True}

def compute():
    result=json.loads((HERE/'result.json').read_text())
    assert result['status']=='PASS' and result['no_smooth_SCE_extension_preserving_this_prepared_past']
    for relative,digest in result['source_sha256'].items():
        assert hashlib.sha256((HERE.parent/relative).read_bytes()).hexdigest()==digest
    lo,hi=map(Q,result['Qpprime_all_roots'])
    assert Q(-14)<lo<hi<Q(-11)
    nrlo,nrhi=map(Q,result['lambda5_normal_spatial_Einstein_residual'])
    assert Q(12)<nrlo<nrhi<Q(16)
    radius=Q(result['root_tightening']['all_prior_roots_absolute_bound'][1])
    assert radius<Q(9,10**9)
    modes,data,previous=assemble.inputs()
    partial=assemble.finite_values(modes[:255])[2]
    assert bg.lower(partial)>0
    assert hi<0
    interval_checks=interval_identities()
    symbolic_checks=symbolic()
    return {'schema':'ueot-prepared-independent-review/1','status':'PASS',
      'symbolic':symbolic_checks,'interval_identities':interval_checks,
      'all_mode_sign_gate':['-14','-11'],'all_root_radius_gate':'9/1000000000',
      'normal_residual_derivative_gate':['12','16'],
      'finite_256_mode_sign_is_opposite_to_full_field':True,
      'no_explicit_uniform_positive_window_length_claimed':True,
      'preserves_initial_slice_existence':True,
      'excludes_only_current_smooth_prepared_history':True,
      'principal_inverse_is_not_full_RSET_inverse':True,
      'Core_unification_claim':False,
      'source_identity':{Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
      'result_sha256':hashlib.sha256((HERE/'result.json').read_bytes()).hexdigest()}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();result=compute();rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/'review.json'
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    print('PASS: independent coefficients, interval identities, all-root obstruction and scope review')
if __name__=='__main__':main()
