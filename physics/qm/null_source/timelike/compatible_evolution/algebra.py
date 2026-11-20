"""Exact checks of new regularity, source, and fixed-driver identities."""
from pathlib import Path
import argparse,hashlib,json
import sympy as s
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compute():
    t,k,c=s.symbols('t k c',real=True,positive=True)
    x,z=s.symbols('x z',real=True)
    sigma3=s.diag(1,-1);sigma1=s.Matrix([[0,1],[1,0]])
    matrix=x*sigma3+z*sigma1
    assert s.simplify(matrix*matrix-(x*x+z*z)*s.eye(2))==s.zeros(2)
    # Independent coefficient expansion for the once-differentiated vacuum kernel.
    eps,qs,qt,A=s.symbols('eps qs qt A',real=True)
    angle=s.symbols('angle',real=True)
    expr=s.sqrt(1+qt*eps**2)/(1+qs*eps**2)*s.cos(angle+A*eps)
    coefficients=s.series(expr,eps,0,3).removeO().expand()
    assert s.simplify(coefficients.coeff(eps,1)+A*s.sin(angle))==0
    assert s.simplify(coefficients.coeff(eps,2)-(qt/2-qs-A*A/2)*s.cos(angle))==0
    # After multiplying 2k and summing, these are -A cot(t-s)
    # and (A^2-qt+2qs) log(2sin(t-s)); missing A^2 would be invalid.
    f=s.Function('f')(t);q=s.Function('q')(t)
    Omega=s.Function('Omega')(t);C=s.Function('C')(t);n=s.Function('n')(t)
    # Leading formal coefficient of C'+2 i Omega C=f(1+2n)/(4 Omega^2).
    f1=s.symbols('f1',real=True)
    a3=-s.I*f/8;a4=f1/16
    assert s.simplify(2*s.I*a3-f/4)==0
    assert s.simplify(-s.I*f1/8+2*s.I*a4)==0
    # Finite-mode subtraction cancellation: int f' cos = f(t)-2k int f sin
    # because f(seed)=0. The explicit c*f/k term cancels exactly.
    I_sin,yprime=s.symbols('I_sin yprime',real=True)
    low=k*k*yprime/(2*s.pi**2)+c*f/k-c*(f-2*k*I_sin)/k
    assert s.simplify(low-(k*k*yprime/(2*s.pi**2)+2*c*I_sin))==0
    a=s.Function('a')(t);ar=s.Function('a_ref')(t);H=s.Function('H')(t)
    ratio=a/ar
    assert s.simplify(s.diff(ratio*H,t)-s.diff(ratio,t)*H-ratio*s.diff(H,t))==0
    # Fixed F=H'/(6a_ref), actual C'=2a'F=gH'/3, g=a'/a_ref.
    F=s.diff(H,t)/(6*ar)
    assert s.simplify(2*s.diff(a,t)*F-s.diff(a,t)*s.diff(H,t)/(3*ar))==0
    # A reconstructed conserved perfect fluid describes the residual algebra,
    # not a physically implemented controller.
    constraint=s.Function('constraint')(t)
    rho=3*constraint/(2*a**4)
    pressure=constraint/(2*a**4)-F/a**3
    conservation=s.diff(rho,t)+3*s.diff(a,t)/a*(rho+pressure)
    assert s.simplify(conservation.subs(s.diff(constraint,t),2*s.diff(a,t)*F))==0
    # On the retained reference buffer, nonzero initial NEC slope is forced.
    qpprime=s.symbols('qpprime',real=True)
    force=s.Function('force')(t)
    nec=2*constraint/a**4-force/a**3
    slope=s.diff(nec,t).subs({constraint:0,s.diff(constraint,t):0,force:0,
                             s.diff(a,t):0,s.diff(force,t):a**3*qpprime},simultaneous=True)
    assert s.simplify(slope+qpprime)==0
    # Shoot at fixed source; exact coefficients in the interval sign certificate.
    D,T=s.symbols('D T',positive=True);amp=3*D
    endpoint=D*T/2-amp*(s.Rational(9,10)*T)/3+900*T*D*T*amp/6
    assert s.expand(endpoint+s.Rational(2,5)*D*T-450*D*D*T*T)==0
    monotonic_loss=900*T*D*T/6+amp*900*T*T/3
    assert s.expand(3*monotonic_loss-3150*D*T*T)==0
    # Principal Volterra kernel has smooth compact correction at zero.
    u=s.symbols('u',real=True)
    series=s.series(-s.log(s.sin(u)/u),u,0,10).removeO()
    assert series.coeff(u,2)==s.Rational(1,6) and series.coeff(u,4)==s.Rational(1,180)
    return {'schema':'ueot-compatible-algebra/1','status':'PASS',
      'checks':{'Pauli_quadratic_joint_error':True,'second_phase_log_coefficient':True,
        'initial_symbol_coefficients':True,'finite_mode_counterterm_principal_cancellation':True,
        'fixed_driver_not_confused_with_integrated_control':True,
        'fixed_M2_constraint_source':True,'residual_fluid_conservation':True,
        'strict_shooting_constants':True,'driver_initial_NEC_slope':True,'smooth_compact_principal_kernel':True},
      'analytic_proofs_required':['closed fixed buffer','all-order Volterra regularity',
           'Banach fixed point','strict parameter shooting','Hadamard propagation'],
      'formal_Lean_proof':False,'physical_controller_from_residual_fluid':False,
      'source_sha256':{Path(__file__).name:sha(Path(__file__))}}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,indent=2,sort_keys=True)+'\n'
    p=HERE/'algebra.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    print('PASS: exact low-mode cancellation, high-mode kernel, driver and shooting identities')
if __name__=='__main__':main()
