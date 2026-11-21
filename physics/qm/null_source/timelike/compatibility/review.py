"""Independent aggregate energy bound and full field-equation defect.

Consumes inherited initial mode balls and ultraviolet bounds, and the explicit
rational source as a number. It imports neither the scaling nor root solver.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
EVO=HERE.parent/'evolution'
BASE='1a90c68b6178968e6b8239fc97a8b26200f8d59d'
OLD_STRESS_SHA='e68cf02018507c096aaa896c24e11fa32f52204fa08895f3aac615e114e2c218'
LAMBDA=8192
mp.dps=90
iv.dps=78

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def end(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,man,power,_=x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**power
def pair(x):return [str(rat(end(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([end(I(a),0),end(I(b),1)])
def parse(x):return box(F(x[0]),F(x[1]))
def upper(x):return I(end(x,1))
def absolute(x):return I(max(abs(end(x,0)),abs(end(x,1))))
def sinh(x):return (iv.exp(x)-iv.exp(-x))/2
def cosh(x):return (iv.exp(x)+iv.exp(-x))/2

def symbolic_review():
    c,ell,q0,lam,m=sp.symbols('c ell q0 lambda M2',positive=True)
    ar,ai,br,bi=sp.symbols('Ar Ai Br Bi',real=True)
    A=ar+sp.I*ai;B=br+sp.I*bi
    X=(A+B)/sp.sqrt(2);Y=-sp.I*(A-B)/sp.sqrt(2)
    norm=lambda z:sp.expand(z*sp.conjugate(z))
    nA,nB=norm(A),norm(B);cross=ar*br+ai*bi
    assert sp.expand(norm(X)+norm(Y)-nA-nB)==0
    assert sp.expand(norm(Y)-norm(X)/3-(nA+nB-4*cross)/3)==0
    x,y,w,h=sp.symbols('x y omega h')
    Ap=(h*x+w*y+sp.I*(-h*y-w*x))/sp.sqrt(2)
    Bp=(h*x+w*y-sp.I*(-h*y-w*x))/sp.sqrt(2)
    assert sp.expand(Ap-(-sp.I*w*(x+sp.I*y)+h*(x-sp.I*y))/sp.sqrt(2))==0
    assert sp.expand(Bp-(h*(x+sp.I*y)+sp.I*w*(x-sp.I*y))/sp.sqrt(2))==0
    Hρ=6*(4*c*c-3)/c**6;Hp=(40*c*c-54)/c**6
    L=sp.symbols('L')
    R=((168+180*L)*c*c-110-135*L)/(8640*sp.pi**2*c**6)
    P=((160+300*L)*c*c-240-405*L)/(8640*sp.pi**2*c**6)
    assert sp.simplify(2*c*(sp.diff(R,c)+sp.diff(R,L)/c)+3*(R+P))==0
    assert sp.simplify(2*c*sp.diff(Hρ,c)+3*(Hρ+Hp))==0
    assert sp.simplify(R.subs(L,L+2*ell)-R-ell*Hρ/(576*sp.pi**2))==0
    assert sp.simplify(P.subs(L,L+2*ell)-P-ell*Hp/(576*sp.pi**2))==0
    stiff=q0/c**3
    assert sp.simplify(2*c*sp.diff(stiff,c)+6*stiff)==0
    rhog=1/(2*lam**2*c**3);rhocl=m/(54*lam**6*c**3)
    tuned=27*lam**4-54*lam**2*q0
    assert sp.simplify(rhocl.subs(m,tuned)-rhog+q0/(lam**4*c**3))==0
    q=sp.symbols('q');E3=(q*q+2*q)/8
    assert E3.subs(q,1)-E3.subs(q,-1)==sp.Rational(1,2)
    powers={'fixed_M2':0,'whole_state_transport':2,'classical_homothetic':4}
    phases={name:str(lam**(sp.Rational(power,2)-1)) for name,power in powers.items()}
    assert sp.simplify(lam**8*lam**-6*lam**-2)==1
    Xs,m4=sp.symbols('X m4',real=True)
    moments={0:1,1:0,2:sp.Rational(3,4),3:0,4:m4}
    average=lambda poly:sp.expand(sum(coef*moments[pow[0]] for pow,coef in sp.Poly(poly,Xs).terms()))
    second=average((sp.Rational(1,2)+Xs)**2)
    fourth=average((sp.Rational(1,2)+Xs)**4)
    assert second==1 and sp.expand(fourth-second**2)==m4+sp.Rational(3,16)
    assert (m4+sp.Rational(3,16)).subs(m4,sp.Rational(9,16))==sp.Rational(3,4)
    t=sp.symbols('t',real=True);y=(sp.exp(10*t)-1)/10000
    assert sp.simplify(sp.diff(y,t)-10*y)==sp.Rational(1,1000)
    elo=sum((F(10)**k/F(math.factorial(k)) for k in range(11)),F(0))
    assert (elo-1)/10000>1
    return {
        'instantaneous_basis_energy_and_pressure':'PASS',
        'aggregate_Cauchy_bound':'|sum w*A*conj(B)| <= sqrt(N*(N+S))',
        'aggregate_growth':'sqrt(N(t)) <= sqrt(N0)*cosh(r)+sqrt(N0+S)*sinh(r)',
        'AE_and_H1_conservation':'PASS','correlated_source_initial_constraint':'PASS',
        'transplanted_kernel_log_divergence_coefficient':'1/(72*pi^2)',
        'dual_test_function_transport':'j_lambda=lambda^-3*j for four-volume smearing',
        'centered_smeared_covariance_invariant':True,
        'coherent_phase_factor_for_M2_27_lambda_power':phases,
        'retuned_coherent_phase_factor':'lambda*sqrt(1-2*Qeff0/lambda^2)',
        'source_noise':{
            'primary_Y':'s/2+X, fixed candidate label s=+1 or -1 (not averaged), X=+sqrt(3)/2 or -sqrt(3)/2 equiprobably',
            'E_Y_squared':'1','Var_Y_squared':'3/4',
            'general_symmetric_X_variance':'E[X^4]+3/16 >= 3/4',
            'law_of_total_variance':'Var(A) >= Var(Y^2)*A_f^2',
            'scope':'smooth spacetime stress smearing, centered reference, nonzero A_f; lower bound relative to displacement-source mean, not automatically total mean',
            'deterministic_control':'Y=s preserves second moment but changes mean s/2 to s',
        },
        'small_defect_negative_control':{
            'ODE':'y_prime=10*y; y(0)=0','approximate_path':'(exp(10*t)-1)/10000',
            'uniform_equation_defect':'1/1000',
            'endpoint_error_lower_rational':str((elo-1)/10000),
            'consequence':'No metric-distance claim follows without a stability theorem.'}}

def load_inputs():
    old=EVO/'stress/result.json'
    assert sha(old)==OLD_STRESS_SHA,'old absolute-stress receipt changed'
    data=json.loads(old.read_text())
    paths=[old,HERE/'review.py',HERE/'constraints/result.json']
    for rel,digest in data['input_sha256'].items():
        p=EVO/rel
        assert sha(p)==digest,('old proof source changed',rel)
        paths.append(p)
    for rel in ['physics/qm/null_source/FINITE_WINDOW.md',
                'physics/qm/null_source/timelike/continuation/SOURCE.md']:
        p=REPO/rel
        prior=subprocess.check_output(['git','show',BASE+':'+rel],cwd=REPO)
        assert p.read_bytes()==prior,('declared source changed',rel)
        paths.append(p)
    frozen={p:sha(p) for p in set(paths)}
    prop=json.loads((EVO/'propagation/result.json').read_text())
    ext=json.loads((EVO/'propagation/extra_eta0_256.json').read_text())
    modes=prop['targets']['0']['modes']+ext['targets']['0']['modes']
    assert [r['k'] for r in modes]==list(range(2,257))
    uv=json.loads((EVO/'stress/tail_K256_M1024.json').read_text())
    assert uv['uniform_physical_UV_tail']['eta_interval']==['0','3/16']
    low=next(r for r in data['initial_energy_certificates'] if r['finite_K']==256)['selected']['rho_full_lower_bound'][0]
    high=data['extra_eta0_finite']['rho_full_interval_direct_UV'][1]
    Q0=box(F(low),F(high))
    candidate=json.loads((HERE/'constraints/result.json').read_text())
    tuned=next(r for r in candidate['tuned_sources'] if str(r['lambda'])==str(LAMBDA))
    M2=F(tuned['explicit_rational_approximation']['M2'])
    return modes,uv,Q0,M2,frozen

def independent_uniform(modes,uv):
    S=I(0);N0=I(0);cubic=F(0);linear=F(0);harmonic=F(0)
    for mode in modes:
        k=mode['k'];w=iv.sqrt(k*k-1)
        S+=k*k*w
        n=upper(k*k*(parse(mode['e'])-w)/2)
        assert end(n,1)>=0,('Wronskian energy bound failed',k)
        N0+=n;cubic+=k**3;linear+=k;harmonic+=F(1,k)
    c=iv.cos(box(0,F(3,8)));cend=iv.cos(I(F(3,8)))
    h2=iv.tan(box(0,F(3,8)))**2
    r=upper(-iv.log(cend)/2)
    N=upper((iv.sqrt(upper(N0))*cosh(r)+iv.sqrt(upper(N0+S))*sinh(r))**2)
    C=upper(iv.sqrt(N*(N+upper(S))))
    q=1/c**2;E1=(h2-1)/2;E3=3*q*(1-3*h2)/8
    P1=q/3+h2/2+I(F(1,6));P3=-q*(7+27*h2)/8
    e0=1/(2*c);er0=e0-1-E1-E3;pr0=e0-I(F(1,3))-P1-P3
    pref=1/(36*iv.pi**2*c**2);L=iv.log(3*c/4)+2*iv.euler
    anρ=((168+180*L)*c*c-110-135*L)/(8640*iv.pi**2*c**6)
    anp=((160+300*L)*c*c-240-405*L)/(8640*iv.pi**2*c**6)
    er=er0+S-I(cubic)-E1*I(linear)-E3*I(harmonic)
    pr=pr0+S/3-I(cubic)/3-P1*I(linear)-P3*I(harmonic)
    rho=pref*(er+box(0,end(2*N,1)))+anρ
    pressure=pref*(pr+box(-end(4*C/3,1),end(2*N/3+4*C/3,1)))+anp
    ud=uv['uniform_physical_UV_tail']
    rt=F(ud['rho_UV_tail_absolute_bound'][1]);pt=F(ud['pressure_UV_tail_absolute_bound'][1])
    rho+=box(-rt,rt);pressure+=box(-pt,pt)
    assert end(cend,0)>end(I(F(9,10)),1)
    Hρ=I(6);Hp=absolute((40*cend*cend-54)/cend**6)
    return {
        'method':'aggregate_Hilbert_norm_growth_and_direct_finite_spectral_subtraction',
        'eta_interval':['0','3/16'],'K':256,'spectral_weight_S':pair(S),
        'initial_particle_energy_N0_upper':pair(upper(N0)),
        'later_particle_energy_N_upper':pair(N),'cross_energy_upper':pair(C),
        'c_endpoint':pair(cend),'rho_uniform_interval':pair(rho),
        'pressure_uniform_interval':pair(pressure),'rho_absolute_upper':pair(absolute(rho)),
        'pressure_absolute_upper':pair(absolute(pressure)),
        'H1rho_absolute_upper':pair(Hρ),'H1p_absolute_upper':pair(Hp),
        'new_mode_integrations':0}

def certify_models(Q0,M2,uniform):
    lam=I(LAMBDA);loglam=iv.log(lam);coeff=1/(576*iv.pi**2)
    qeff=Q0+6*coeff*loglam
    R=upper(parse(uniform['rho_absolute_upper'])+6*coeff*loglam)
    P=upper(parse(uniform['pressure_absolute_upper'])+
            parse(uniform['H1p_absolute_upper'])*coeff*loglam)
    cend=parse(uniform['c_endpoint'])
    tuned_M2=27*lam**4-54*lam**2*qeff
    assert end(tuned_M2,0)>0
    qcap=absolute(qeff)
    exact_r=upper(2*(R+qcap)/lam**2);exact_p=upper(2*(P+qcap)/lam**2)
    qhat=F(LAMBDA*LAMBDA,2)-M2/(54*LAMBDA*LAMBDA)
    assert M2>0 and qhat>0
    initial_defect=qeff-I(qhat)
    initial_rel=upper(2*absolute(initial_defect)/lam**2)
    explicit_r=upper(2*(R+I(qhat))/lam**2)
    explicit_p=upper(2*(P+I(qhat))/lam**2)
    # Conservation: d_rho=c^-3/2*d_rho(0)-a^-3 int 3h*a^3*d_p.
    abs_pressure=upper(P+qcap/cend**3)
    geometric=upper(cend**I(F(3,2))-cend**3)
    assert end(cend,0)>end(I(2)**I(F(-2,3)),1)
    conserved_r=upper(2*abs_pressure*geometric/lam**2)
    explicit_conserved_r=upper(initial_rel+2*(P+I(qhat)/cend**3)*geometric/lam**2)
    exact_best=min(F(pair(exact_r)[1]),F(pair(conserved_r)[1]))
    explicit_best=min(F(pair(explicit_r)[1]),F(pair(explicit_conserved_r)[1]))
    for bound in [exact_best,F(pair(exact_p)[1]),explicit_best,F(pair(explicit_p)[1])]:
        assert bound<F(1,100),('1 percent gate failed',float(bound))
    assert F(pair(initial_rel)[1])<F(1,500000)
    focusing=upper((I(exact_best)+3*exact_p)/4)
    classical_fraction=1-2*qeff/lam**2
    mixture_vs_geometry=I(F(3,4))*classical_fraction**2
    mixture_vs_total=mixture_vs_geometry/(1+I(exact_best))**2
    assert F(pair(mixture_vs_total)[0])>F(1499,2000)
    explicit_fraction=M2/(27*LAMBDA**4)
    explicit_noise=F(3,4)*explicit_fraction**2/(1+explicit_best)**2
    assert explicit_noise>F(1499,2000)
    return {
        'lambda':LAMBDA,'physical_mu':'1','finite_alpha':'0',
        'quantum_initial_effective_interval':pair(qeff),
        'geometric_density_and_pressure':'1/(2*lambda^2*cos(2*eta)^3)',
        'exact_correlated_source':{
            'M2_formula':'27*lambda^4-54*lambda^2*Qeff0',
            'M2_interval':pair(tuned_M2),'initial_density_defect':'0','initial_momentum_defect':'0',
            'uniform_density_relative_defect_upper':str(exact_best),
            'uniform_pressure_relative_defect_upper':pair(exact_p)[1],
            'uniform_focusing_relative_defect_upper':pair(focusing)[1],
            'density_bound_from_direct_stress':pair(exact_r)[1],
            'density_bound_from_conservation':pair(conserved_r)[1],
            'Qeff0_and_M2_are_correlated':True},
        'explicit_rational_source':{
            'M2':str(M2),'Qhat':str(qhat),
            'initial_density_defect_interval':pair(initial_defect/lam**4),
            'initial_Einstein_nn_relative_abs_upper':pair(initial_rel)[1],
            'uniform_density_relative_defect_upper':str(explicit_best),
            'uniform_pressure_relative_defect_upper':pair(explicit_p)[1],
            'is_exact_initial_constraint_solution':False},
        'full_tensor_components_certified':['orthonormal_00','three_equal_orthonormal_spatial_diagonals','vanishing_off_diagonals'],
        'domain':'homogeneous inner causal region; eta in [0,3/16]',
        'infinite_field_included':True,'defect_covariantly_conserved':True,
        'distance_to_an_exact_metric_certified':False,
        'existence_of_an_exact_nearby_solution_proved':False,
        'global_asymptotically_flat_extension_constructed':False,
        'physical_instrument_implementation_certified':False,
        'retained_source_mixture_noise':{
            'reference_observable':'nonzero, nonnegative, smooth compactly supported spacetime smearing of orthonormal density in the certified inner domain',
            'relative_to_geometric_mean_squared_lower':pair(mixture_vs_geometry)[0],
            'relative_to_total_mean_squared_lower':pair(mixture_vs_total)[0],
            'explicit_source_relative_to_total_mean_squared_lower':str(explicit_noise),
            'uses_uniform_density_defect_to_bound_total_mean':True,
            'small_mean_defect_implies_small_stress_noise':False,
            'geometry_noise_response_not_inferred':True,
        }}

def calculate():
    if not __debug__:raise RuntimeError('Do not use -O; proof assertions are required')
    symbols=symbolic_review()
    modes,uv,Q0,M2,frozen=load_inputs()
    uniform=independent_uniform(modes,uv)
    models=certify_models(Q0,M2,uniform)
    for p,digest in frozen.items():
        assert sha(p)==digest,('source changed during independent review',str(p))
    return {
        'schema':'ueot-compatibility-independent-review/1','reviewed_base':BASE,
        'status':'INDEPENDENT_UNIFORM_FULL_FIELD_DEFECT_BELOW_ONE_PERCENT',
        'symbolic_review':symbols,'independent_uniform_reference':uniform,
        'physical_models':models,'new_mode_integrations':0,
        'input_sha256':{str(p.relative_to(REPO)):digest for p,digest in sorted(frozen.items())}}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true')
    args=parser.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+'\n'
    target=HERE/'review.json'
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,'independent review receipt mismatch'
    for name in ['exact_correlated_source','explicit_rational_source']:
        row=result['physical_models'][name]
        print(name,'rho relative <=',float(F(row['uniform_density_relative_defect_upper'])),
              'p relative <=',float(F(row['uniform_pressure_relative_defect_upper'])))
    print('PASS: independent aggregate energy, conserved defect and exact-source/rational-source distinction.')
