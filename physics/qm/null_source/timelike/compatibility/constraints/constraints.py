"""Interval certificates for same-shape initial constraint candidates.

The entire reference metric and covariance are scaled. The classical second
moment is a separate contract. A scalar constraint solution is not a solution
of all semiclassical Einstein equations or a global finite-source state.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
from mpmath import iv
import sympy as sp

HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parents[1]
EVO=TIMELIKE/'evolution'
BASE='1a90c68b6178968e6b8239fc97a8b26200f8d59d'
iv.dps=80
INHERITED_RESULT_SHA='e68cf02018507c096aaa896c24e11fa32f52204fa08895f3aac615e114e2c218'
LOADED_SOURCE_SHA=hashlib.sha256((HERE/'constraints.py').read_bytes()).hexdigest()


def I(x):
    if hasattr(x,'_mpi_'):return x
    r=Q(x)
    return iv.mpf(r.numerator)/r.denominator


def endpoint(x,side):
    sign,man,exponent,_=x._mpi_[side]
    return Q((-1 if sign else 1)*man)*Q(2)**exponent


def lo(x):return endpoint(x,0)
def hi(x):return endpoint(x,1)
def box(a,b):return iv.mpf([I(a).a,I(b).b])
def pair(x):return [str(lo(x)),str(hi(x))]
def absolute_upper(x):return max(abs(lo(x)),abs(hi(x)))


def hashes():
    names=[HERE/'constraints.py',EVO/'stress/result.json',
           EVO/'stress/tail.py',EVO/'stress/assemble.py',
           TIMELIKE/'continuation/SOURCE.md',
           TIMELIKE/'instrument/instrument.py',TIMELIKE.parent/'FINITE_WINDOW.md']
    return {str(p.relative_to(TIMELIKE.parent)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in names}


def reference_interval():
    raw=(EVO/'stress/result.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==INHERITED_RESULT_SHA, 'inherited stress receipt changed'
    data=json.loads(raw)
    assert data['scheme']=='Anderson_Eaker_mu1_no_additional_finite_curvature_terms'
    entry=next(x for x in data['initial_energy_certificates'] if x['finite_K']==256)
    lower=Q(entry['selected']['rho_full_lower_bound'][0])
    upper=Q(data['extra_eta0_finite']['rho_full_interval_direct_UV'][1])
    assert Q(3,2)<lower<upper
    return box(lower,upper)


def equation(x,q,C,kind):
    x=I(x)
    if kind=='fixed_M2_27':
        return x-1/x-C*iv.log(x)-2*I(q)
    if kind=='transport_entire_state':
        return x-C*iv.log(x)-1-2*I(q)
    raise ValueError(kind)


def endpoint_root(q,C,kind,steps=112):
    left,right=Q(1),Q(2)
    assert hi(equation(left,q,C,kind))<0
    while lo(equation(right,q,C,kind))<=0:
        right*=2
    for _ in range(steps):
        middle=(left+right)/2
        sign=equation(middle,q,C,kind)
        if hi(sign)<0:left=middle
        elif lo(sign)>0:right=middle
        else:raise RuntimeError('Increase interval precision before claiming a root bracket')
    below=equation(left,q,C,kind)
    above=equation(right,q,C,kind)
    assert hi(below)<0<lo(above)
    return {'x_bracket':[str(left),str(right)],
            'equation_at_lower':pair(below),'equation_at_upper':pair(above)}


def root_family(q,C,kind):
    low=endpoint_root(lo(q),C,kind)
    high=endpoint_root(hi(q),C,kind)
    x=box(Q(low['x_bracket'][0]),Q(high['x_bracket'][1]))
    lam=iv.sqrt(x)
    if kind=='fixed_M2_27':
        derivative_lower=1-C*C/4
        fraction=1-1/(x*x)
        assert lo(derivative_lower)>0 and lo(fraction)>Q(9,10)
        domain='all x>0; unique positive root for every fixed Q and alpha'
    else:
        derivative_lower=1-C
        fraction=1-1/x
        assert lo(derivative_lower)>0 and lo(fraction)>Q(3,4)
        domain='x>=1 only; a separate very small x branch is not excluded'
    return {'contract':kind,'alpha':'0','x_domain_for_claim':domain,
            'Q_lower_endpoint_root':low,'Q_upper_endpoint_root':high,
            'x_interval':pair(x),'lambda_interval':pair(lam),
            'derivative_uniform_lower_bound':str(lo(derivative_lower)),
            'quantum_fraction_of_required_initial_density':pair(fraction),
            'is_small_quantum_fraction':False}


def tuned_source(lam,q,C):
    lam=Q(lam);assert lam>=1
    x=lam*lam
    effective=q+C*iv.log(I(lam))
    m2=I(27*x*x)-I(54*x)*effective
    relative=2*effective/I(x)
    assert lo(m2)>0 and 0<lo(relative)<=hi(relative)<1
    midpoint=(lo(effective)+hi(effective))/2
    rational_m2=27*x*x-54*x*midpoint
    assert rational_m2>0
    density_error=(effective-I(midpoint))/I(x*x)
    nn_error=-2*density_error
    relative_nn=I(x)*nn_error
    return {'lambda':str(lam),'alpha':'0','Q_effective_initial':pair(effective),
        'M2_exact_correlated_formula':'27*lambda^4-54*lambda^2*(Q+C*log(lambda))',
        'M2_interval':pair(m2),'M2_is_function_of_the_same_Q':True,
        'M2_interval_is_not_an_independent_choice':True,
        'classical_Pi_rms_interval':pair(iv.sqrt(m2/I(27*lam**6))),
        'relative_decrease_from_classical_homothety':pair(relative),
        'relative_field_amplitude_to_classical_homothety':pair(iv.sqrt(1-relative)),
        'initial_Hamiltonian_residual_with_exact_correlated_M2':'0',
        'initial_momentum_residual':'0 by homogeneity and isotropy',
        'explicit_rational_approximation':{
            'Q_effective_midpoint':str(midpoint),'M2':str(rational_m2),
            'density_constraint_error_interval':pair(density_error),
            'Einstein_nn_residual_interval':pair(nn_error),
            'Einstein_nn_relative_residual_interval':pair(relative_nn),
            'Einstein_nn_relative_absolute_bound':str(absolute_upper(relative_nn)),
            'is_exact_constraint_data':False},
        'later_density_source_minus_geometry':
            'lambda^-4*(rho_q_eff(eta)-Q_effective_initial*cos(2eta)^-3)',
        'later_pressure_source_minus_geometry':
            'lambda^-4*(p_q_eff(eta)-Q_effective_initial*cos(2eta)^-3)',
        'full_semiclassical_evolution_proved':False}


def algebra():
    l,q,c,alpha,m=sp.symbols('lambda Q C alpha M2',positive=True)
    rho_cl=m/(54*l**6)
    rho_q=(q+c*sp.log(l)+6*alpha)/l**4
    required=1/(2*l**2)
    fixed=sp.expand(2*l**4*(required-rho_cl.subs(m,27)-rho_q))
    assert sp.simplify(fixed-(l*l-1/(l*l)-2*c*sp.log(l)-2*q-12*alpha))==0
    natural=sp.expand(2*l**4*(required-rho_cl.subs(m,27*l*l)-rho_q))
    assert sp.simplify(natural-(l*l-1-2*c*sp.log(l)-2*q-12*alpha))==0
    exact_m=27*l**4-54*l*l*(q+c*sp.log(l)+6*alpha)
    assert sp.simplify(required-rho_cl.subs(m,exact_m)-rho_q)==0
    h=sp.symbols('c_eta',positive=True)
    old_required=1/(2*l*l*h**3)
    later_cl=exact_m/(54*l**6*h**3)
    assert sp.simplify(later_cl-old_required+(q+c*sp.log(l)+6*alpha)/(l**4*h**3))==0
    x=sp.symbols('x',positive=True)
    assert sp.simplify(1+1/x**2-c/x-((1/x-c/2)**2+1-c*c/4))==0
    # Exact positive-density taper inherited from the finite classical source.
    s,z=sp.symbols('s z',real=True)
    bump=1-10*z**3+15*z**4-6*z**5
    assert sp.simplify(sp.diff(bump,z)+30*z*z*(z-1)**2)==0
    mass=sp.Rational(1,6)+sp.integrate(s*s*bump.subs(z,2*(s-1))**2/2,(s,1,sp.Rational(3,2)))
    assert mass==sp.Rational(7565,26208)
    return {'all_scaling_constraint_identities':True,
        'exact_correlated_tuning_identity':True,
        'later_stiff_source_subtraction_identity':True,
        'global_fixed_M2_monotonicity_identity':True,
        'taper_derivative':'-30*z^2*(1-z)^2',
        'conditional_total_profile_mass_coefficient':str(mass)}


def finite_ball(fixed_root,natural_root):
    # This is a geometry/total-density stencil, not a constructed QFT exterior.
    collection=Q(3,8);last_gate=Q(3,16)
    threshold_collection=1/(iv.sqrt(3)*iv.sin(I(collection)))
    threshold_last_gate=1/(iv.sqrt(3)*iv.sin(I(last_gate)))
    output={}
    for name,r in [('fixed_M2_27',fixed_root),('transport_entire_state',natural_root)]:
        lam=box(Q(r['lambda_interval'][0]),Q(r['lambda_interval'][1]))
        x=box(Q(r['x_interval'][0]),Q(r['x_interval'][1]))
        assert lo(lam)>hi(threshold_collection)
        assert lo(lam)<lo(threshold_last_gate)<hi(threshold_last_gate)<hi(lam)
        output[name]={
            'co_scaled_core_area_radius':pair(lam),
            'co_scaled_taper_outer_area_radius':pair(I(Q(3,2))*lam),
            'conditional_co_scaled_ADM_GM':pair(I(Q(7565,26208))*lam),
            'conditional_fixed_radius_ADM_GM':pair(I(Q(7565,26208))/x),
            'fixed_original_core_local_2mu_over_R_at_boundary':pair(1/(3*x)),
            'old_center_collection_eta_3over8_inside_fixed_radius_core_domain':False,
            'old_last_gate_eta_3over16_uniformly_guaranteed_by_Q_bracket':False}
    assert hi(iv.sin(I(collection)))<lo(1/iv.sqrt(3))
    return {'original_core_area_radius':'1','original_taper_outer_area_radius':'3/2',
        'conditional_total_density_profile':
            'rho_tot(R)=B(R/lambda)^2/(2lambda^2), or B(R)^2/(2lambda^2)',
        'co_scaled_profile_2mu_over_R_global_upper':'3/4',
        'co_scaled_profile_core_2mu_over_R_upper':'1/3',
        'fixed_radius_profile_2mu_over_R_global_upper':'3/(4lambda^2)',
        'co_scaled_null_coordinate_containment_of_original_protocol':True,
        'fixed_radius_lambda_upper_for_eta_3over8':pair(threshold_collection),
        'fixed_radius_lambda_upper_for_eta_3over16':pair(threshold_last_gate),
        'branches':output,
        'conditional_profile_is_actual_global_quantum_state':False,
        'global_exterior_Hadamard_state_and_renormalized_stress_matching':'OPEN',
        'global_semiclassical_cauchy_evolution':'OPEN',
        'old_ADM_mass_and_old_instrument_program_preserved':False}


def calculate():
    assert hashlib.sha256((HERE/'constraints.py').read_bytes()).hexdigest()==LOADED_SOURCE_SHA, 'source changed after import'
    frozen=hashes()
    q=reference_interval()
    C=1/(96*iv.pi**2)
    assert 0<lo(C)<=hi(C)<1
    symbolic=algebra()
    fixed=root_family(q,C,'fixed_M2_27')
    natural=root_family(q,C,'transport_entire_state')
    unscaled=27-54*q
    assert hi(unscaled)<0
    no_anomaly_x=q+iv.sqrt(q*q+1)
    omitted_log_residual=-C*iv.log(no_anomaly_x)
    assert hi(omitted_log_residual)<0
    natural_x=box(Q(natural['x_interval'][0]),Q(natural['x_interval'][1]))
    wrong_fixed_M2_at_natural_root=1-1/natural_x
    assert lo(wrong_fixed_M2_at_natural_root)>0
    result={
        'status':'EXACT_INITIAL_CONSTRAINT_CANDIDATES_ON_SPECIFIED_SCALED_BACKGROUND',
        'reviewed_base':BASE,'interval_decimal_precision':iv.dps,
        'reference_Q_interval':pair(q),'C_density_log_scale':pair(C),
        'fixed_physical_mu':'1','additional_finite_alpha':'0',
        'quantum_reference_transport':'g_lambda=lambda^2*g; W_lambda=lambda^-2*W',
        'reference_zero_mode_transport':{
            'preparation_slice':'Var(q0)=1/(6lambda^2); Var(p0)=3lambda^2/2; Cov(q0,p0)=0',
            'at_eta0_and_other_slices':'V_lambda=S_lambda*V*S_lambda^T, S_lambda=diag(lambda^-1,lambda); retain propagated q-p covariance'},
        'classical_contracts':{
            'fixed_source_second_moment':'M2=27',
            'entire_field_state_transport':'M2=27lambda^2',
            'classical_Einstein_homothety':'M2=27lambda^4'},
        'symbolic_checks':symbolic,'fixed_M2_root':fixed,'entire_state_transport_root':natural,
        'tuned_sources':[tuned_source(15,q,C),tuned_source(8192,q,C)],
        'negative_controls':{
            'required_M2_at_original_scale_alpha0':pair(unscaled),
            'nonnegative_classical_source_at_original_scale_rejected':True,
            'omitting_log_anomaly_equation_residual':pair(omitted_log_residual),
            'using_fixed_M2_at_entire_state_transport_root_residual':pair(wrong_fixed_M2_at_natural_root),
            'classical_homothety_quantum_effective_positive_for_lambda_ge1':True,
            'classical_homothety_exact_constraint_repair_for_lambda_ge1':False},
        'finite_ball_scope':finite_ball(fixed,natural),
        'source_sha256':frozen,
        'not_proved':['full_semiclassical_surface_Hadamard_data','new_exact_semiclassical_evolution',
            'distance_to_an_exact_solution','physical_exterior_quantum_state','instrument_preparation_cost']}
    assert frozen==hashes(),'source changed during certificate calculation'
    return result


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Proof assertions require ordinary Python; do not use -O')
    p=argparse.ArgumentParser()
    p.add_argument('--write',action='store_true')
    p.add_argument('--check',action='store_true')
    args=p.parse_args()
    receipt=calculate()
    path=HERE/'result.json'
    if args.write:path.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
    if args.check:assert receipt==json.loads(path.read_text()),'receipt mismatch'
    for name in ('fixed_M2_root','entire_state_transport_root'):
        r=receipt[name]
        print(name,'lambda',[float(Q(x)) for x in r['lambda_interval']],
              'quantum_fraction',[float(Q(x)) for x in r['quantum_fraction_of_required_initial_density']])
    for r in receipt['tuned_sources']:
        print('lambda',r['lambda'],'M2 relative decrease',
              [float(Q(x)) for x in r['relative_decrease_from_classical_homothety']],
              'rational instance relative nn error',
              float(Q(r['explicit_rational_approximation']['Einstein_nn_relative_absolute_bound'])))
    print('PASS: same-reference scaled initial constraints, correlation, negative controls and finite-ball scope')
