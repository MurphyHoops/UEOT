"""A positive-window later-release construction from the actual all-root state."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json
from mpmath import iv
from mpmath.libmp import to_rational
iv.dps=70
HERE=Path(__file__).resolve().parent
def I(x):
    x=Q(x);return iv.mpf(x.numerator)/x.denominator
def lower(x):return Q(*to_rational(x._mpi_[0]))
def upper(x):return Q(*to_rational(x._mpi_[1]))
def top(x):return I(upper(x))
def pair(x):return [str(lower(x)),str(upper(x))]
def box(a,b):return iv.mpf([I(a).a,I(b).b])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compute():
    state=json.loads((HERE/'state_norms.json').read_text())
    feedback=json.loads((HERE/'feedback.json').read_text())
    initial=json.loads((HERE.parent/'prepared_initial/result.json').read_text())
    recent=json.loads((HERE.parent/'prepared_dynamics/result.json').read_text())
    assert all(x['status']=='PASS' for x in [state,feedback,initial,recent])
    row=next(w for w in feedback['windows'] if w['T']=='1/1099511627776')
    T=I(Q(1,2**40));rho=I(Q(1,16));M=I(75);lam=32768
    radius=Q(recent['root_tightening']['all_prior_roots_absolute_bound'][1])
    theta=box(-radius,radius);q0=1-theta
    t=box(0,Q(1,2**40));sec2=1/iv.cos(2*t)**2;tan=iv.sin(2*t)/iv.cos(2*t)
    href=-tan+theta*t;h1=-2*sec2+theta;h2=-8*sec2*tan
    h3=-32*sec2*tan*tan-16*sec2*sec2
    q2=-h3-2*h1*h1-2*href*h2
    assert lower(q2)>7 and upper(q2)<9
    Fref=9*T;Dgeom=I(3);H=Dgeom*T;ell=Dgeom*T*T/2
    E=iv.exp(2*H*T);a02=I(3*lam**2);Ametric=a02*iv.exp(2*ell)
    Bmetric=iv.exp(2*ell)/a02;c=1/(8*iv.pi**2)
    C0=19+15*(iv.log(a02/4)+2*iv.euler);Cmax=top(abs(C0)+30*ell)
    rT=(T*T/6)/(1-T*T/6)
    Pmax=I(row['Pmax'][1]);Lreg=I(row['Lreg'][1])
    # Actual constant-q evolution is only a Wick-square comparison, not a new state.
    # Every root's instantaneous C0 is bounded by the certified finite boxes and tail.
    S3finite=I(state['zero_mode']['C_upper'][1])
    for mode in state['modes']:S3finite+=mode['k']**3*I(mode['C_abs_upper'])
    b4=I(state['UV']['beta4'][1]);b5=I(state['UV']['beta5'][1])
    beta=top(b4/513**4+b5/513**5);factor=iv.sqrt(1+beta*beta)
    K=2**40
    Hfinite=2*iv.sqrt(I(3))*T*S3finite/iv.pi**2
    Htail=factor*(b4*(2*iv.sqrt(I(3))*T*iv.log(I(Q(K,512)))+I(Q(2,K)))
                 +2*iv.sqrt(I(3))*T*b5/512)/iv.pi**2
    singular=c*9*T*(1-iv.log(2*T)+rT)
    Pprime_delta=top(Hfinite+Htail+singular+Lreg*Fref)
    Jbound=2*Cmax*Fref+(abs(60-4*C0)+120*ell)*H*2+56*H+I(Q(56,3))*H**3
    Qrho=I(initial['absolute_stress']['Qrho_absolute_integer_bound'])
    assert upper(Qrho)==508
    # M2=27 lambda^4-54 lambda^2 Qrho, fixed once at the old initial root.
    # The O(lambda^2) terms cancel at t=0 before absolute values are taken.
    I0bound=36*Qrho+18*lam**2*I(radius)
    dloga=ell
    dq=I(Q(9,2))*T*T
    M2max=I(28*lam**4)
    Einstein_change=6*Ametric*dq+12*a02*iv.exp(2*ell)*2*dloga
    fixed_source_change=4*M2max*Bmetric*dloga
    anomaly=(Dgeom**2+(1+H*H)**2)/(16*iv.pi**2)
    integrated=top(T*(I0bound+Einstein_change+fixed_source_change+anomaly))
    pieces={'initial_coherence_finite':Hfinite,'initial_coherence_infinite_tail':Htail,
            'principal_reference_term':singular,'regular_reference_change':Lreg*Fref,
            'two_h_P':2*H*Pmax,'AE_J':Jbound/(480*iv.pi**2),
            'Einstein_source_and_anomaly_integral':integrated}
    D=top(sum(pieces.values(),I(0)))
    assert upper(D)<Q(1,6400)
    amplitude=3*D
    # Fixed smooth F_alpha=H_alpha'/(6 a_ref); actual trace source is integral r H_alpha'.
    driver_lip=top(iv.exp(2*ell)*E*(D+amplitude)*(T**3/3+Dgeom*T**5/15))
    base_lip=sum((I(v[1]) for k,v in row['feedback_components'].items()
                  if k!='driver_geometry_for_L1_cap_1'),I(0))
    kappa=top(M*(base_lip+driver_lip))
    assert upper(kappa)<Q(1,4)
    selfmap_margin=(1-kappa)*rho-M*(D+amplitude)
    assert lower(selfmap_margin)>0
    assert upper(Fref+rho)<1
    qlo=1-I(radius)-(Fref+rho)*T
    qhi=1+I(radius)+(Fref+rho)*T
    assert lower(qlo)>Q(9,10) and upper(qhi)<Q(11,10)
    assert upper(iv.exp(2*ell))<Q(101,100) and lower(iv.exp(-2*ell))>Q(99,100)
    # Fixed-buffer interval [0,T/4]; chi ends at T/2; Psi rises on [T/2,3T/4].
    # g=a'/a_ref has |g'|<=3 and g<=-9T/10 on supp(Psi').
    assert upper(I(Q(101,100))*(1+qhi+H*H+2*H*H))<3
    assert lower(I(Q(99,100))*I(Q(19,10))*T/2)>Q(9,10)*upper(T)
    endpoint_margin=I(Q(2,5))*D*T-450*D*D*T*T
    monotone_margin=(I(Q(9,10))*T-3150*D*T*T)/3
    assert lower(endpoint_margin)>0 and lower(monotone_margin)>0
    assert upper(1200*D*T**3)<Q(1,1000000)
    clock=iv.sqrt(a02)*T/4*iv.exp(box(-upper(ell),upper(ell)))
    sources=[HERE/'state_norms.json',HERE/'feedback.json',
             HERE.parent/'prepared_initial/result.json',HERE.parent/'prepared_dynamics/result.json',
             HERE/'REGULARITY.md',Path(__file__)]
    return {'schema':'ueot-later-release-construction/1','status':'PASS',
      'T':'1/1099511627776','fixed_buffer_end':'1/4398046511104',
      'driver_release':'3/4398046511104','post_release_window_length':'1/4398046511104',
      'candidate_ball_radius':'1/16','inverse_gate':75,'reference_qsecond':pair(q2),
      'reference_residual_upper':pair(D),'residual_components':{k:pair(top(v)) for k,v in pieces.items()},
      'control_amplitude_interval':[str(-upper(amplitude)),str(upper(amplitude))],
      'full_feedback_with_fixed_driver':pair(kappa),'self_mapping_margin':pair(selfmap_margin),
      'shooting_endpoint_margin':pair(endpoint_margin),'shooting_monotonicity_margin':pair(monotone_margin),
      'fixed_driver_geometry_Lipschitz':pair(driver_lip),
      'proper_duration_post_release_model_units':pair(clock),
      'S3_finite_only':pair(top(S3finite)),
      'scope':{'all_prior_initial_roots':True,'same_actual_full_initial_kernel':True,
               'M2_fixed_once':True,'one_common_geometry_and_state_after_release':True,
               'existence_by_contraction_and_strict_shooting':True,
               'numerical_trajectory_or_alpha_value_computed':False,
               'regularity_analytic_proof':'REGULARITY.md',
               'smooth_Hadamard_post_release_history':True,
               'proof_status':'analytic proof plus directed interval certificate; research candidate',
               'immediate_undriven_extension':False,'original_no_go_preserved':True,
               'physical_controller_constructed':False,'long_time_or_global_existence':False,
               'whole_unified_physics_goal':'OPEN'},
      'source_sha256':{str(p.relative_to(HERE.parent)):sha(p) for p in sources}}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,indent=2,sort_keys=True)+'\n'
    p=HERE/'history.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    for k in ['reference_residual_upper','full_feedback_with_fixed_driver','self_mapping_margin',
              'shooting_endpoint_margin','shooting_monotonicity_margin']:
        print(k,float(Q(r[k][1])))
    print('PASS: actual-state fixed-source later-release existence inequalities')
if __name__=='__main__':main()
