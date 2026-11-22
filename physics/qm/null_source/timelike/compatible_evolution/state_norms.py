"""Actual centered prepared-state norms, including zero mode and infinite UV tail."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json
from mpmath import iv
from mpmath.libmp import to_rational
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
iv.dps=70

def I(x):
    x=Q(x)
    return iv.mpf(x.numerator)/x.denominator
def lower(x):return Q(*to_rational(x._mpi_[0]))
def upper(x):return Q(*to_rational(x._mpi_[1]))
def box(a,b):return iv.mpf([I(a).a,I(b).b])
def pair(x):return [str(lower(x)),str(upper(x))]
def read_pair(p):return box(Q(p[0]),Q(p[1]))
def top(x):return I(upper(x))
def absolute(x):return I(max(abs(lower(x)),abs(upper(x))))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())

def compute():
    paths=[TIMELIKE/'evolution/propagation/result.json',
           TIMELIKE/'evolution/propagation/extra_eta0_256.json',
           TIMELIKE/'prepared_dynamics/modes_257_512.json']
    modes=[]
    for p in paths:modes.extend(load(p)['targets']['0']['modes'])
    assert [r['k'] for r in modes]==list(range(2,513))
    old=load(TIMELIKE/'prepared_initial/result.json')
    recent=load(TIMELIKE/'prepared_dynamics/result.json')
    assert old['status']==recent['status']=='PASS'
    radius=Q(recent['root_tightening']['all_prior_roots_absolute_bound'][1])
    theta=box(-radius,radius)
    q0=1-theta
    H=top(read_pair(old['finite_modes']['original_log_energy_bound']))
    change=top(iv.exp(H)*(iv.exp(I(radius)/64)-1))
    # At eta=0 all family members have A=sqrt(3), h=0.
    # The archived energy frame uses omega=sqrt(k^2-1).
    finite_N=I(0);finite_C=I(0);finite_S=I(0);finite_C2=I(0);finite_N1=I(0)
    rows=[]
    for row in modes:
        k=row['k'];omega=iv.sqrt(I(k*k-1));Omega=iv.sqrt(k*k+q0)
        u=[I(Q(x)) for x in row['u_center']]
        p=[I(Q(x)) for x in row['p_center']]
        vv=3*(u[0]**2+u[1]**2)
        ww=(p[0]**2+p[1]**2)/3
        norm=iv.sqrt(Omega*vv+ww/Omega)
        eps=iv.sqrt(Omega/omega)*(I(Q(row['norm_error_radius']))+change)
        error=top(norm*eps+eps*eps/2)
        n=I(max(Q(0),upper((Omega*vv+ww/Omega-1)/2+error)))
        cr=(Omega*vv-ww/Omega)/2
        ci=u[0]*p[0]+u[1]*p[1]
        coherence=top(iv.sqrt(cr*cr+ci*ci)+error)
        finite_N+=n;finite_C+=k*coherence;finite_S+=k*(n+coherence)
        finite_C2+=k*k*coherence;finite_N1+=k*n
        rows.append({'k':k,'n_upper':str(upper(n)),'C_abs_upper':str(upper(coherence))})
    # Original regular zero-mode seed u=1/sqrt(6), p=-i*sqrt(3/2).
    # u(0)=u(-1/8)+p*integral A_theta^-2; no reset at the physical slice.
    integ=box(lower(I(1)/(24*iv.exp(I(radius)/64))),
              upper(iv.exp(I(radius)/64)/(24*iv.cos(I(Q(1,4))))))
    Omega=iv.sqrt(1+q0)
    vv=I(Q(1,2))+I(Q(9,2))*integ*integ
    ww=I(Q(1,2));ci=I(Q(3,2))*integ
    zn=top((Omega*vv+ww/Omega-1)/2)
    zc=top(iv.sqrt(((Omega*vv-ww/Omega)/2)**2+ci*ci))
    assert lower(zn)>0
    # Convert the already certified static-matched W2 state to instantaneous modes.
    N=512;d=box(0,Q(1,513**2));q2=8+8*theta-2*theta**2
    A=1+q0*d;B=A-q2*d*d/(4*A)
    assert lower(A)>0 and lower(B)>0
    cm=top(absolute(q2)/(8*A*(iv.sqrt(A)+iv.sqrt(B))*iv.sqrt(iv.sqrt(A*B))))
    D5=top(read_pair(old['new_uniform_uv']['D5']))
    rapidity=D5/513**5
    ch=(iv.exp(rapidity)+iv.exp(-rapidity))/2
    b4=top(cm*ch)
    b5=top(iv.sqrt(1+(cm/513**4)**2)*D5*ch)
    beta_max=top(b4/513**4+b5/513**5)
    ctail=top(iv.sqrt(1+beta_max**2)*(b4/(2*N**2)+b5/(3*N**3)))
    c2tail=top(iv.sqrt(1+beta_max**2)*(b4/N+b5/(2*N**2)))
    ntail=top(b4*b4/(7*N**7)+b4*b5/(4*N**8)+b5*b5/(9*N**9))
    nweighted=top(b4*b4/(6*N**6)+2*b4*b5/(7*N**7)+b5*b5/(8*N**8))
    total_N=top(finite_N+zn+ntail)
    total_C=top(finite_C+zc+ctail)
    total_S=top(finite_S+zn+zc+ctail+nweighted)
    total_C2=top(finite_C2+zc+c2tail)
    total_N1=top(finite_N1+zn+nweighted)
    # Deliberately coarse reusable gates; precise enclosures are retained.
    assert upper(total_N)<100 and upper(total_C)<100 and upper(total_S)<100
    assert upper(total_C2)<14000 and upper(total_N1)<100, (float(upper(total_C2)),float(upper(total_N1)),float(upper(D5)))
    paths += [TIMELIKE/'prepared_initial/result.json',TIMELIKE/'prepared_dynamics/result.json',
              TIMELIKE/'instrument/instrument.py',Path(__file__)]
    return {'schema':'ueot-compatible-state-norms/1','status':'PASS',
      'theta_all_initial_roots':pair(theta),'q0':pair(q0),
      'N0_upper':pair(total_N),'S1_upper':pair(total_C),'S_upper':pair(total_S),
      'S2_upper':pair(total_C2),'weighted_n_upper':pair(total_N1),
      'finite':{'N0':pair(finite_N),'S1':pair(finite_C),'S':pair(finite_S),'S2':pair(finite_C2),'weighted_n':pair(finite_N1)},
      'zero_mode':{'past_integral':pair(integ),'n_upper':pair(zn),'C_upper':pair(zc)},
      'UV':{'instantaneous_basis_d4':pair(cm),'D5_reused':pair(D5),'beta4':pair(b4),'beta5':pair(b5),
            'N0_tail':pair(ntail),'S1_tail':pair(ctail),'S2_tail':pair(c2tail),'weighted_n_tail':pair(nweighted)},
      'parameter_energy_frame_radius':pair(change),'modes':rows,
      'mode_integrations_performed':0,'past_integrals_evaluated_numerically':0,
      'scope':{'actual_all_root_centered_prepared_states':True,
               'classical_displacement_M2_is_separate':True,'new_release_state_constructed':False,
               'initial_slice_existence_reused':True,'prior_nonextension_preserved':True},
      'source_sha256':{str(p.relative_to(TIMELIKE)):sha(p) for p in paths}}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,sort_keys=True,indent=2)+'\n'
    p=HERE/'state_norms.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    print('PASS: all-root actual centered-state norms; zero mode and infinite UV tail')
    for k in ['N0_upper','S1_upper','S_upper','S2_upper','weighted_n_upper']:print(k,float(Q(r[k][1])))
if __name__=='__main__':main()
