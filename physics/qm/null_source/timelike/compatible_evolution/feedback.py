"""Directed actual-state feedback bounds and the first regularity increment."""
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
def box(p):return iv.mpf([I(p[0]).a,I(p[1]).b])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compute():
    state=json.loads((HERE/'state_norms.json').read_text())
    principal=json.loads((HERE.parent/'prepared_dynamics/principal.json').read_text())
    assert state['status']==principal['status']=='PASS'
    N0=I(state['N0_upper'][1]);S1=I(state['S1_upper'][1])
    S=I(state['S_upper'][1]);S2=I(state['S2_upper'][1])
    N10=I(state['weighted_n_upper'][1]);q0=box(state['q0'])
    z2=iv.pi**2/6;z4=iv.pi**4/90
    # Independent integral-test enclosure of zeta(3).
    z3partial=sum((I(1)/k**3 for k in range(1,1025)),I(0))
    z3=top(z3partial+I(Q(1,2*1024**2)))
    assert upper(z3)<Q(1202057,1000000)
    lam=32768;a0=iv.sqrt(I(3))*lam;a02=I(3*lam**2)
    C0=19+15*(iv.log(a02/4)+2*iv.euler)
    c=1/(8*iv.pi**2);D=I(3);F=I(1);Qmax=I(2)
    certified=next(w for w in principal['windows'] if w['T']=='1/2097152')
    assert Q(certified['inverse_bound'][1])<75
    M=I(75)
    rows=[]
    for power in [21,40]:
        T=I(Q(1,2**power));H=D*T;E=iv.exp(2*H*T);ell=D*T*T/2
        A=a02*iv.exp(2*ell);B=iv.exp(2*ell)/a02
        amax=a0*iv.exp(ell);Lh=E*T*T/2;Lell=E*T**3/6
        rapid=F*T/4;rT=(T*T/6)/(1-T*T/6)
        NT=N0+iv.exp(2*rapid)*(F*T*S1/2+F*F*T*T*(2*N0+z4)/16)
        Z2=z2+2*N0;Z4=z4+2*N0;Z3=z3+2*N0
        Ln=2*iv.exp(3*rapid)*(T*Z2/4+F*T*T*Z4/4+F*T**3*Z3/8)
        JT=T*T/2*(I(Q(1,2))-iv.log(2*T)+rT)
        AT=(Qmax*z2+2*NT)*T+Qmax*JT+Qmax**2*z3*T*T/8+Qmax**2*z2*T**3/6
        BT=T*T*z2+T*JT+3*Qmax*z3*T**3/4+Qmax*z2*T**4/3+2*NT*(T*T+T**3/2)+2*T*Ln
        Lreg=T*T*S1/(2*iv.pi**2)+(AT+F*BT)/(4*iv.pi**2)
        LP=c*T*(1-iv.log(2*T)+rT)+T*Lreg
        Pmax=(S+3*top(q0*q0)*z3/16)/(2*iv.pi**2)+F*LP
        M2max=I(28*lam**4)
        components={
          'regular_quantum_response':Lreg,
          'two_h_P':2*(Pmax*Lh+H*LP),
          'AE_regular_J':((abs(60-4*C0)+120*ell)*(Qmax*Lh+H*T)
                        +120*H*Qmax*Lell+56*(1+H*H)*Lh)/(480*iv.pi**2),
          'Einstein_integral':3*A*T*T+(Qmax/2)*A*E*T**4,
          'fixed_M2_integral':M2max*B*E*T**4/6,
          'geometric_anomaly_integral':(D*T*T+I(Q(2,3))*H*E*(D+1+H*H)*T**3)/(16*iv.pi**2),
          'variable_AE_contact':c*(ell+F*Lell),
          # Driver here means the acceleration defect mathcal F, not a field.
          # This is a conditional cap ||mathcal F||_L1 <= 1, not a constructed protocol.
          'driver_geometry_for_L1_cap_1':amax*E*T**3}
        total=sum(components.values(),I(0));kappa=top(M*total)
        assert upper(kappa)<Q(165,1000)
        # A hypothetical ball f in [-1,1] automatically satisfies the geometry domain.
        qmax=I(state['q0'][1])+T
        assert upper(qmax)<2 and upper(1+qmax+(D*T)**2)<3
        N1T=N10+iv.exp(2*rapid)*(F*T*S1/2+F*F*T*T*(z3+2*N0)/16)
        L0=T*(-iv.log(2*T)+1+rT)
        L2=T**3/3*(-iv.log(2*T)+I(Q(1,3))+rT)
        derivative_kernel=2*Qmax*L0+Qmax**2*L2+(Qmax+I(Q(9,4))*Qmax**2*z3
            +4*iv.sqrt(1+Qmax)*N1T)*T+I(Q(5,4))*Qmax**2*z2*T*T
        derivative_kernel+=Qmax**3*z3*T**3/6+Qmax**3*z2*T**4/12
        initial_derivative=(T*S1+iv.sqrt(1+Qmax)*T*T*S2)/iv.pi**2
        Kv=3*A*E*T*T*(1+H*T/3)*M/(1-kappa)
        rows.append({'T':str(Q(1,2**power)),'inverse_gate':75,
          'Lreg':pair(top(Lreg)),'LP':pair(top(LP)),'Pmax':pair(top(Pmax)),
          'NT':pair(top(NT)),'N1T':pair(top(N1T)),
          'feedback_components':{k:pair(top(v)) for k,v in components.items()},
          'feedback_sum':pair(top(total)),'kappa':pair(kappa),
          'uniform_outward_kappa_gate':'33/200',
          'driver_L1_cap':'1','self_map_forcing_certified':False,
          'geometry_ball_automatic_if_f_ball_holds':True,
          'C1_kernel_derivative_L1':pair(top(derivative_kernel)),
          'C1_initial_coherence_difference':pair(top(initial_derivative)),
          'conditional_shooting_velocity_Lipschitz':pair(top(Kv))})
    sources=[HERE/'state_norms.json',HERE.parent/'prepared_dynamics/principal.json',Path(__file__)]
    return {'schema':'ueot-compatible-full-feedback/1','status':'PASS','windows':rows,
      'scope':{'actual_all_root_initial_state_norms':True,'full_difference_budget':True,
               'constant_M2_through_each_history':True,'C4_bootstrap_conditional_on_actual_C0_solution_and_open_buffer':True,
               'self_mapping_ball_and_forcing':False,'smooth_Hadamard_history':False,
               'later_constraint_shooting_achieved':False,'whole_unified_physics_goal':'OPEN'},
      'zeta3_upper':pair(z3),'source_sha256':{str(p.relative_to(HERE.parent)):sha(p) for p in sources}}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,indent=2,sort_keys=True)+'\n'
    p=HERE/'feedback.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    for w in r['windows']:
        print('PASS: T='+w['T']+' full difference kappa < '+str(float(Q(w['kappa'][1]))))
        print('  regular response',float(Q(w['Lreg'][1])),
              'C1 kernel integral',float(Q(w['C1_kernel_derivative_L1'][1])))
if __name__=='__main__':main()
