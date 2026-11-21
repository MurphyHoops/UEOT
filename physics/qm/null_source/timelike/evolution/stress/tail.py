"""Directed UV certificate from static-matched W2 modes and Bogoliubov mixing."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import sys
import time
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"propagation"))
import background as bg
I,box,Jet=bg.I,bg.box,bg.Jet
TARGETS=(Q(0),Q(3,64),Q(11,64),Q(3,16))

def source_identity():
    paths={"tail.py":HERE/"tail.py",
           "../propagation/background.py":HERE.parent/"propagation/background.py"}
    return {name:hashlib.sha256(path.read_bytes()).hexdigest() for name,path in paths.items()}

LOADED_SOURCE_SHA256=source_identity()

def absI(x): return I(bg.absmax(x))
def topI(x): return I(bg.upper(x))
def botI(x): return I(bg.lower(x))
def exact_fraction(x):
    sign,man,exponent,_=x._mpf_
    return Q((-1 if sign else 1)*man)*(Q(2)**exponent)
def pair(x): return [str(exact_fraction(bg.lower(x))),str(exact_fraction(bg.upper(x)))]
def read_pair(x): return box(Q(x[0]),Q(x[1]))
def cosh(x): return (iv.exp(x)+iv.exp(-x))/2
def sinh(x): return (iv.exp(x)-iv.exp(-x))/2

def power(x,n):
    if n<0:return power(x,-n).inverse()
    out=Jet.const(1,x.n)
    for _ in range(n):out=out*x
    return out

def normalized_defect(q,delta):
    """Generic time/inverse-frequency jets. W2^2=k^2 B, R=k^-4 Rn."""
    q0,q1,q2,q3,q4=q
    A=1+q0*delta
    T=-q2/(4*A)+5*delta*power(q1,2)/(16*power(A,2))
    T1=(-q3/(4*A)+7*delta*q1*q2/(8*power(A,2))
        -5*power(delta,2)*power(q1,3)/(8*power(A,3)))
    T2=(-q4/(4*A)+9*delta*q1*q3/(8*power(A,2))
        +7*delta*power(q2,2)/(8*power(A,2))
        -29*power(delta,2)*power(q1,2)*q2/(8*power(A,3))
        +15*power(delta,3)*power(q1,4)/(8*power(A,4)))
    B=A+power(delta,2)*T
    assert bg.lower(A.c[0])>0 and bg.lower(B.c[0])>0
    Rn=(-T2/(4*B)+delta*q2*T/(4*A*B)
        +5*delta*(2*q1*T1+delta*power(T1,2))/(16*power(B,2))
        -5*power(delta,2)*power(q1,2)*T*(2*A+power(delta,2)*T)
            /(16*power(A,2)*power(B,2)))
    return A,B,T,T1,Rn

def cell_bound(lo,hi,K):
    qv=bg.q_box(lo,hi,5)
    q=[Jet([qv[j],qv[j+1]]) for j in range(5)]
    delta=Jet.const(box(0,Q(1,(K+1)**2)),1)
    A,B,T,T1,Rn=normalized_defect(q,delta)
    # After removing the diagonal term phi'=W+R/(2W).
    # c/(2phi')=k^-6 H; static initial c=0 exactly.
    denom=4*B+2*power(delta,3)*Rn
    phase_positive=bg.lower(denom.c[0])>0
    H=Rn/denom if phase_positive else Jet.const(0,1)
    zden=2*iv.sqrt(botI(B.c[0]))
    rabs=absI(Rn.c[0])
    return {"D5":rabs/zden,"Hprime":absI(H.c[1]),
        "N11":rabs*absI(H.c[0])/zden,"B_lower":botI(B.c[0]),
        "phase_positive":phase_positive,
        "max_q4":absI(qv[4]),"max_q5":absI(qv[5])}

def local_tail(target,K,D5,Hvariation,N11,phase_positive=True,interval_end=None):
    end=target if interval_end is None else interval_end
    assert Q(0)<=target<=end<=Q(3,16)
    tbox=box(target,end)
    qv=bg.q_box(target,end,5)
    dmax=Q(1,(K+1)**2)
    dj=Jet([box(0,dmax),1,0,0])
    qs=[Jet.const(x,3) for x in qv[:5]]
    A,B,T,T1,Rn=normalized_defect(qs,dj)
    h=-iv.tan(2*tbox)
    Bprime=dj*qs[1]+power(dj,2)*T1
    g=Jet.const(h,3)+Bprime/(4*B)
    G=(B+1-dj+dj*power(g,2))/(2*B.sqrt())
    P=(B-(1-dj)/3+dj*power(g,2))/(2*B.sqrt())
    # Interval coefficient 3 bounds the third derivative divided by 3!.
    local_rho=absI(G.c[3])/(2*K*K)
    local_p=absI(P.c[3])/(2*K*K)
    bmin,bmax=botI(B.c[0]),topI(B.c[0])
    gabs,emax=absI(g.c[0]),absI(G.c[0])
    H=Rn/(4*B+2*power(dj,3)*Rn)
    I0=topI(D5)/(K+1)**5
    c1,c2,s1=topI(cosh(I0)),topI(cosh(2*I0)),topI(sinh(I0))
    beta5,ab5=topI(D5)*c1,topI(D5)*c2
    beta6=c1*(absI(H.c[0])+topI(Hvariation))+s1*topI(N11)/(K+1)**5
    ab6=c1*beta6
    Rconst=2*gabs*iv.sqrt(bmax/bmin)
    Rinv=(gabs*gabs+absI(qv[0]+1)+I(dmax)*absI(T.c[0]))/iv.sqrt(bmin)
    Pc=(bmax+I(1)/3+I(dmax)*gabs*gabs
        +2*gabs*iv.sqrt(bmax)/(K+1))/iv.sqrt(bmin)
    estimates={}
    candidates=[(5,beta5,ab5)]
    if phase_positive:candidates.append((6,beta6,ab6))
    for rank,be,ab in candidates:
        diagonal=be*be*emax/((rank-2)*K**(2*rank-4))
        rho_negative=ab*(Rconst/((rank-3)*K**(rank-3))
                                    +Rinv/((rank-2)*K**(rank-2)))
        rho_state=diagonal+rho_negative
        p_state=diagonal+ab*Pc/((rank-4)*K**(rank-4))
        estimates[str(rank)]={"rho_state":pair(rho_state),"p_state":pair(p_state),
             "rho_negative_state":pair(rho_negative),
             "beta_coefficient":pair(be),"alpha_beta_coefficient":pair(ab)}
    rho_state=min(bg.upper(read_pair(v["rho_state"])) for v in estimates.values())
    rho_negative=min(bg.upper(read_pair(v["rho_negative_state"])) for v in estimates.values())
    p_state=min(bg.upper(read_pair(v["p_state"])) for v in estimates.values())
    a=iv.sqrt(3*iv.cos(2*tbox))
    pref=1/(4*iv.pi**2*a**4)
    return {"eta":str(target),"eta_interval":[str(target),str(end)],
        "K":K,"ibp_phase_positive":phase_positive,
        "bogoliubov_rapidity_upper":pair(I0),
        "rho_UV_tail_absolute_bound":pair(topI(pref*(I(rho_state)+local_rho))),
        "rho_UV_tail_lower_bound":pair(-topI(pref*(I(rho_negative)+local_rho))),
        "pressure_UV_tail_absolute_bound":pair(topI(pref*(I(p_state)+local_p))),
        "rho_local_W2_subtraction_tail_bound":pair(pref*local_rho),
        "pressure_local_W2_subtraction_tail_bound":pair(pref*local_p),
        "state_tail_unscaled":estimates,
        "integration_D5":pair(D5),"integration_Hvariation":pair(Hvariation),
        "integration_N11":pair(N11),
        "physical_rho_an":pair(analytic(tbox)[0]),
        "physical_pressure_an":pair(analytic(tbox)[1])}

def analytic(eta,mu=1):
    t=I(eta);c=iv.cos(2*t);L=iv.log(3*c*I(mu)**2/4)+2*iv.euler
    den=8640*iv.pi**2*c**6
    return (((168+180*L)*c*c-110-135*L)/den,
            ((160+300*L)*c*c-240-405*L)/den)

def algebra_checks():
    h,L=sp.symbols("h L",real=True);q=1+h*h
    R=-q*((135*L+110)*h*h-45*L-58)/960
    P=-q*((81*L+48)*h*h+21*L+16)/192
    assert sp.factor(-2*q*sp.diff(R,h)+2*h*sp.diff(R,L)+h*(-R+3*P))==0
    z=sp.symbols("z");q0,q1,q2,hh=sp.symbols("q0 q1 q2 hh")
    B=1+q0*z-q2*z*z/4;bp=q1*z;g=hh+bp/(4*B)
    G=(B+1-z+z*g*g)/(2*sp.sqrt(B))
    P=(B-(1-z)/3+z*g*g)/(2*sp.sqrt(B))
    e1=(hh*hh-1)/2
    e3=(q0*q0-2*(hh*hh-1)*q0+2*hh*q1)/8
    p1=q0/3+hh*hh/2+sp.Rational(1,6)
    p3=-q0*q0/8-q2/12-(3*hh*hh+1)*q0/12+hh*q1/4
    assert sp.simplify(sp.series(G,z,0,3).removeO()-1-e1*z-e3*z*z)==0
    assert sp.simplify(sp.series(P,z,0,3).removeO()-sp.Rational(1,3)-p1*z-p3*z*z)==0

def mesh(step):
    cuts=sorted(set(bg.BREAKS+TARGETS+(Q(0),)))
    cells=[]
    for a,b in zip(cuts,cuts[1:]):
        local_step=max(step,Q(1,512)) if a>=bg.STOP else step
        n=max(1,math.ceil((b-a)/local_step))
        for j in range(n):
            cells.append((a+(b-a)*Q(j,n),a+(b-a)*Q(j+1,n)))
    return cells

def certificate(K=64,subdivisions=1024,progress=False):
    if not __debug__:raise RuntimeError("Do not use -O: proof assertions are required.")
    assert isinstance(K,int) and K>=2 and isinstance(subdivisions,int) and subdivisions>0
    assert source_identity()==LOADED_SOURCE_SHA256,"source changed after import"
    algebra_checks()
    cells=mesh(Q(1,16*subdivisions))
    D5,Hvar,N11=I(0),I(0),I(0)
    Bmin=I(1);max4=I(0);max5=I(0);rows=[];phase_positive=True;phase_failure=None
    for index,(lo,hi) in enumerate(cells):
        b=cell_bound(lo,hi,K);width=I(hi-lo)
        if not b["phase_positive"]:
            phase_positive=False
            if phase_failure is None:phase_failure=[str(lo),str(hi)]
        D5+=width*b["D5"];Hvar+=width*b["Hprime"];N11+=width*b["N11"]
        if bg.lower(b["B_lower"])<bg.lower(Bmin):Bmin=b["B_lower"]
        if bg.upper(b["max_q4"])>bg.upper(max4):max4=b["max_q4"]
        if bg.upper(b["max_q5"])>bg.upper(max5):max5=b["max_q5"]
        if hi in TARGETS:
            rows.append(local_tail(hi,K,D5,Hvar,N11,phase_positive))
            if progress:print("target",str(hi),"rho bound",rows[-1]["rho_UV_tail_absolute_bound"],
                              "p bound",rows[-1]["pressure_UV_tail_absolute_bound"],flush=True)
        if progress and index%256==0:print("cells",index,"/",len(cells),flush=True)
    uniform=local_tail(Q(0),K,D5,Hvar,N11,phase_positive,interval_end=Q(3,16))
    assert source_identity()==LOADED_SOURCE_SHA256,"source changed during proof computation"
    return {"method":"static_matched_W2_residual_Bogoliubov_plus_oscillatory_IBP",
        "interval_encoding":"exact_binary_endpoints_as_rational_strings",
        "source_sha256":dict(LOADED_SOURCE_SHA256),
        "base":"987dd4ccc58d0086cc1305e99b5cdb67f8127fde","K":K,
        "preparation_subdivisions":subdivisions,"cells":len(cells),
        "ibp_first_unverified_phase_cell":phase_failure,
        "B_uniform_lower":pair(Bmin),"q4_uniform_abs_bound":pair(max4),
        "q5_uniform_abs_bound":pair(max5),"targets":rows,
        "uniform_physical_UV_tail":uniform,
        "background_sha256":hashlib.sha256((HERE.parent/"propagation/background.py").read_bytes()).hexdigest(),
        "finite_mode_stress_included":False}

if __name__=="__main__":
    if not __debug__:raise SystemExit("Do not use -O: proof assertions are required.")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--K",type=int,default=64)
    parser.add_argument("--mesh",type=int,default=1024)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument("--write",action="store_true")
    mode.add_argument("--check",action="store_true")
    parser.add_argument("--progress",action="store_true")
    args=parser.parse_args();start=time.monotonic()
    result=certificate(args.K,args.mesh,progress=args.progress)
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    path=HERE/f"tail_K{args.K}_M{args.mesh}.json"
    if args.write:path.write_text(rendered)
    if args.check:assert rendered==path.read_text(),"UV certificate recomputation mismatch"
    for row in result["targets"]:
        print("eta",row["eta"],"rho UV lower",float(bg.lower(read_pair(row["rho_UV_tail_lower_bound"]))),
              "rho UV abs upper",float(bg.upper(read_pair(row["rho_UV_tail_absolute_bound"]))),
              "p UV abs upper",float(bg.upper(read_pair(row["pressure_UV_tail_absolute_bound"]))))
    print("PASS: recomputed directed UV certificate",args.K,args.mesh,
          "seconds",time.monotonic()-start,flush=True)
