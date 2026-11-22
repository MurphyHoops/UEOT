"""Parameter sensitivity of phase-preserving Born polynomials on the root family."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import argparse,hashlib,json,time
import sympy as sp
import phase_extension as ext
pq=ext.pq;pb=pq.pb;initial=pq.initial
bg,old,iv=pq.bg,pq.old,pq.iv
I,box,Jet=pq.I,pq.box,pq.Jet
HERE=Path(__file__).resolve().parent
RADIUS=Q(15933,67108864)

def parameter_q(lo,hi,radius):
    parameter=box(-radius,radius)
    base=bg.q_box(lo,hi,4)
    psi=initial.time_jet(lo,hi,6);psi=psi*psi*initial.smooth_step(lo,hi,6)/2
    psi1=Jet([(j+1)*psi.c[j+1] for j in range(5)])
    psi2=Jet([(j+1)*(j+2)*psi.c[j+2] for j in range(5)])
    a=bg.derivative_box(lo,hi,5)
    h=Jet([(j+1)*a.c[j+1] for j in range(5)])/Jet(a.c[:5])
    L=psi2+2*h*psi1;B=psi1*psi1
    return [Jet([base[j]-(L.c[j]*parameter+B.c[j]*parameter**2)*factorial(j),
                 -(L.c[j]+2*B.c[j]*parameter)*factorial(j)]) for j in range(5)]

def param_prefactors(radius):
    theta,d=sp.symbols('theta d')
    q=1-theta;q2=8+8*theta-2*theta**2
    A=1+q*d;T=-q2/(4*A);B=A+d*d*T
    P=(B+(1-d)/3)/sp.sqrt(B)
    R=(q+1+d*T)/sp.sqrt(B)
    tjet=Jet([box(-radius,radius),1])
    def eval_poly(expr):
        out=Jet.const(0,1)
        for c in sp.Poly(sp.expand(expr),theta).all_coeffs():out=out*tjet+I(Q(str(c)))
        return out
    polys=[[eval_poly(sp.diff(expr,d,j).subs(d,0)/factorial(j)) for j in range(5)] for expr in [P,R]]
    return [[Jet.const(x,1) for x in [1,-1,0,0,0]],*polys]

def compute(radius=RADIUS,N=512,progress=False):
    pref=param_prefactors(radius)
    future=[Jet.const(0,1) for _ in range(5)]
    constants=[I(0),I(0),I(0)]
    cells=list(reversed(initial.mesh()));start=time.monotonic()
    for index,(lo,hi) in enumerate(cells):
        q=parameter_q(lo,hi,radius)
        fs=ext.sources(q);width=I(hi-lo)
        values=[v+f*box(0,hi-lo) for v,f in zip(future,fs)]
        phases=[values[0]/2,(q[1]-values[1])/8,
                (-q[3]-6*q[0]*q[1]-values[2]+2*values[3])/32,values[4]]
        F=ext.coefficients_from_phase(q,phases,pref)
        if lo>=bg.STOP:
            q4param=parameter_q(lo,Q(0),radius)[4].c[1]
            amp=pq.absI(q4param)*I(-lo)/iv.sin(I(-lo))
        else:
            amp=pq.absI(q[3].c[1]/iv.sin(box(lo,hi)))
        constants[0]+=width*amp/32
        constants[0]+=width*sum((pq.absI(F[0][j].c[1])*I(Q(1,j*N**j)) for j in range(1,9)),I(0))
        for kind,offset in [(1,2),(2,4)]:
            constants[kind]+=width*sum((pq.absI(F[kind][j].c[1])*I(Q(1,(j+offset-1)*N**(j+offset-1))) for j in range(9)),I(0))
        future=[v+f*width for v,f in zip(future,fs)]
        if progress and index%256==0:print('Phase parameter cells',index,len(cells),flush=True)
    factors=[2/(27*iv.pi**2),1/(36*iv.pi**2),1/(36*iv.pi**2)]
    return {'schema':'ueot-prepared-phase-parameter/1','status':'PASS','radius':str(radius),'N':N,'J':8,'cells':len(cells),
      'born_polynomial_lipschitz':{k:old.pair(pq.top(v*p)) for k,v,p in zip(['pressure_derivative','pressure','density'],constants,factors)},
      'source_identity':{Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
      'semantics':'Lipschitz constants of explicit Born polynomial only; exact UV remainder is enclosed separately, once around the zero-parameter proxy.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();result=compute(progress=True);rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/'phase_sensitivity.json'
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    for k,v in result['born_polynomial_lipschitz'].items():print(k,float(bg.upper(old.read_pair(v))),flush=True)
if __name__=='__main__':main()
