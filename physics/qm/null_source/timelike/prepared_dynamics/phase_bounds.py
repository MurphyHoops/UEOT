"""All-mode W2 phase expansion and parameter sensitivity, directed intervals."""
from fractions import Fraction as Q
from math import factorial
import argparse,hashlib,json,sys,time
from pathlib import Path
from mpmath import iv,mp
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"prepared_initial"))
import check as initial
bg=initial.bg;old=initial.old_tail
I,box,Jet=bg.I,bg.box,bg.Jet
pw=old.power
iv.dps=55;mp.dps=65

def shift_q(lo,hi,parameter):
    return initial.family_q_box(lo,hi,parameter,4)

def frequency_data(qv,z):
    d=z*z
    q=[Jet.const(v,z.n) for v in qv]
    A,B,T,T1,Rn=old.normalized_defect(q,d)
    r=Rn/(2*B.sqrt())
    phase=(q[0]*z+T*pw(z,3))/(B.sqrt()+1)+r*pw(z,5)
    return B,T,r,phase

def parameter_data(lo,hi,parameter,N):
    base=bg.q_box(lo,hi,4)
    psi=initial.time_jet(lo,hi,6)
    psi=psi*psi*initial.smooth_step(lo,hi,6)/2
    psi1=Jet([(j+1)*psi.c[j+1] for j in range(5)])
    psi2=Jet([(j+1)*(j+2)*psi.c[j+2] for j in range(5)])
    a=bg.derivative_box(lo,hi,5)
    h=Jet([(j+1)*a.c[j+1] for j in range(5)])/Jet(a.c[:5])
    L=psi2+2*h*psi1
    Bpsi=psi1*psi1
    qv=[Jet([base[j]-(L.c[j]*parameter+Bpsi.c[j]*parameter**2)*factorial(j),
             -(L.c[j]+2*Bpsi.c[j]*parameter)*factorial(j)]) for j in range(5)]
    d=Jet.const(box(0,Q(1,(N+1)**2)),1)
    A,B,T,T1,Rn=old.normalized_defect(qv,d)
    r=Rn/(2*B.sqrt())
    dr=initial.absolute(r.c[1])
    lp=initial.absolute((qv[0].c[1]+d.c[0]*T.c[1])/(2*iv.sqrt(B.c[0]))+d.c[0]**2*r.c[1])
    return dr,lp

def compute(radius=Q(0),N=512,J=6,progress=False):
    parameter=box(-radius,radius)
    z=Jet([box(0,Q(1,N+1)),1]+[0]*J)
    q0=shift_q(Q(0),Q(0),parameter)
    B0,T0,r0,p0=frequency_data(q0,z)
    P=(B0+(1-z*z)/3)/B0.sqrt()
    R=(z*z*T0+(q0[0]+1))/B0.sqrt()
    future=Jet.const(0,J+1)
    Md=I(0);Mp=I(0);Mr=I(0);Dr=I(0);Lphi=I(0);D5=I(0)
    cells=list(reversed(initial.mesh()))
    start=time.monotonic()
    for index,(lo,hi) in enumerate(cells):
        qv=shift_q(lo,hi,parameter)
        B,T,r,ph=frequency_data(qv,z)
        width=I(hi-lo)
        interval_phase=future+ph*box(0,hi-lo)
        sn,cs=(2*interval_phase).sincos()
        Fd=r*(1-z*z)
        Fp=r*P
        Fr=r*R
        def coeff_bound(f):
            return initial.absolute((f*cs).c[J+1])+initial.absolute((f*sn).c[J+1])
        Md+=width*coeff_bound(Fd)
        Mp+=width*coeff_bound(Fp)
        Mr+=width*coeff_bound(Fr)
        future=future+ph*width
        D5+=width*initial.absolute(r.c[0])
        dr,lp=parameter_data(lo,hi,parameter,256)
        Dr+=width*dr;Lphi+=width*lp
        if progress and index%256==0:print('Phase bound cells',index,len(cells),flush=True)
    cder=2/(27*iv.pi**2);cm=1/(36*iv.pi**2)
    return {'schema':'ueot-prepared-phase-bounds/1','status':'PASS','N':N,'J':J,'radius':str(radius),
      'cells':len(cells),'D5':old.pair(D5),'Dr_above_256':old.pair(Dr),'Lphi_above_256':old.pair(Lphi),
      'taylor_remainder_derivative':old.pair(initial.top(cder*Md/((J+1)*N**(J+1)))),
      'taylor_remainder_pressure':old.pair(initial.top(cm*Mp/((J+2)*N**(J+2)))),
      'taylor_remainder_density':old.pair(initial.top(cm*Mr/((J+4)*N**(J+4)))),
      'integrated_next_coefficient':{'derivative':old.pair(Md),'pressure':old.pair(Mp),'density':old.pair(Mr)},
      'phase_future_coefficients':[old.pair(x) for x in future.c]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',default='0');ap.add_argument('--N',type=int,default=512);ap.add_argument('--J',type=int,default=6)
    ap.add_argument('--output',default='phase_bounds_zero.json');ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();data=compute(Q(args.radius),args.N,args.J,True)
    rendered=json.dumps(data,indent=2,sort_keys=True)+'\n';path=HERE/args.output
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    for key in ['D5','Dr_above_256','Lphi_above_256','taylor_remainder_derivative','taylor_remainder_pressure','taylor_remainder_density']:
        print(key,float(bg.upper(old.read_pair(data[key]))),flush=True)
if __name__=='__main__':main()
