"""Certified inverse-frequency terms seven and eight of the actual Born tail."""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import argparse,hashlib,json,time
import phase_quadrature as pq
I,box,Jet=pq.I,pq.box,pq.Jet
bg,old,iv=pq.bg,pq.old,pq.iv
HERE=Path(__file__).resolve().parent

def w7(qs):
    q,q1,q2,q3,q4=qs
    return -5*q*q*q*q/128-15*q*q*q2/64-25*q*q1*q1/64-5*q*q4/64-7*q1*q3/32-19*q2*q2/128

def r4(qs):
    q,q1,q2,q3,q4=qs
    return (1155*q*q*q*q*q4/4096+1617*q*q*q*q1*q3/512+2079*q*q*q*q2*q2/1024
      +2673*q*q*q1*q1*q2/256+297*q*q*q2*q4/2048+495*q*q*q3*q3/4096
      +1485*q*q1*q1*q1*q1/512+165*q*q1*q1*q4/2048+957*q*q1*q2*q3/1024
      +297*q*q2*q2*q2/1024+45*q1*q1*q1*q3/256+297*q1*q1*q2*q2/512
      +15*q2*q2*q4/4096+25*q2*q3*q3/4096)

def sources(q):return pq.primitive_sources(q)+[w7(q)]

def prefactors(radius):
    d=Jet([0,1,0,0,0])
    vals=pq.actual_q(Q(0),Q(0),radius,4)
    q=[Jet.const(v,4) for v in vals]
    A,B,T,T1,Rn=old.normalized_defect(q,d)
    P=(B+(1-d)/3)/B.sqrt();R=(d*T+(vals[0]+1))/B.sqrt()
    return [I(1),I(-1),I(0),I(0),I(0)],P.c,R.c

def coefficients_from_phase(q,phases,pref):
    # exp(i*sum(2 Phi_j z^(2j+1))); even entries are real, odd imaginary.
    degree=q[0].n
    ex=[Jet.const(1,degree)]
    for n in range(1,9):
        value=sum(((2*j+1)*2*phases[j]*ex[n-(2*j+1)] for j in range(min(3,(n-1)//2)+1)),Jet.const(0,degree))/n
        ex.append(value if n%2 else -value)
    r=pq.r_coefficients(q)+[r4(q)]
    results=[]
    for p in pref:
        amp=[sum((r[k-j]*p[j] for j in range(k+1)),Jet.const(0,degree)) for k in range(5)]
        results.append([sum((amp[k]*ex[j-2*k] for k in range(j//2+1)),Jet.const(0,degree)) for j in range(9)])
    return results

def coefficients(q,values,pref):
    integ=[pq.integral_jet(v,f) for v,f in zip(values,sources(q))]
    phases=[integ[0]/2,(q[1]-integ[1])/8,
            (-q[3]-6*q[0]*q[1]-integ[2]+2*integ[3])/32,integ[4]]
    return coefficients_from_phase(q,phases,pref)

def compute(radius=Q(0),N=512,subdivisions=1024,degree=10,progress=False,limit=None):
    pref=prefactors(radius);end=pq.time_q(-pq.EPS,Q(0),radius,degree)
    fs=sources(end);future=[I(pq.EPS)*x.c[0] for x in fs]
    Fe=coefficients(end,[box(0,pq.EPS)*x.c[0] for x in fs],pref)
    endpoint=[sum((I(pq.EPS)*pq.absI(Fe[kind][j].c[0])*I(Q(1,(j+offset-1)*N**(j+offset-1)))
                  for j in (7,8)),I(0)) for kind,offset in [(0,1),(1,2),(2,4)]]
    sums=[pq.symmetric(e) for e in endpoint];errors=[I(0),I(0),I(0)]
    panels=pq.cells(subdivisions)
    if limit:panels=panels[:limit]
    start=time.monotonic()
    for index,(lo,hi) in enumerate(panels):
        mid=(lo+hi)/2;h=(hi-lo)/2
        qc=pq.time_q(mid,mid,radius,degree);qb=pq.time_q(lo,hi,radius,degree)
        fcs=sources(qc);fbs=sources(qb)
        center=[v+pq.integrate_primitive(fc,fb,h,degree,False) for v,fc,fb in zip(future,fcs,fbs)]
        boxes=[v+box(0,hi-lo)*fb.c[0] for v,fb in zip(future,fbs)]
        Fc=coefficients(qc,center,pref);Fb=coefficients(qb,boxes,pref)
        kval=pq.kernels(-mid,N,max_s=12,min_s=-degree)
        for kind,offset in [(0,1),(1,2),(2,4)]:
            for j in (7,8):
                component=('real' if j%2==0 else 'imag') if kind==0 else ('imag' if j%2==0 else 'real')
                kc=pq.kernel_jet(j+offset,kval,component,degree)
                kb=pq.kernel_bound(j+offset,-hi,N,degree)
                value,error=pq.integrate_product(Fc[kind][j],Fb[kind][j],kc,kb,h,degree)
                sums[kind]+=(-value if kind==0 and j%2 else value);errors[kind]+=error
        future=[v+pq.integrate_primitive(fc,fb,h,degree,True) for v,fc,fb in zip(future,fcs,fbs)]
        if progress and index%128==0:print('Phase extension',index,len(panels),'seconds',round(time.monotonic()-start,3),flush=True)
    factors=[2/(27*iv.pi**2),1/(36*iv.pi**2),1/(36*iv.pi**2)]
    keys=['pressure_derivative','pressure','density']
    return {'schema':'ueot-prepared-phase-extension/1','status':'PARTIAL' if limit else 'PASS','N':N,'radius':str(radius),
       'J':8,'terms':[7,8],'panels':len(panels),'time_taylor_degree':degree,'preparation_subdivisions':subdivisions,
       'born_polynomial_integrals':{k:old.pair(v*p) for k,v,p in zip(keys,sums,factors)},
       'time_quadrature_error_bounds':{k:old.pair(v*p) for k,v,p in zip(keys,errors,factors)},
       'source_identity':{Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          'phase_quadrature.py':hashlib.sha256((HERE/'phase_quadrature.py').read_bytes()).hexdigest()}}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',default='0');ap.add_argument('--N',type=int,default=512)
    ap.add_argument('--mesh',type=int,default=1024);ap.add_argument('--degree',type=int,default=10);ap.add_argument('--limit',type=int)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    ap.add_argument('--output',default='phase_extension_zero.json')
    args=ap.parse_args();result=compute(Q(args.radius),args.N,args.mesh,args.degree,True,args.limit)
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/args.output
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    for key,value in result['born_polynomial_integrals'].items():print(key,[float(bg.lower(old.read_pair(value))),float(bg.upper(old.read_pair(value)))],flush=True)
if __name__=='__main__':main()
