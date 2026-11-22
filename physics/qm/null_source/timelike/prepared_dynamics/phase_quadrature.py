"""Directed phase-preserving quadrature of the actual all-mode Born tail.

No mode cutoff replaces the infinite field. The inverse-frequency and
nonlinear remainders are separate certificates in phase_bounds.py/assemble.py.
"""
from __future__ import annotations
import argparse, json, hashlib, sys, time
from fractions import Fraction as Q
from math import factorial, comb, ceil
from functools import lru_cache
from pathlib import Path
from mpmath import iv,mp
import sympy as sp
import phase_bounds as pb
bg,old,initial=pb.bg,pb.old,pb.initial
I,box,Jet=bg.I,bg.box,bg.Jet
pw=old.power
HERE=Path(__file__).resolve().parent
ORDER=10
EPS=Q(1,2**20)
iv.dps=50;mp.dps=60

def absI(x):return initial.absolute(x)
def top(x):return initial.top(x)
def symmetric(r):return box(-bg.upper(r),bg.upper(r))
def actual_q(lo,hi,radius,order):
    return bg.q_box(lo,hi,order) if not radius else initial.family_q_box(lo,hi,box(-radius,radius),order)
def time_q(lo,hi,radius,degree):
    values=actual_q(lo,hi,radius,degree+4)
    return [Jet([values[j+n]/factorial(n) for n in range(degree+1)]) for j in range(5)]
def primitive_sources(q):
    return [q[0],q[0]*q[0],q[1]*q[1],q[0]*q[0]*q[0]]
def integral_jet(value,f):
    return Jet([value]+[-f.c[n-1]/n for n in range(1,f.n+1)])
def r_coefficients(qs):
    q,q1,q2,q3,q4=qs
    qsq=q*q;q1sq=q1*q1;q2sq=q2*q2
    return [
      q4/32,
      -5*q*q4/64-7*q1*q3/32-9*q2sq/64,
      35*qsq*q4/256+49*q*q1*q3/64+63*q*q2sq/128+27*q1sq*q2/32+3*q2*q4/256+5*q3*q3/512,
      -105*qsq*q*q4/512-441*qsq*q1*q3/256-567*qsq*q2sq/512-243*q*q1sq*q2/64
      -27*q*q2*q4/512-45*q*q3*q3/1024-135*q1sq*q1sq/256-15*q1sq*q4/1024
      -87*q1*q2*q3/512-27*q2sq*q2/512]

def endpoint_prefactors(radius):
    d=Jet([0,1,0,0])
    vals=actual_q(Q(0),Q(0),radius,4)
    q=[Jet.const(v,3) for v in vals]
    A,B,T,T1,Rn=old.normalized_defect(q,d)
    P=(B+(1-d)/3)/B.sqrt()
    R=(d*T+(vals[0]+1))/B.sqrt()
    return [I(1),I(-1),I(0),I(0)],P.c,R.c

def F_coefficients(q,primitive_values,prefactors):
    integrals=[integral_jet(v,f) for v,f in zip(primitive_values,primitive_sources(q))]
    a=integrals[0]
    b=(q[1]-integrals[1])/4
    c=(-q[3]-6*q[0]*q[1]-integrals[2]+2*integrals[3])/16
    aa=a*a;aaa=aa*a;aaaa=aa*aa
    expcoeff=[Jet.const(1,q[0].n),a,-aa/2,b-aaa/6,
              -a*b+aaaa/24,c-aa*b/2+aaaa*a/120,
              -a*c-b*b/2+aaa*b/6-aaaa*aa/720]
    r=r_coefficients(q)
    results=[]
    for pref in prefactors:
        amplitudes=[sum((r[k-j]*pref[j] for j in range(k+1)),Jet.const(0,q[0].n)) for k in range(4)]
        results.append([sum((amplitudes[k]*expcoeff[j-2*k] for k in range(j//2+1)),Jet.const(0,q[0].n)) for j in range(7)])
    return results

@lru_cache(None)
def bernoulli(n):return Q(str(sp.bernoulli(n)))
@lru_cache(None)
def zeta(s):
    assert s>=2
    M=32;P=14
    value=sum((Q(1,k**s) for k in range(1,M)),Q(0))+Q(M)**(1-s)/(s-1)+Q(1,2)*Q(M)**(-s)
    rising=1
    for r in range(1,P+1):
        rising=1
        for j in range(2*r-1):rising*=s+j
        value+=bernoulli(2*r)*rising*Q(M)**(-s-2*r+1)/factorial(2*r)
    remainder=top(2*(iv.pi**2/6)*rising*I(Q(M)**(-s-2*P+1))/(2*iv.pi)**(2*P))
    return I(value)+symmetric(remainder)

def polylog_positive(s,tau):
    x=2*I(tau)
    if s==1:return iv.mpc(-iv.log(2*iv.sin(I(tau))),iv.pi/2-I(tau))
    mu=iv.mpc(0,x)
    out=iv.mpc(0)
    for n in range(s-1):out+=zeta(s-n)*mu**n/factorial(n)
    harmonic=I(sum((Q(1,k) for k in range(1,s)),Q(0)))
    out+=mu**(s-1)/factorial(s-1)*iv.mpc(harmonic-iv.log(x),iv.pi/2)
    out-=mu**s/(2*factorial(s))
    P=8
    for n in range(1,P+1):
        out-=I(bernoulli(2*n))*mu**(s+2*n-1)/(2*n*factorial(s+2*n-1))
    ratio=x/(2*iv.pi)
    rem=top(2*(iv.pi**2/6)*x**(s-1)*I(Q(factorial(2*P+1),factorial(s+2*P+1)))
            *ratio**(2*P+2)/(1-ratio**2))
    return out+iv.mpc(symmetric(rem),symmetric(rem))

@lru_cache(None)
def eulerian_poly(m):
    # Li_{-m}(z)=P_m(z)/(1-z)^{m+1}.
    p=[0,1]
    for j in range(m):
        derivative=[(k+1)*p[k+1] for k in range(len(p)-1)]
        b=[0]*(len(p)+1)
        for k,v in enumerate(derivative):b[k+1]+=v;b[k+2]-=v
        for k,v in enumerate(p):b[k+1]+=(j+1)*v
        while len(b)>1 and b[-1]==0:b.pop()
        p=b
    return tuple(p)

def negative_li(m,z):
    value=iv.mpc(0)
    for c in reversed(eulerian_poly(m)):value=value*z+c
    return value/(1-z)**(m+1)

@lru_cache(None)
def inverse_weights(N,max_s):
    return [[I(Q(1,k**s)) for s in range(1,max_s+1)] for k in range(1,N+1)]

def kernels(tau,N,max_s=10,min_s=-10):
    z=iv.mpc(iv.cos(2*I(tau)),iv.sin(2*I(tau)))
    sums=[iv.mpc(0) for _ in range(max_s)]
    zk=iv.mpc(1)
    for weights in inverse_weights(N,max_s):
        zk*=z
        for j,w in enumerate(weights):sums[j]+=zk*w
    values={s:polylog_positive(s,tau)-sums[s-1] for s in range(1,max_s+1)}
    lower={0:1/(1-z)}
    lower.update({j:negative_li(j,z) for j in range(1,-min_s+1)})
    leading=zk*z
    for m in range(-min_s+1):
        values[-m]=leading*sum((comb(m,j)*(N+1)**(m-j)*lower[j] for j in range(m+1)),iv.mpc(0))
    return values

def kernel_jet(s,values,component,degree):
    entries=[]
    for n in range(degree+1):
        z=values[s-n]*((-2j)**n)/factorial(n)
        entries.append(z.real if component=='real' else z.imag)
    return Jet(entries)

def kernel_bound(s,taumin,N,degree):
    denominator=I(bg.lower(2*iv.sin(I(taumin))))
    H=I(sum((Q(1,k) for k in range(1,N+1)),Q(0)))
    def one(r):
        if r>=2:return I(Q(1,(r-1)*N**(r-1)))
        if r==1:return -iv.log(denominator)+iv.pi/2+H
        m=-r
        return sum((I(comb(m,j)*(N+1)**(m-j)*factorial(j))/denominator**(j+1)
                    for j in range(m+1)),I(0))
    return [top(I(2**n)*one(s-n)/factorial(n)) for n in range(degree+1)]

def integrate_product(fc,fb,kc,kbounds,h,degree):
    product=fc*kc
    polynomial=sum((product.c[j]*I(2)*I(h)**(j+1)/(j+1) for j in range(0,degree,2)),I(0))
    error=sum((absI(fb.c[j])*kbounds[degree-j] for j in range(degree+1)),I(0))
    error=top(error*2*I(h)**(degree+1)/(degree+1))
    return polynomial+symmetric(error),error

def integrate_primitive(fc,fb,h,degree,whole):
    if whole:
        value=sum((fc.c[j]*2*I(h)**(j+1)/(j+1) for j in range(0,degree,2)),I(0))
        error=top(absI(fb.c[degree])*2*I(h)**(degree+1)/(degree+1))
    else:
        value=sum((fc.c[j]*I(h)**(j+1)/(j+1) for j in range(degree)),I(0))
        error=top(absI(fb.c[degree])*I(h)**(degree+1)/(degree+1))
    return value+symmetric(error)

def cells(subdivisions):
    cuts=list(bg.BREAKS)+[Q(-1,32),Q(-1,64)]
    width=Q(1,16*subdivisions)
    grid=set(cuts)
    for lo,hi in zip(cuts,cuts[1:]):
        step=width if lo<bg.STOP else Q(1,512)
        count=max(1,ceil((hi-lo)/step))
        grid.update(lo+(hi-lo)*Q(j,count) for j in range(count+1))
    value=EPS
    while value<Q(1,64):grid.add(-value);value*=2
    grid.add(-EPS)
    grid=sorted(v for v in grid if v<=-EPS)
    return list(reversed(list(zip(grid,grid[1:]))))

def compute(radius=Q(0),N=512,subdivisions=1024,degree=ORDER,progress=False,limit=None):
    assert degree%2==0 and degree>=4
    prefactors=endpoint_prefactors(radius)
    qs_end=time_q(-EPS,Q(0),radius,degree)
    fs_end=primitive_sources(qs_end)
    future=[I(EPS)*f.c[0] for f in fs_end]
    at_any_end=[box(0,EPS)*f.c[0] for f in fs_end]
    Fe=F_coefficients(qs_end,at_any_end,prefactors)
    # The removable q'''/sin endpoint of the leading derivative term.
    q4max=absI(qs_end[4].c[0])
    endpoint_d=top(I(EPS)*q4max*I(EPS)/iv.sin(I(EPS))/32)
    for j in range(1,7):endpoint_d+=I(EPS)*absI(Fe[0][j].c[0])*I(Q(1,j*N**j))
    endpoint_p=sum((I(EPS)*absI(Fe[1][j].c[0])*I(Q(1,(j+1)*N**(j+1))) for j in range(7)),I(0))
    endpoint_r=sum((I(EPS)*absI(Fe[2][j].c[0])*I(Q(1,(j+3)*N**(j+3))) for j in range(7)),I(0))
    sums=[symmetric(endpoint_d),symmetric(endpoint_p),symmetric(endpoint_r)]
    errors=[I(0),I(0),I(0)]
    panels=cells(subdivisions)
    if limit is not None:panels=panels[:limit]
    start=time.monotonic()
    for index,(lo,hi) in enumerate(panels):
        mid=(lo+hi)/2;h=(hi-lo)/2
        qc=time_q(mid,mid,radius,degree);qb=time_q(lo,hi,radius,degree)
        sources_c=primitive_sources(qc);sources_b=primitive_sources(qb)
        primitive_center=[f+integrate_primitive(fc,fb,h,degree,False) for f,fc,fb in zip(future,sources_c,sources_b)]
        primitive_box=[f+box(0,hi-lo)*fb.c[0] for f,fb in zip(future,sources_b)]
        Fc=F_coefficients(qc,primitive_center,prefactors)
        Fb=F_coefficients(qb,primitive_box,prefactors)
        values=kernels(-mid,N,min_s=-degree)
        kcache={};bcache={}
        def kernel(s,component):
            key=(s,component)
            if key not in kcache:kcache[key]=kernel_jet(s,values,component,degree)
            if s not in bcache:bcache[s]=kernel_bound(s,-hi,N,degree)
            return kcache[key],bcache[s]
        tcenter=initial.time_jet(mid,mid,degree);tbox=initial.time_jet(lo,hi,degree)
        ac=qc[3]/tcenter.sincos()[0]/32
        ab=qb[3]/tbox.sincos()[0]/32
        frequency=2*N+1
        kc=(tcenter*frequency).sincos()[1]
        kb=[I(Q(frequency**j,factorial(j))) for j in range(degree+1)]
        value,error=integrate_product(ac,ab,kc,kb,h,degree)
        sums[0]+=value;errors[0]+=error
        for j in range(1,7):
            component='real' if j%2==0 else 'imag'
            kc,kb=kernel(j+1,component)
            value,error=integrate_product(Fc[0][j],Fb[0][j],kc,kb,h,degree)
            sums[0]+=value if j%2==0 else -value;errors[0]+=error
        for kind,offset in [(1,2),(2,4)]:
            for j in range(7):
                component='imag' if j%2==0 else 'real'
                kc,kb=kernel(j+offset,component)
                value,error=integrate_product(Fc[kind][j],Fb[kind][j],kc,kb,h,degree)
                sums[kind]+=value;errors[kind]+=error
        future=[f+integrate_primitive(fc,fb,h,degree,True) for f,fc,fb in zip(future,sources_c,sources_b)]
        if progress and index%128==0:
            print('Phase quadrature',index,len(panels),'seconds',round(time.monotonic()-start,3),
                  'derivative partial',float(bg.lower(sums[0]*2/(27*iv.pi**2))),float(bg.upper(sums[0]*2/(27*iv.pi**2))),flush=True)
    pref=[2/(27*iv.pi**2),1/(36*iv.pi**2),1/(36*iv.pi**2)]
    return {'schema':'ueot-prepared-phase-quadrature/1','status':'PARTIAL' if limit else 'PASS',
        'radius':str(radius),'N':N,'J':6,'time_taylor_degree':degree,'preparation_subdivisions':subdivisions,
        'panels':len(panels),'endpoint_epsilon':str(EPS),
        'born_polynomial_integrals':{key:old.pair(value*p) for key,value,p in zip(['pressure_derivative','pressure','density'],sums,pref)},
        'time_quadrature_error_bounds':{key:old.pair(value*p) for key,value,p in zip(['pressure_derivative','pressure','density'],errors,pref)},
        'endpoint_error_bounds':{key:old.pair(value*p) for key,value,p in zip(['pressure_derivative','pressure','density'],[endpoint_d,endpoint_p,endpoint_r],pref)},
        'tail_remainders_included':False,'source_identity':{Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius',default='0');ap.add_argument('--N',type=int,default=512);ap.add_argument('--mesh',type=int,default=1024)
    ap.add_argument('--degree',type=int,default=10);ap.add_argument('--limit',type=int)
    ap.add_argument('--output',default='phase_quadrature_zero.json');ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();result=compute(Q(args.radius),args.N,args.mesh,args.degree,True,args.limit)
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/args.output
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    for key,value in result['born_polynomial_integrals'].items():print(key,[float(bg.lower(old.read_pair(value))),float(bg.upper(old.read_pair(value)))],flush=True)
if __name__=='__main__':main()
