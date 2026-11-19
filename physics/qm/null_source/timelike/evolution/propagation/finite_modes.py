"""Validated canonical mode propagation using Taylor remainders and energy balls.

Every local error bound is directed interval arithmetic. The nominal centers
are arbitrary binary mp numbers, and are never themselves called proofs.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time
from mpmath import iv,mp
from background import (I,box,lower,upper,absmax,derivative_box,coefficients,
                        START,STOP,CAP,BREAKS)

HERE=Path(__file__).resolve().parent
TARGETS=(Q(0),Q(3,64),Q(11,64),Q(3,16))


def mid(x):
    return (lower(x)+upper(x))/2


def bound(x):
    return I(upper(x))


def norm(u,p,a,omega):
    return iv.sqrt(omega*a*a*(u.real**2+u.imag**2)
                   +(p.real**2+p.imag**2)/(omega*a*a))


def recenter(z):
    c=iv.mpc(I(mid(z.real)),I(mid(z.imag)))
    d=z-c
    radius=iv.sqrt(I(absmax(d.real))**2+I(absmax(d.imag))**2)
    return c,bound(radius)


def decimal_box(x,digits=50):
    # Outward decimal endpoints from a rational floor/ceiling, not mp.nstr.
    factor=10**digits
    lo=int(mp.floor(lower(x)*factor))-2
    hi=int(mp.ceil(upper(x)*factor))+2
    while not I(Q(lo,factor))<=x.a:
        lo-=1
    while not x.b<=I(Q(hi,factor)):
        hi+=1
    return [str(Q(lo,factor)),str(Q(hi,factor))]


def point_pair(z):
    # Exact binary centers serialized as rational numbers.
    def rational(x):
        sign,man,exp,bc=lower(x)._mpf_
        v=Q((-1 if sign else 1)*int(man))
        return str(v*2**exp) if exp>=0 else str(v/Q(2**(-exp)))
    return [rational(z.real),rational(z.imag)]


def local_certificate(lo,hi,degree,last):
    h=hi-lo
    aj,cj,bj=coefficients(lo,hi,degree,h)
    assert aj.c[0]>0
    amin,amax=I(lower(aj.c[0])),I(upper(aj.c[0]))
    variation=I(absmax(aj.c[1]/aj.c[0]))
    growth=iv.exp(variation)
    omin,omax=iv.sqrt(3),iv.sqrt(last*last-1)
    # Unit initial energy covers every k=2..last and both complex components.
    u=[growth/(amin*iv.sqrt(omin))]
    p=[growth*amax*iv.sqrt(omax)]
    cabs=[I(absmax(x)) for x in cj.c]
    babs=[I(absmax(x)) for x in bj.c]
    for n in range(degree+1):
        un=I(h)*sum((babs[j]*p[n-j] for j in range(n+1)),I(0))/(n+1)
        pn=I(h)*(last*last-1)*sum((cabs[j]*u[n-j] for j in range(n+1)),I(0))/(n+1)
        u.append(un);p.append(pn)
    remainder=iv.sqrt(omax*amax*amax*u[-1]**2+p[-1]**2/(omin*amin*amin))
    return bound(variation),bound(growth),bound(remainder)


def make_mesh(last=64,degree=12,tolerance='1e-18'):
    tol=I(tolerance)
    total=TARGETS[-1]-START
    breaks=sorted(set(BREAKS+TARGETS))
    cells=[]
    def add(lo,hi,depth=0):
        try:
            variation,growth,remainder=local_certificate(lo,hi,degree,last)
            good=upper(remainder)<lower(tol*I((hi-lo)/total))
        except (AssertionError,ZeroDivisionError):
            good=False
        if not good:
            if depth>22:
                raise RuntimeError(f'Cannot certify cell {lo},{hi}')
            m=(lo+hi)/2
            add(lo,m,depth+1);add(m,hi,depth+1)
            return
        a,c,b=coefficients(lo,lo,degree,hi-lo)
        endpoint=derivative_box(hi,hi,1)
        cells.append(dict(lo=lo,hi=hi,variation=variation,growth=growth,
            remainder=remainder,c=c.c,b=b.c,a_end=endpoint.c[0],h_end=endpoint.c[1]/endpoint.c[0]))
    for lo,hi in zip(breaks,breaks[1:]):
        add(lo,hi)
    return cells


def step(u,p,error,cell,k,degree):
    h=I(cell['hi']-cell['lo']);lam=k*k-1;omega=iv.sqrt(lam)
    a_start=derivative_box(cell['lo'],cell['lo'],0).c[0]
    initial_norm=norm(u,p,a_start,omega)
    us,ps=[u],[p]
    for n in range(degree):
        us.append(h*sum((cell['b'][j]*ps[n-j] for j in range(n+1)),iv.mpc(0))/(n+1))
        ps.append(-h*lam*sum((cell['c'][j]*us[n-j] for j in range(n+1)),iv.mpc(0))/(n+1))
    un,ur=recenter(sum(us,iv.mpc(0)))
    pn,pr=recenter(sum(ps,iv.mpc(0)))
    a=cell['a_end']
    round_error=iv.sqrt(omega*a*a*ur*ur+pr*pr/(omega*a*a))
    new_error=cell['growth']*error+cell['remainder']*initial_norm+round_error
    return un,pn,bound(new_error)


def report_mode(u,p,error,a,h,k):
    omega=iv.sqrt(k*k-1)
    n=norm(u,p,a,omega)
    e=(p.real**2+p.imag**2)/(a*a)+(k*k-1)*a*a*(u.real**2+u.imag**2)
    pressure=(p.real**2+p.imag**2)/(a*a)-(k*k-1)*a*a*(u.real**2+u.imag**2)/3
    delta=bound(omega*(2*n*error+error*error))
    symmetric=box(-upper(delta),upper(delta))
    v=a*u
    vp=p/a+h*v
    return dict(k=k,u_center=point_pair(u),p_center=point_pair(p),
        norm_error_radius=decimal_box(error)[1],
        e=decimal_box(e+symmetric),s=decimal_box(pressure+symmetric),
        e_s_error_radius=decimal_box(delta)[1],
        v_center_box={'real':decimal_box(v.real),'imag':decimal_box(v.imag)},
        v_center_error_radius=decimal_box(error/iv.sqrt(omega))[1],
        vprime_center_box={'real':decimal_box(vp.real),'imag':decimal_box(vp.imag)},
        vprime_error_radius=decimal_box((iv.sqrt(omega)+I(absmax(h))/iv.sqrt(omega))*error)[1])


def calculate(last=64,degree=12,tolerance='1e-18',progress=True):
    start=time.monotonic()
    frozen_sources={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in ('background.py','finite_modes.py')}
    cells=make_mesh(last,degree,tolerance)
    print(f'Certified mesh: {len(cells)} cells',file=sys.stderr,flush=True)
    targets={str(t):dict(eta=str(t),a=decimal_box(derivative_box(t,t,0).c[0]),modes=[]) for t in TARGETS}
    for k in range(2,last+1):
        omega=iv.sqrt(k*k-1);a0=iv.sqrt(3)
        u,du=recenter(iv.mpc(1/(a0*iv.sqrt(2*omega)),0))
        p,dp=recenter(iv.mpc(0,-a0*iv.sqrt(omega/2)))
        error=bound(iv.sqrt(omega*a0*a0*du*du+dp*dp/(omega*a0*a0)))
        for cell in cells:
            u,p,error=step(u,p,error,cell,k,degree)
            if cell['hi'] in TARGETS:
                targets[str(cell['hi'])]['modes'].append(report_mode(u,p,error,cell['a_end'],cell['h_end'],k))
        if progress and (k%8==0 or k==last):
            print(f'Certified k={k}, energy radius={float(upper(error)):.3e}',file=sys.stderr,flush=True)
    error_max=max(float(Q(row['norm_error_radius'])) for target in targets.values() for row in target['modes'])
    variation=sum((c['variation'] for c in cells),I(0))
    relative=sum((c['remainder'] for c in cells),I(0))
    assert frozen_sources=={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in frozen_sources}, 'source changed during verification'
    return dict(status='VALIDATED_FINITE_MODES_ONLY',last_nonzero_mode=last,degree=degree,
        precision_decimal=iv.dps,requested_sum_local_relative_budget=tolerance,
        canonical_reference='instrument.state_scale; interpolate a not a²; k1 excluded and treated exactly',
        energy_norm='E²=omega*a²*|delta u|²+|delta p|²/(omega*a²)',
        mesh_cells=len(cells),mesh=[[str(c['lo']),str(c['hi'])] for c in cells],
        log_energy_growth_upper=decimal_box(variation)[1],sum_local_relative_remainder_upper=decimal_box(relative)[1],
        max_energy_radius=error_max,targets=targets,
        source_sha256=frozen_sources,
        numerical_tail_beyond_cutoff='NOT_IN_THIS_CERTIFICATE',
        dynamic_absolute_stress='requires UV tail and same-scheme local additions',
        diagnostic_wall_seconds=round(time.monotonic()-start,3))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Validated propagation requires assertions; do not use -O')
    parser=argparse.ArgumentParser()
    parser.add_argument('--last',type=int,default=64)
    parser.add_argument('--degree',type=int,default=12)
    parser.add_argument('--tolerance',default='1e-18')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result=calculate(args.last,args.degree,args.tolerance)
    rendered=json.dumps(result,indent=2,ensure_ascii=False)+'\n'
    if args.check:
        old=json.loads((HERE/'result.json').read_text())
        for name in set(old)|set(result):
            if name!='diagnostic_wall_seconds':
                assert old[name]==result[name], ('receipt mismatch',name)
        print('PASS: validated finite-mode propagation and exact receipt replay')
    if args.output:
        args.output.write_text(rendered)
        print(f'Saved {args.output}, {result["mesh_cells"]} cells, max radius {result["max_energy_radius"]:.3e}')
    else:
        print(rendered,end='')
