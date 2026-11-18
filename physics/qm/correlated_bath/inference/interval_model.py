"""Independent interval Born/Weyl event predictor in Ramsey log coordinates."""
from fractions import Fraction as Fr
from functools import lru_cache
from itertools import product
from mpmath import iv
from shared import historic,read

H=historic("interval_source")
C=historic("common_c")
q,I=H.q,H.I
cfg=read("protocol.json")
iv.dps=48

def box(lo,hi):
    return iv.mpf([q(lo).a,q(hi).b])

def endpoints(x):
    return (C.iv_endpoint_fraction(x),C.iv_endpoint_fraction(x,True))

def bounds(x):
    return [C.decimal_string(C.outward_fraction(x,upper),12) for upper in (False,True)]

def intersect(x,lo,hi):
    l,h=endpoints(x)
    l,h=max(l,Fr(str(lo))),min(h,Fr(str(hi)))
    if l>h:
        raise ValueError("empty physical intersection")
    return box(l,h)

def expand(x,r):
    return x+iv.mpf([-r.b,r.b])

@lru_cache(None)
def row(t,a="0"):
    d=[g/w*(1-iv.exp(I*w*q(t)))*iv.exp(I*w*q(a)) for w,g in
       ((q(1),q(1)),(q("3/2"),q("3/5")))]
    return 2*H.inner(d,d).real,8*(H.conj(d[0])*d[1]).real

@lru_cache(None)
def response(a,b="3/4"):
    return 4*sum((g/w)**2*(iv.sin(w*q(a))+iv.sin(w*q(b))-iv.sin(w*(q(a)+q(b))))
                 for w,g in ((q(1),q(1)),(q("3/2"),q("3/5"))))

(A1,B1),(A2,B2)=row("3/4"),row("3/2")
DET=A1*B2-A2*B1

def coordinates(A,B):
    return (A*B2-B*A2)/DET,(B*A1-A*B1)/DET

def attenuation(A,B,logs):
    # A*u+B*v = a1*log(eta/m_short)+a2*log(eta/m_long).
    a1,a2=coordinates(A,B)
    return (a1+a2)*logs[0]-a1*logs[1]-a2*logs[2]

def calmean(key,eta,w,offset,atten):
    if key.startswith("R"):
        a,b=row({"R0":"0","Rshort":"3/4","Rlong":"3/2"}[key])
        return eta*iv.exp(-atten(a,b))
    a="1" if key.startswith("H") else "2/3"
    s=1 if key.endswith("p") else -1
    phi=offset+s*w*response(a)
    amp=eta*iv.exp(-atten(*row("3/4",a)))
    return amp*(iv.cos(phi) if key.startswith("X") else -iv.sin(phi))

@lru_cache(None)
def paths(times):
    ops=[H.kron(H.PAULI[a],H.PAULI[b]) for a,b in cfg["bell_tests"]]
    result=[]
    for stop,record in enumerate(cfg["records"]):
        k=min(stop+1,3)
        ks=[H.mm(H.ROTATIONS[j],H.PASS) for j in range(stop)]+([H.FAIL] if stop<3 else [])
        histories=[]
        for idx in product((0,1),repeat=k):
            op=H.IDENT
            for inst,z in zip(ks,idx):
                op=H.mm(H.mm(inst,H.PROJECT[z]),op)
            v=sum(op,[])
            beta,phase=H.bath_path(times[:k],idx)
            histories.append((v,beta,phase))
        diag=[q(0) for _ in range(5)]
        pairs=[]
        total=sum(Fr(t) for t in times[:k])
        rot=[iv.exp(I*q(w)*q(total)) for w in ("1","3/2")]
        for j,(v,b,p) in enumerate(histories):
            mv=[v]+[H.mv(o,v) for o in ops]
            diag=[x+H.inner(v,y).real/2 for x,y in zip(diag,mv)]
            for vp,bp,pp in histories[j+1:]:
                d=[r*(x-y) for r,x,y in zip(rot,b,bp)]
                A=H.inner(d,d).real/2
                B=2*(H.conj(d[0])*d[1]).real
                phase=p-pp+H.inner(bp,b).imag
                pairs.append((A,B,phase,[H.inner(vp,y) for y in mv]))
        result.append((diag,pairs))
    return result

def bell(times,eta,w,atten):
    values={obs:[] for obs in cfg["bell_tests"]}
    for diag,pairs in paths(tuple(times)):
        moments=list(diag)
        for A,B,f,coeff in pairs:
            influence=iv.exp(-atten(A,B)+I*(f*w))
            moments=[x+(y*influence).real for x,y in zip(moments,coeff)]
        for name,m in zip(values,moments[1:]):
            values[name].extend([(moments[0]-eta*m)/2,(moments[0]+eta*m)/2])
    return values

def altrule(a,total):
    # Exact equal-Ramsey pair; type I and II worst cases after sign alignment.
    atten=lambda A,B:q("9/50")*A+q("9/400")*B
    amp=iv.exp(-atten(*row("3/4",a)))
    err=q(cfg["bias_mean"])/2+q(1)/2**cfg["grid_bits"]
    upper=(1+amp*iv.sin(q("9/100")*response(a)))/2+err
    lower=(1+q(".9")*amp*iv.sin(response(a)/9)*iv.cos(q(".02")))/2-err
    threshold=(upper+lower)/2
    delta=lower-upper
    if endpoints(delta)[0]<=0:
        raise ValueError("power gap closed")
    return {"upper_P1":bounds(upper),"lower_P2":bounds(lower),"threshold":bounds(threshold),
            "guaranteed_gap":bounds(delta),"error_each_at_most":bounds(iv.exp(-total*delta**2/2)),
            "aligned_shots":total}

def radius(n,cells,alpha):
    return iv.sqrt(iv.ln(q(2*cells)/q(alpha))/(2*n))
