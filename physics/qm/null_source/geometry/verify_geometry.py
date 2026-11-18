"""Certified transverse transfer for the massless scalar sandwich wave."""
import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path

from mpmath import iv
from scipy.integrate import solve_ivp

iv.dps = 48
N = 512
ORDER = 10
CASES = {"baseline":("1/4","0",1), "minus":("-1/4","0",1),
         "improved":("1/4","1/6",1), "holdout_eighth":("1/8","0",1),
         "holdout_three_eighths":("3/8","1/6",1), "flat":("0","0",1),
         "vacuum_y":("1/4","0",-1)}
SCALAR = tuple(k for k in CASES if k not in ("minus","flat"))


def q(value):
    value = F(value)
    return iv.mpf(value.numerator)/value.denominator


def box(a,b):
    return iv.mpf([a.a,b.b])


def signed(bound):
    return iv.mpf([-1,1])*bound


def outward(x):
    parts = [(-1)**s*m*F(2)**e*10**13 for s,m,e,_ in x._mpi_]
    return [str(F(parts[0]//1,10**13)),str(F(-(-parts[1]//1),10**13))]


def conv(a,b,n):
    return sum(a[j]*b[n-j] for j in range(n+1))


def shape(u,h):
    # Coefficients of f(u+ht), f² and both derivative terms in h² K.
    den = 1-u**2
    assert den>0
    recip = [1/den]
    f = [iv.exp(1-recip[0])]
    for n in range(1,ORDER+2):
        recip.append((2*u*h*recip[-1]+(h**2*recip[-2] if n>=2 else 0))/den)
        f.append(-sum(j*recip[j]*f[n-j] for j in range(1,n+1))/n)
    ff = [conv(f,f,n) for n in range(len(f))]
    df = [(j+1)*v for j,v in enumerate(f[1:])]
    pulse = [den,-2*u*h,-h*h]
    chi = [q(1)]
    for _ in range(3):
        chi = [sum(chi[n-j]*v for j,v in enumerate(pulse) if 0<=n-j<len(chi))
               for n in range(len(chi)+2)]
    probe = [sum(v*f[n-j] for j,v in enumerate(chi) if j<=n) for n in range(ORDER+1)]
    return (ff,[conv(df,df,n) for n in range(ORDER)],
            [(n+1)*(n+2)*ff[n+2] for n in range(ORDER)],probe)


def potential(sh,a,xi,sign):
    ff,df2,ddff,_ = sh
    den = 1-2*xi*a*a*ff[0]
    assert den>0
    out = []
    for n in range(ORDER):
        other = sum(ff[j]*out[n-j] for j in range(1,n+1))
        out.append((sign*a*a*(df2[n]-xi*ddff[n])+2*xi*a*a*other)/den)
    return out


def column(k,y,dy,order):
    v = [y,dy]
    for n in range(order-1):
        v.append(-conv(k,v,n)/((n+1)*(n+2)))
    return v


def multiply(A,B):
    a,b,c,d=A
    e,f,g,h=B
    return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)


def step(k,kbox,h):
    # Sup norm of either solution column is <= exp(h max(1,|K|)) < 2.
    assert h+abs(kbox[0])/h<q("1/2")
    enclosing = column(kbox,iv.mpf([-2,2]),2*signed(h),ORDER+1)
    rem = signed(abs(enclosing[-1]))
    vals = []
    for y,v in ((1,0),(0,1)):
        coeff = column(k,q(y),h*v,ORDER)
        vals.append((sum(coeff)+rem,
                     (sum(n*t for n,t in enumerate(coeff))+(ORDER+1)*rem)/h))
    return (vals[0][0],vals[1][0],vals[0][1],vals[1][1])


def numerics(a,xi,sign):
    def rhs(u,y):
        r = 1-u*u
        f = math.exp(1-1/r) if r>1e-5 else 0.
        fp = -2*u*f/r**2 if f else 0.
        fpp = f*(4*u*u/r**4-2/r**2-8*u*u/r**3) if f else 0.
        k = sign*a*a*(fp**2-2*xi*(fp**2+f*fpp))/(1-2*xi*(a*f)**2)
        return (y[1],-k*y[0],y[3],-k*y[2])
    sol=solve_ivp(rhs,(-1.,1.),(1.,0.,0.,1.),rtol=2e-13,atol=2e-15,method="DOP853",max_step=.025)
    assert sol.success
    p,v,b,d=sol.y[:,-1]
    return (p,b,v,d)


def curvature_check():
    # Independent symbolic contraction of the metric, without using its field equation.
    import sympy as sp
    u,v,x,y=coord=sp.symbols("u v x y",real=True)
    a,b,c=(sp.Function(n)(u) for n in ("a","b","c"))
    metric=sp.Matrix([[-a*x*x-2*b*x*y-c*y*y,-1,0,0],[-1,0,0,0],[0,0,1,0],[0,0,0,1]])
    inv=metric.inv()
    ix=range(4)
    gamma=[[[sum(inv[i,l]*(metric[l,j].diff(coord[k])+metric[l,k].diff(coord[j])
                            -metric[j,k].diff(coord[l])) for l in ix)/2 for k in ix] for j in ix] for i in ix]
    def riem(i,j,k,l):
        return (gamma[i][l][j].diff(coord[k])-gamma[i][k][j].diff(coord[l])+
                sum(gamma[i][k][m]*gamma[m][l][j]-gamma[i][l][m]*gamma[m][k][j] for m in ix))
    assert all(gamma[0][j][k]==0 for j in ix for k in ix) and inv[0,0]==0
    assert sp.Matrix(2,2,lambda i,j:riem(i+2,0,j+2,0))==sp.Matrix([[a,b],[b,c]])
    ric=sp.Matrix(4,4,lambda j,l:sum(riem(i,j,i,l) for i in ix))
    assert ric==sp.diag(a+c,0,0,0) and (inv*ric).trace()==0


def calculate():
    curvature_check()
    edge = q("63/64")
    h = edge/N
    ids = (q(1),q(0),q(0),q(1))
    configs = {k:(q(a),q(x),s) for k,(a,x,s) in CASES.items()}
    flows = {k:ids for k in SCALAR}
    l1 = {k:q(0) for k in SCALAR}
    probe_integral = q(0)
    for i in range(N):
        u=i*h
        left,region=shape(u,h),shape(box(u,u+h),h)
        probe_integral += h*(sum(z/(n+1) for n,z in enumerate(left[3][:-1]))+
                             region[3][-1]/(ORDER+1))
        for k in SCALAR:
            kp=potential(left,*configs[k])
            kb=potential(region,*configs[k])
            flows[k]=multiply(step(kp,kb,h),flows[k])
            l1[k]+=abs(kb[0])/h
    for k,(a,xi,_) in configs.items():
        if k not in SCALAR:
            continue
        y=1/(1-edge**2)
        small=a*a*(4+36*abs(xi))*y**4*iv.exp(2-2*y)/(1-2*abs(xi)*a*a)
        cap=1-edge
        err=signed(cap*small*iv.exp(cap*(1+small)))
        flows[k]=multiply((1+err,cap+err,err,1+err),flows[k])
        l1[k]=2*(l1[k]+cap*small)
    flows["flat"]=(q(1),q(1),q(0),q(1))
    probe_integral=2*(probe_integral+iv.mpf([0,1])*(1-edge)*iv.exp(1-1/(1-edge**2)))
    l1["flat"]=q(0)
    flows["minus"],l1["minus"]=flows["baseline"],l1["baseline"]
    results={}
    for name,(amp,xi,sign) in configs.items():
        a,b,c,d = flows[name]
        assert 1 in a*d-b*c
        half = (d,b,c,a)                 # time reflection, det=1
        full = multiply((a,b,c,d),half)
        p,shift,v,velocity = full
        assert 1 in p*velocity-shift*v and l1[name]<1
        num=numerics(float(amp.mid),float(xi.mid),sign)
        discrepancy=max(abs(float(t.mid)-n) for t,n in zip(full,num))
        assert discrepancy<3e-11
        assert max(float(t.delta) for t in full)<1e-11
        center=(4*xi*amp**2)/(1-2*xi*amp**2)
        results[name]={"signed_shape_amplitude":CASES[name][0],
                       "physical_scalar_amplitude":"0" if name=="vacuum_y" else CASES[name][0],"xi":CASES[name][1],
                       "tidal_sign":sign,"K_at_zero":outward(sign*center),
                       "central_probe_mu":outward((q(0) if name=="vacuum_y" else amp)*probe_integral),
                       "half_transfer":list(map(outward,half)),
                       "full_transfer":list(map(outward,full)),"screen_at_2":outward(p+v),
                       "integral_abs_K_upper":outward(l1[name])[1]}
    assert results["minus"]["full_transfer"]==results["baseline"]["full_transfer"]
    def first(k):
        return list(map(F,results[k]["full_transfer"][0]))
    assert first("vacuum_y")[0]>1>first("baseline")[1]
    assert first("baseline")[1]<first("improved")[0] or first("improved")[1]<first("baseline")[0]
    a,b,c,d = flows["baseline"]
    vacuum_area = a*d+b*c
    y = flows["vacuum_y"]
    vacuum_area *= y[0]*y[3]+y[1]*y[2]
    assert vacuum_area<1
    # F=0 at the pulse peak: a nonzero numerator obstructs the metric equation.
    assert 1-2*F(8)*F(1,4)**2==0 and 4*F(8)*F(1,4)**2==2
    return {"baseline_commit":"3346989339cfbfa2322812448cee336c8633ff89","cells_per_half":N,
            "taylor_order":ORDER,"matrix_order":"row major (position, affine velocity)",
            "vacuum_control":"M=diag(K_baseline,-K_baseline); X uses baseline; scalar amplitude zero",
            "vacuum_parallel_beam_area_at_1":outward(vacuum_area),
            "central_probe_chi_f_integral":outward(probe_integral),"cases":results}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    data=calculate()
    if args.check:
        assert data==json.loads(Path(__file__).with_name("result.json").read_text())
        print("PASS: 7 propagation cases, interval Taylor bounds, finite screens, vacuum Weyl mimic and independent DOP853")
    else:
        print(json.dumps(data,indent=2))
