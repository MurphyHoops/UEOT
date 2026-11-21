"""Independent wide-window, visibility-free readout and weak-lens checks."""
import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import roots_legendre
from numpy.polynomial import Polynomial as P
import replay as r


def window(t):
    return (1-t*t)**3


def point_probe(A,b,d,order):
    # Independent canonical solutions. B(u,s) solves B(s,s)=0, B_u(s,s)=1.
    t,w=roots_legendre(order)
    u=b*t+d
    def rhs(x,y):
        k=r.curvature(x,A,0.)
        return [y[1],-k*y[0],y[3],-k*y[2]]
    sol=solve_ivp(rhs,(-1.02,1.02),[1.,0.,0.,1.],t_eval=u,method="DOP853",
                  atol=2e-15,rtol=1e-13,max_step=.025)
    p,pd,q,qd=sol.y
    np.testing.assert_allclose(p*qd-pd*q,1.,atol=4e-12,rtol=0)
    sep=u[:,None]-u
    J=q[:,None]*p-p[:,None]*q
    mask=sep!=0
    kernel=np.diag([r.curvature(x,A,0.)/6 for x in u])
    kernel[mask]=(sep[mask]/J[mask]-1)/sep[mask]**2
    weights=b*w*window(t)
    var=64/(75*np.pi**2)-weights@kernel@weights/(4*np.pi**2)
    visibility=np.exp(-var/2)
    theta=A*np.sum(weights*[r.profile(x)[0] for x in u])
    return (1+visibility*np.array([np.cos(theta),np.sin(theta)]))/2


def shape_integral(b,d):
    n=32768
    t=-1+(np.arange(n)+.5)*2/n
    mid=(2/n)*np.sum(window(t)*[r.profile(x)[0] for x in t])
    # |(chi*f)'| <= 6+8/e <9. Lipschitz midpoint bound over length 2.
    span=9/n+32/35*(8/math.e)*(max(abs(b[0]-1),abs(b[1]-1))+max(map(abs,d)))
    return [.998*b[0]*(mid-span),1.002*b[1]*(mid+span)]


def phase_box(count,n):
    mean=2*np.asarray(count)/n-1
    half=2*(r.radius(n,1.)+.001)
    if mean[0]<=half:
        raise ValueError("quadratures do not certify the selected X half-plane")
    corners=[math.atan2(mean[1]+j*half,mean[0]+i*half) for i in (-1,1) for j in (-1,1)]
    return [min(corners),max(corners)]


def simulate_wide():
    cal=r.instrument_data(np.random.Generator(np.random.PCG64(33469801)))
    # Only rod and clock measurements are shared. No use of narrow Ramsey counts.
    rod_range=r.radius(r.N["rod"],.001)+.0005
    g=r.iw(cal["rod_mean"])+r.iw(-rod_range,rod_range)
    left,right=cal["clock_mean"]
    cr=r.radius(r.N["clock"],.002)+.0005
    b=[(right-left)/2-cr,(right-left)/2+cr]
    d=[(right+left)/2-cr,(right+left)/2+cr]
    F=shape_integral(b,d)
    beam=[]
    train_rng=np.random.default_rng(33469811)
    k=[.9,1.1]
    for cmd in (.25,-.25):
        p=point_probe(cmd,1.001,-.002,96)
        np.testing.assert_allclose(p,point_probe(cmd,1.001,-.002,64),atol=1e-9,rtol=0)
        counts=train_rng.binomial(65536,p)
        phi=phase_box(counts,65536)
        corners=[q/(cmd*v) for q in phi for v in F]
        k=[max(k[0],min(corners)),min(k[1],max(corners))]
        beam.append(counts.tolist())
    if k[0]>k[1]:
        raise ValueError("incompatible signed wide-window data")
    amp=sorted([-.375*z for z in k])
    phase_pred=[min(a*f for a in amp for f in F),max(a*f for a in amp for f in F)]
    bands={name:r.bound_geometry(r.iw(*amp),xi,g,r.iw(*b),r.iw(*d))["camera_readout"]
           for name,xi in [("minimal",r.iw(0)),("improved",r.iw(1)/6)]}
    # Reveal new amplitude and shots only after forming both predictions.
    hold_rng=np.random.default_rng(33469812)
    p=point_probe(-.375,1.001,-.002,96)
    counts=hold_rng.binomial(32768,p)
    held_phi=phase_box(counts,32768)
    def ode(t,y):
        return [y[1],-1.001**2*r.curvature(1.001*t-.002,-.375,0)*y[0]]
    sol=solve_ivp(ode,r.TIMES[[0,-1]],[1.,0.],t_eval=r.TIMES,method="DOP853",rtol=1e-13,atol=1e-15)
    assert sol.success
    clean=1.013*sol.y[0,:,None,None]*np.eye(2)
    frames=clean+hold_rng.uniform(-.0005,.0005,(8192,4,2,2))
    y=float(r.statistic(frames).mean())
    e=r.radius(8192,.001*math.sqrt(8)/(.1))
    ci=[y-e,y+e]
    src=r.intersect(phase_pred,held_phi)
    verdict={key:("source_monitor_failed" if not src else
                  "compatible" if r.intersect(ci,val) else "rejected") for key,val in bands.items()}
    assert verdict==dict(minimal="compatible",improved="rejected")
    peer=json.loads((r.HERE.parent/"probe/observed.json").read_text())
    pq=peer["rows"][0]["probabilities"]
    v=point_probe(.25,1.,0.,96)
    np.testing.assert_allclose(v,[pq["X"][0],pq["Y"][0]],atol=2e-10,rtol=0)
    return dict(narrow_p_gap_lower=peer["narrow_point_gate"]["Y_plus_ideal_probability_gap_lower"],
                independent_nominal_p_XY=v.tolist(),cal_XY=beam,kappa=k,held_A=amp,
                held_XY=counts.tolist(),held_phase_prediction=phase_pred,held_phase_observed=held_phi,
                geo_prediction=bands,geo_observed=ci,decision=verdict,starts=360448)


def weak_rows(A,velocity_gain=1.,area_gain=1.,order=96):
    def rhs(u,y):
        j,v=y.reshape(2,2,2)
        w=(1+u)/8
        T=np.array([[w,u/10],[u/10,-w]])+np.eye(2)*r.curvature(u,A,1/6)
        return np.stack([v,-T@j]).ravel()
    x,weights=roots_legendre(order)
    u=.75*x
    s=solve_ivp(rhs,(-.75,.75),np.r_[np.eye(2).ravel(),np.zeros(4)],t_eval=u,
                rtol=2e-13,atol=1e-15,method="DOP853")
    assert s.success
    j,v=s.y.T.reshape(-1,2,2,2).transpose(1,0,2,3)
    z=area_gain*np.linalg.det(j)
    dv=area_gain*velocity_gain**2*np.linalg.det(v)
    f,fp,fpp=np.array([r.profile(t) for t in u]).T
    F,Fp,Fpp=f*f,2*f*fp,2*(fp*fp+f*fpp)
    curv=np.array([r.curvature(t,A,1/6) for t in u])
    rows=[]
    for n in (0,2,4):
        w=P([1,0,-16/9])**3*P([0]*n+[1])
        q,qp,qpp=w(u),w.deriv()(u),w.deriv(2)(u)
        L=-qpp*z/2+q*dv
        M=q*z*fp**2
        B=-(qpp*F+2*qp*Fp+2*q*Fpp)*z+2*q*F*dv
        num=lambda y: .75*float(weights@y)
        if velocity_gain==1:
            np.testing.assert_allclose(num(L),num(q*curv*z),rtol=1e-10,atol=2e-13)
        rows.append([num(L),num(M),num(B)])
    return np.array(rows)


def weak():
    def solve(a):
        return np.linalg.solve(a[:2,1:],a[:2,0])
    rows=weak_rows(.25)
    fit=solve(rows)
    np.testing.assert_allclose(fit,[.0625,1/96],atol=1e-11,rtol=0)
    same=solve(weak_rows(.25,area_gain=7.))
    np.testing.assert_allclose(same,fit,atol=1e-12,rtol=0)
    biased=solve(weak_rows(.25,velocity_gain=1.1))
    alt=weak_rows(.375)
    res=alt[:,0]-2.25*(alt[:,1:]@fit)
    assert abs(res).max()<1e-11
    det=float(np.linalg.det(rows[:2,1:]))
    archived=json.loads((r.HERE.parent/"lens_result.json").read_text())
    for name,value in (("rank_determinant",det),("h",fit[0]),("b",fit[1]),("xi",fit[1]/fit[0])):
        a,b=archived[name]
        assert a<=value<=b,(name,value,a,b)
    return dict(rank_det=det,h_b=fit.tolist(),common_area_gain7=same.tolist(),
                velocity_gain_1p1_h_b=biased.tolist(),velocity_gain_1p1_xi=biased[1]/biased[0],
                held_residuals=res.tolist(),same_trace_unused_weight=float(rows[2,0]-rows[2,1:]@fit))


def sign_pair():
    peer=json.loads((r.HERE.parent/"probe/pair_observed.json").read_text())
    def decode(ratio):
        z={}
        for row in peer["records"]:
            z[row["source"],row["input_X"]]=complex(2*row["X"][0]-1,ratio*(2*row["Y"][0]-1))
        a=z["+",1]-z["+",-1]
        b=z["-",1]-z["-",-1]
        return np.angle(a*b.conjugate())/2
    theta=decode(1.)
    assert abs(theta-peer["recovered_half_phase"])<1e-13
    wrong=decode(.7)
    assert abs(wrong-theta)>.01
    return dict(half_phase=theta,Y_axis_gain_times_0p7=wrong,
                centered_mixture_Y=peer["centered_same_stress_mixture_Y_plus"])


if __name__=="__main__":
    out=dict(wide_probe=simulate_wide(),weak_lens=weak(),sign_pair=sign_pair())
    if sys.argv[1:]==["--check"]:
        saved=json.loads((Path(__file__).with_name("review_result.json")).read_text())
        for key,d in out.items():
            assert saved[key].keys()==d.keys()
            for field,value in d.items():
                if isinstance(value,dict):
                    if field=="geo_prediction":
                        for model,interval in value.items():
                            np.testing.assert_allclose(interval,saved[key][field][model],atol=1e-10)
                    else:
                        assert value==saved[key][field]
                else:
                    np.testing.assert_allclose(value,saved[key][field],atol=1e-10)
        print("PASS: physical wide probe, split calibration and holdout, weak identities and gain controls.")
    else:
        print(json.dumps(out,indent=2))
