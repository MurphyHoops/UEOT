"""Finite-window, two-column Jacobi experiment. Python, NumPy, SciPy, mpmath."""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from mpmath import iv
from scipy.integrate import quad, solve_ivp

HERE = Path(__file__).resolve().parent
TIMES = np.array([-.30,-.25,.25,.30])
H = .05
N = dict(rod=8192,clock=8192,train=131072,matter=65536,geo=8192)
ALPHA = .05
iv.dps = 32


def profile(u):
    if abs(u)>=1:
        return 0.,0.,0.
    r=1-u*u
    f=math.exp(1-1/r)
    lp=-2*u/r**2
    lpp=-2/r**2-8*u*u/r**3
    return f,f*lp,f*(lp*lp+lpp)


def curvature(u,A,xi):
    f,fp,fpp=profile(u)
    return A*A*((1-2*xi)*fp*fp-2*xi*f*fpp)/(1-2*xi*(A*f)**2)


def shear(u):
    v,w=.055*math.cos(3*u),.040*math.sin(4*u)
    return np.array([[v,w],[w,-v]])


def paths(A,xi,b,d,extra_cycles=0,relative_tolerance=3e-12):
    def rhs(t,y):
        u=b*t+d
        K=curvature(u,A,xi)
        tide=K*np.eye(2)+shear(u)
        if extra_cycles:
            frequency=2*np.pi*extra_cycles/(b*H)
            theta=frequency*(u-(b*TIMES[0]+d))
            modulation=frequency*math.sqrt((curvature(u,A,1/6)-K)/2.5)
            tide=tide+np.diag([1.,-1.])*modulation*(np.cos(theta)-4*np.cos(2*theta))
        J,V=y.reshape(2,2,2)
        return np.stack((V,-b*b*tide@J)).ravel()
    y0=np.r_[np.eye(2).ravel(),np.zeros(4)]
    sol=solve_ivp(rhs,TIMES[[0,-1]],y0,t_eval=TIMES,method="DOP853",
                  atol=relative_tolerance/20,rtol=relative_tolerance,
                  max_step=H/(8*extra_cycles) if extra_cycles else H)
    if not sol.success:
        raise ArithmeticError(sol.message)
    return sol.y[:4].T.reshape(4,2,2)


def statistic(frames):
    # Entire 2x2 frame is retained; trace removes instantaneous traceless tides.
    tr=np.trace(frames,axis1=-2,axis2=-1)
    return -(tr[...,3]-tr[...,2]-tr[...,1]+tr[...,0])/(2*H)


def instrument_data(rng):
    rod=1.013+rng.uniform(-.0005,.0005,N["rod"])
    clocks=np.array([1.001*t-.002+rng.uniform(-.001,.001,N["clock"]) for t in (-1,1)])
    return dict(rod_mean=rod.mean(),clock_mean=clocks.mean(axis=1).tolist())


def train_data():
    rng=np.random.Generator(np.random.PCG64(33469801))
    instruments=instrument_data(rng)
    mean_f=quad(lambda t:profile(1.001*t-.002)[0],-.1,.1)[0]/.2
    bitcounts=[int(np.sum(rng.random(N["train"])<(1+math.sin(cmd*mean_f))/2))
               for cmd in (.25,-.25)]
    return dict(**instruments,matter_plus_counts=bitcounts)


def held_data():
    # Independent acquisition, no fitted values enter this generator.
    rng=np.random.Generator(np.random.PCG64(33469802))
    A=-.375
    mean_f=quad(lambda t:profile(1.001*t-.002)[0],-.1,.1)[0]/.2
    m=int(np.sum(rng.random(N["matter"])<(1+math.sin(A*mean_f))/2))
    frames=1.013*paths(A,0.,1.001,-.002)
    values=frames+rng.uniform(-.0005,.0005,(N["geo"],4,2,2))
    obs=statistic(values)
    return dict(matter_plus=m,frame_mean=values.mean(axis=0).tolist(),geo_mean=float(obs.mean()),
                geo_sd=float(obs.std(ddof=1)),
                raw_frames_sha256=hashlib.sha256(values.astype("<f8").tobytes()).hexdigest())


def iw(l,h=None):
    return iv.mpf([str(l),str(l if h is None else h)])


def endpoints(x):
    # Convert the interval into an enclosing pair of float64 endpoints.
    return [float(np.nextafter(float(x.a),-math.inf)),float(np.nextafter(float(x.b),math.inf))]


def radius(n,width):
    return width*math.sqrt(math.log(2*12/ALPHA)/(2*n))


def clock_profile(t,b,d):
    u=b*t+d
    r=1-u**2
    f=iv.exp(1-1/r)
    lp=-2*u/r**2
    lpp=-2/r**2-8*u**2/r**3
    return f,f*lp,f*(lp**2+lpp)


def filtered_profile(b,d):
    n=128
    return sum(clock_profile(iw(-1)/10+iw(1)/5*iw(j,j+1)/n,b,d)[0]
               for j in range(n))/n


def calibrate(measured):
    rg=radius(N["rod"],.001)+.0005
    g=iw(measured["rod_mean"])+iw(-rg,rg)
    c=[iw(t)+iw(-1,1)*iw(radius(N["clock"],.002)) for t in measured["clock_mean"]]
    b=(c[1]-c[0])/2+iw(-.0005,.0005)
    d=(c[1]+c[0])/2+iw(-.0005,.0005)
    if not (g>0 and b>0 and abs(d)<.02 and abs(b-1)<.02):
        raise ValueError("rod or affine clock outside operational domain")
    f=filtered_profile(b,d)
    kappas=[.9,1.1]
    for count,cmd in zip(measured["matter_plus_counts"],(.25,-.25),strict=True):
        p=iw(count)/N["train"]+iw(-1,1)*iw(radius(N["train"],1.)+.001)
        y=2*p-1
        angle=iv.atan2(y,iv.sqrt(1-y**2))  # monotone branch fixed by the command domain
        kl,kh=endpoints(angle/(iw(cmd)*f))
        kappas=[max(kl,kappas[0]),min(kh,kappas[1])]
    if kappas[0]>kappas[1]:
        raise ValueError("signed calibrations inconsistent with common source scale")
    return g,b,d,iw(*kappas),f


def bound_geometry(A,xi,g,b,d):
    # Exact cell weights. The knots 0, 1/20, 11/20, 12/20 are aligned.
    n=240
    width=iw(3)/5/n
    total=iw(0)
    sup=0.
    for j in range(n):
        lo=iw(-3)/10+width*j
        f,fp,fpp=clock_profile(lo+width*iw(0,1),b,d)
        k=A**2*((1-2*xi)*fp**2-2*xi*f*fpp)/(1-2*xi*(A*f)**2)
        adjusted=b**2*k
        weight=iw(1)
        if j<20:
            weight=iw(2*j+1)/40
        elif j>=220:
            weight=iw(2*(239-j)+1)/40
        total+=width*weight*adjusted
        sup=max(sup,endpoints(abs(adjusted))[1])
    M=iw(sup)+b**2/10
    # Volterra-Gronwall: ||J-I|| <= cosh(sqrt(M)*s)-1.
    z=iv.sqrt(M)*iw(.6)
    remainder=iv.sqrt(M)*(iv.exp(z)-iv.exp(-z))/2-M*iw(.6)
    # Implicit float conversion is avoided for the symmetric remainder.
    return dict(weighted_ricci=endpoints(total),jacobi_remainder=endpoints(remainder)[1],
                camera_readout=endpoints(g*(total+iw(-1,1)*remainder)),
                operator_bound=endpoints(M)[1])


def forecast(measured):
    g,b,d,kappa,f=calibrate(measured)
    A=iw(-.375)*kappa
    pm=(1+iv.sin(A*f))/2+iw(-.001,.001)
    return dict(gain=endpoints(g),clock_rate=endpoints(b),clock_offset=endpoints(d),
                kappa=endpoints(kappa),held_A=endpoints(A),matter=endpoints(pm),
                geometry={key:bound_geometry(A,xi,g,b,d)
                          for key,xi in (("minimal",iw(0)),("improved",iw(1)/6))})


def intersect(x,y):
    return max(x[0],y[0])<=min(x[1],y[1])


def score(fore,held):
    mp=held["matter_plus"]/N["matter"]
    matter= [mp-radius(N["matter"],1),mp+radius(N["matter"],1)]
    # Up to 8 independent coordinate errors per trial, coefficient 1/(2h).
    # McDiarmid/Hoeffding on 8*n independent bounded errors.
    rg=radius(N["geo"],.001*math.sqrt(8)/(2*H))
    geo=[held["geo_mean"]-rg,held["geo_mean"]+rg]
    np.testing.assert_allclose(statistic(np.array(held["frame_mean"])),held["geo_mean"],atol=4e-13)
    ok=intersect(fore["matter"],matter)
    return dict(held_matter_interval=matter,held_geo_interval=geo,
                source_consistent=ok,geometry_outcome={
                    k:("source_monitor_failed" if not ok else
                       "compatible" if intersect(v["camera_readout"],geo) else "rejected")
                    for k,v in fore["geometry"].items()})


def verlet(A,xi,b,d,cycles,substeps):
    # Independent direct position recurrence; no ODE solver or velocities in output.
    per_h=max(1,cycles)*substeps
    dt=H/per_h
    u=b*np.linspace(TIMES[0],TIMES[-1],12*per_h+1)+d
    k=np.array([curvature(t,A,xi) for t in u])
    w=.055*np.cos(3*u)
    if cycles:
        improved=np.array([curvature(t,A,1/6) for t in u])
        omega=2*np.pi*cycles/(b*H)
        ph=omega*(u-u[0])
        w+=omega*np.sqrt((improved-k)/2.5)*(np.cos(ph)-4*np.cos(2*ph))
    T=np.empty((len(u),2,2))
    T[:,0,0],T[:,1,1]=k+w,k-w
    T[:,0,1]=T[:,1,0]=.040*np.sin(4*u)
    T*=-(b*dt)**2
    prev=np.eye(2)
    cur=prev+.5*T[0]
    frames=[prev]
    for j in range(1,len(u)):
        if j in (per_h,11*per_h,12*per_h):
            frames.append(cur)
        if j+1<len(u):
            prev,cur=cur,2*cur-prev+T[j]@cur
    return np.array(frames)


def checks(fore,held):
    A,b,d=-.375,1.001,-.002
    minimal=paths(A,0,b,d)
    improved=paths(A,1/6,b,d)
    np.testing.assert_allclose(paths(-A,0,b,d),minimal,atol=1e-14)
    # Re-use the registered noise realization to test the opposite model in simulation.
    change=1.013*(improved-minimal)
    alt=dict(held,frame_mean=(np.array(held["frame_mean"])+change).tolist(),
             geo_mean=held["geo_mean"]+float(statistic(change)))
    alt_verdict=score(fore,alt)["geometry_outcome"]
    assert alt_verdict==dict(minimal="rejected",improved="compatible")
    signfail=score(fore,dict(held,matter_plus=N["matter"]-held["matter_plus"]))
    assert not signfail["source_consistent"]
    records=[]
    for cycles in (0,2,4,8):
        actual=paths(A,0,b,d,cycles,relative_tolerance=3e-10)
        v1=verlet(A,0,b,d,cycles,128)
        v2=verlet(A,0,b,d,cycles,256)
        extrapolated=v2+(v2-v1)/3
        cross=float(np.max(abs(actual-extrapolated)))
        if cross>3e-8:
            raise AssertionError(f"direct-ODE vs position recurrence {cycles=}, {cross=}")
        records.append(dict(cycles_per_chord=cycles,
                            absolute_max_coordinate_gap_to_improved=float(np.max(abs(actual-improved))),
                            signed_Y_gap_to_improved=float(statistic(actual)-statistic(improved)),
                            ODE_vs_independent_positions=cross))
    assert records[-1]["absolute_max_coordinate_gap_to_improved"]<3e-6
    assert records[0]["absolute_max_coordinate_gap_to_improved"]>.01
    from scipy.optimize import brentq
    clock=brentq(lambda beta:statistic(paths(A,1/6,beta,d))-statistic(minimal),.01,b)
    mp=(1+math.sin(A*quad(lambda t:profile(clock*t+d)[0],-.1,.1)[0]/.2))/2
    return dict(free_clock_absorbing_single_Y=clock,narrow_matter_p_at_free_clock=mp,
                equal_budget_standard_model="same Jacobi and Ramsey probabilities",
                improved_counterfactual=alt_verdict,flipped_matter_control=signfail["geometry_outcome"],
                free_camera_gain_absorbing_single_Y=1.013*statistic(minimal)/statistic(improved),
                unbounded_Weyl=records)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument("--predict-only",action="store_true")
    modes.add_argument("--check",action="store_true")
    args=parser.parse_args()
    cal=train_data()
    pred=forecast(cal)
    results=dict(calibration=cal,prediction=pred)
    if not args.predict_only:
        held=held_data()
        verdict=score(pred,held)
        assert verdict["geometry_outcome"]==dict(minimal="compatible",improved="rejected")
        results.update(held=held,verdict=verdict,crosschecks=checks(pred,held))
    if args.check:
        archived=json.loads((HERE/"result.json").read_text())
        def compare(a,b,path):
            if isinstance(b,dict):
                assert a.keys()==b.keys(),path
                for key,value in b.items():
                    compare(a[key],value,path+"."+key)
            elif isinstance(b,list):
                assert len(a)==len(b),path
                for j,value in enumerate(b):
                    compare(a[j],value,f"{path}[{j}]")
            elif isinstance(b,float):
                np.testing.assert_allclose(a,b,rtol=3e-9,atol=2e-10,err_msg=path)
            else:
                assert a==b,path
        compare(results,archived,"receipt")
        compare(dict(calibration=cal,prediction=pred),
                json.loads((HERE/"prediction.json").read_text()),"prediction")
        print("PASS: calibration, separate holdout, bounded and unrestricted Weyl controls.")
        return
    print(json.dumps(results,indent=2,allow_nan=False))

if __name__=="__main__":
    main()
