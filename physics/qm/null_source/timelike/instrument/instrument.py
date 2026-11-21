"""Two compact Ramsey sources inside the finite sphere's fixed normal-clock patch."""
import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import roots_legendre
from mpmath import iv

from joint_bound import certificate

HERE = Path(__file__).resolve().parent
R, GATE = .1, .05
WINS = [(1/32,1/16),(5/32,3/16)]
END = .25
BASIS_NORM = math.sqrt(2*math.pi**2)


def bump(x):
    if abs(x)>=1:
        return 0.
    return math.exp(-1/(1-x*x))


TIME_NORM = quad(bump,-1,1,epsabs=1e-14)[0]


def weight(t,pair,poly):
    lo,hi=pair
    x=(t-lo)/(hi-lo)
    if x<=0 or x>=1:
        return 0.
    return (30*x*x*(1-x)**2 if poly else 2*bump(2*x-1)/TIME_NORM)/(hi-lo)


def scale(t):
    return math.sqrt(3*math.cos(2*t))


def scalar(t):
    return math.sqrt(3)/2*math.atanh(math.sin(2*t))


def state_scale(t):
    # Only for specifying the incoming Gaussian Cauchy data of the local reference.
    if t>=-1/16:
        return scale(t)
    if t<=-1/8:
        return math.sqrt(3)
    x=16*(t+1/8)
    l,r=math.exp(-1/x),math.exp(-1/(1-x))
    return math.sqrt(3)+(scale(t)-math.sqrt(3))*l/(l+r)


def profile(n,radius,shell_center):
    chi,w=roots_legendre(200)
    lo,hi=max(0.,shell_center-radius),shell_center+radius
    chi=lo+(1+chi)*(hi-lo)/2
    w=w*(hi-lo)/2
    f=np.array([bump((t-shell_center)/radius) for t in chi])
    z=4*np.pi*np.sum(w*np.sin(chi)**2*f)
    f/=z
    fn=4*np.pi/BASIS_NORM*(np.sin(n[:,None]*chi)@(w*np.sin(chi)*f))
    assert abs(fn[0]-1/BASIS_NORM)<1e-13
    return fn,float(4*np.pi*np.sum(w*np.sin(chi)**2*f**2))


def evolve(last,poly=False,radius=R,shell_center=0.,local_only=False):
    n=np.arange(1,last+1)
    freq2=n*n-1
    fn,fnorm=profile(n,radius,shell_center)
    v=np.sqrt(np.maximum(1,freq2))
    a0=math.sqrt(3)
    u=1/(a0*np.sqrt(2*v))
    p=-1j*a0*np.sqrt(v/2)
    # State propagation plus independent inhomogeneous retarded solutions.
    y=np.zeros(8*last+7,dtype=complex)
    y[:last],y[last:2*last]=u,p
    def rhs(t,y):
        u,p,h1,p1,h2,p2,amp1,amp2=y[:-7].reshape(8,last)
        a=state_scale(t)
        w1,w2=(weight(t,win,poly) for win in WINS)
        j1,j2=GATE*w1*fn,GATE*w2*fn
        deriv=np.empty_like(y)
        deriv[:-7].reshape(8,last)[:]=[p/a**2,-a*a*freq2*u,
               p1/a**2,j1-a*a*freq2*h1,p2/a**2,j2-a*a*freq2*h2,j1*u,j2*u]
        rates=deriv[-7:]
        rates[:]=0.
        if t>=0:
            for i,(h,pr,j) in enumerate(((h1.real,p1.real,j1),(h2.real,p2.real,j2))):
                kinetic=pr@pr/(2*a**3)
                potential=a/2*(freq2*h)@h
                rates[2*i]=j@pr/a**3
                rates[2*i+1]=-math.tan(2*t)*(potential-3*kinetic)
            rates[4]=j2@h1.real
            rates[5]=j1@h2.real
            if not local_only:
                central=n@np.stack([p1.real,p2.real]).T/(BASIS_NORM*a**3)
                rates[6]=a*(4*(4*t)*(1-4*t))**4*(central@central)
        return deriv
    pts=[-1/8,-1/16,0.,*WINS[0],*WINS[1],END]
    saved=[]
    for lo,hi in zip(pts,pts[1:]):
        sol=solve_ivp(rhs,(lo,hi),y,method="DOP853",rtol=1e-10,atol=5e-14,
                      max_step=min(.002,1/last))
        if not sol.success:
            raise RuntimeError(sol.message)
        y=sol.y[:,-1]
        if hi>=WINS[0][1]:
            parts=y[:-7].reshape(8,last)
            central=(n@parts[[3,5]].real.T)/(BASIS_NORM*scale(hi)**3)
            saved.append({"eta":hi,"central_n_dh":central.tolist(),
                          "delta_SEC_central":float(central@central)})
    u,p,h1,p1,h2,p2,amp1,amp2=y[:-7].reshape(8,last)
    a=scale(END)
    # Fundamental positive-frequency mode is independent of the forced ODE.
    for h,pr,amp in [(h1,p1,amp1),(h2,p2,amp2)]:
        np.testing.assert_allclose(h.real,-2*np.imag(u*amp.conj()),atol=2e-10)
        np.testing.assert_allclose(pr.real,-2*np.imag(p*amp.conj()),atol=4e-9)
    np.testing.assert_allclose(-2*np.imag(u.conj()*p),1,rtol=2e-8)
    amps=np.array([amp1,amp2])
    cov=(amps@amps.conj().T).real
    ledger=y[-7:].real
    pair=float(ledger[4])
    np.testing.assert_allclose(pair,2*np.imag(amp1@amp2.conj()),atol=3e-10)
    assert abs(ledger[5])<1e-15
    if local_only:
        return cov[1,1],pair,float(ledger[2])
    es=[]
    for i,(h,pr) in enumerate(((h1.real,p1.real),(h2.real,p2.real))):
        energy=float(pr@pr/(2*a**3)+a/2*(freq2*h)@h)
        work,geometry=ledger[2*i:2*i+2]
        np.testing.assert_allclose(energy,work+geometry,atol=3e-10)
        rad=R+END-WINS[i][0]
        vol=2*np.pi*(rad-math.sin(2*rad)/2)*a**3
        bounds=[GATE**2/(2*vol),GATE**2*fnorm/(2*a**3)]
        assert bounds[0]<energy<bounds[1]
        es.append(dict(E=energy,switch_work=float(work),metric_work=float(geometry),
                       retarded_support_radius=rad,energy_bounds=bounds))
    means=[quad(lambda t:weight(t,win,poly)*scalar(t),*win,epsabs=1e-14)[0] for win in WINS]
    return dict(energy_by_gate=es,covariance=cov.tolist(),retarded_pair=pair,
                central_weighted_SEC=float(ledger[6]),reverse_pair=float(ledger[5]),means=means,spatial_L2_sq=fnorm,central=saved)


def output_table(run,relative=(1.,1.),sign=1,axes="YY"):
    factors=np.array(relative)
    mean=sign*GATE*factors*np.asarray(run["means"])
    cov=np.outer(factors,factors)*np.asarray(run["covariance"])
    comm=np.prod(factors)*run["retarded_pair"]
    branches=[(a,b) for a in (1,-1) for b in (1,-1)]
    rho=np.empty((4,4),complex)
    for i,(a,b) in enumerate(branches):
        for j,(c,d) in enumerate(branches):
            # U_cd^dagger U_ab; the ordered symplectic area retains time ordering.
            x=y=area=0
            for v,w in ((c,0),(0,d-b),(-a,0)):
                area+=x*w-y*v
                x,y=x+v,y+w
            v=np.array([x,y])
            rho[i,j]=np.exp(1j*(v@mean-comm*area/2)-(v@cov@v)/2)/4
    assert np.linalg.eigvalsh(rho).min()>-1e-12
    pauli={"X":np.array([[0,1],[1,0]]),"Y":np.array([[0,-1j],[1j,0]])}
    P=[[(np.eye(2)+s*pauli[ax])/2 for s in (1,-1)] for ax in axes]
    prob=np.array([[np.trace(rho@np.kron(a,b)).real for b in P[1]] for a in P[0]])
    assert prob.min()>-1e-13 and abs(prob.sum()-1)<2e-14
    visibles=np.exp(-2*np.diag(cov))
    single=visibles*(np.cos(2*mean) if axes=="XX" else np.sin(2*mean))
    if axes in ("XX","YY"):
        np.testing.assert_allclose([prob[0,:].sum(),prob[:,0].sum()],
                 (1+single*np.array([1.,np.cos(2*comm)]))/2,atol=1e-13)
    return prob.tolist()


def visibility_certificate():
    # Conservative low-mode proof, independent of the ultraviolet sum.
    a0,amin=math.sqrt(3),scale(END)
    variation_bound=((scale(-1/16)-scale(-1/8))+(a0-scale(-1/8)))/scale(-1/8)
    variation_bound+=math.log(a0/scale(-1/16))+math.log(a0/amin)
    assert variation_bound<.16
    lower=0.
    for n in range(2,24):
        v=math.sqrt(n*n-1)
        amp=1/(2*a0*math.exp(.16)*math.sqrt(v))-(1/64)*math.exp(.16)*math.sqrt(v)/amin
        fn=math.sin(n*R)/(R*BASIS_NORM)
        lower+=(fn*max(0.,amp))**2
    assert lower>.090 and math.exp(-2*3.25**2*.090)<.15
    return dict(log_scale_variation_upper=variation_bound,
                unit_variance_lower_low_modes=lower,strong_visibility_upper=.15)


def offset_transfer(mean):
    center,width=25/64,1/128
    chi_b=math.asin(1/math.sqrt(3))
    earliest=center-width+WINS[0][0]
    last_report=center+width+WINS[1][1]
    assert earliest>3/8 and last_report<chi_b
    # Characteristic functions and source work require only events in the known patch.
    out={}
    for name,rc in (("translated_small_ball",0.),("complete_radial_shell",center)):
        last=2048 if rc==0. else 1024
        var,pair,work=evolve(last,True,width,rc,local_only=True)
        alt=evolve(last//2,True,width,rc,local_only=True)
        partial=evolve(32,True,width,rc,local_only=True)[0]
        # Sharp spatial profile: original C1 time weight filters high modes.
        rel=1/(GATE*mean)
        log_v=-2*var*rel**2
        out[name]=dict(last_mode=last,standard_gate_maximal_t_at_visibility_floor=
                       2*mean*GATE*math.sqrt(-math.log(.2)/(2*var)),
                       first_32_mode_strong_visibility=math.exp(-2*partial*rel**2),
                       v_standard=math.exp(-2*var*(.5/GATE)**2),
                log_v_strong=log_v,v_strong=math.exp(log_v) if log_v>-700 else None,
                retarded_pair=pair,strong_switch_work=work*rel**2,
                log_visibility_refinement=abs(alt[0]-var)*2*rel**2,
                switch_work_refinement=abs(alt[2]-work)*rel**2)
        out[name]["new_single_second_gate"]=dose_menu(log_v,work*rel**2,mean)
        rows=out[name]["new_single_second_gate"]["rows"]
        assert all((r["robust_gap"]>0)==(rc!=0.) for r in rows), name
        if rc:
            assert out[name]["v_strong"]<.2
            assert rows[2]["total_launches"]<rows[1]["total_launches"]<rows[3]["total_launches"]
            assert rows[1]["total_nominal_switch_work"]<rows[2]["total_nominal_switch_work"]
    return dict(chi_b=chi_b,earliest_arrival=earliest,latest_direct_report=last_report,
                aperture_cases=out)


def dose_menu(log_v2,work2,mean):
    """One X readout of the second gate. Every launch enters the score."""
    s=-2/log_v2
    rows=[]
    for t in (1.,1.4,1.5,2.):
        phase=iv.mpf(str(t))*iv.mpf(["0.995","1.005"])
        # A calibrated additive visibility residual includes the transfer model error.
        transfer=iv.exp(log_v2*phase**2/4)+iv.mpf(["-.001",".001"])
        visibility=iv.mpf([max(0.,float(transfer.a)-1e-15),min(1.,float(transfer.b)+1e-15)])
        rotation=iv.cos(iv.mpf(["-.02",".02"]))
        chi=[iv.cos(iv.sqrt(3)*phase/2),(2+iv.cos(3*phase/2))/3]
        bands=[(1+visibility*rotation*z)/2+iv.mpf(["-.001",".001"]) for z in chi]
        ranges=[[float(z.a)-1e-14,float(z.b)+1e-14] for z in bands]
        gap=ranges[1][0]-ranges[0][1]
        count=math.ceil(2*math.log(80)/gap**2)+1 if gap>0 else None
        log_v=log_v2*t*t/4
        v=math.exp(log_v)
        ca,cb=math.cos(math.sqrt(3)*t/2),(2+math.cos(1.5*t))/3
        for (lo,hi),z in zip(ranges,(ca,cb)):
            assert lo<=(1+v*z)/2<=hi
        if count:
            assert 4*math.exp(-count*gap**2/2)<.05
        work=work2*t*t/4
        rows.append(dict(t=t,g=t/(2*mean),nominal_log_visibility=log_v,
            nominal_probability=[(1+v*ca)/2,(1+v*cb)/2],
            nominal_log_probability_gap=log_v+math.log(abs(cb-ca)/2),
            probability_ranges=ranges,robust_gap=gap,launches_per_arm=count,
            total_launches=2*count if count else None,switch_work_per_launch=work,
            total_nominal_switch_work=2*count*work if count else None))
    return dict(gain_relative_radius=.005,visibility_absolute_radius=.001,
                residual_phase_radius=.02,probability_bias_radius=.001,
                family_error_two_arms=.05,all_gain_nominal_AB_probability_gap_upper=.75*s*s*math.exp(-2),
                rows=rows)


def replay():
    coarse=evolve(512)
    run=evolve(1024)
    original=evolve(1024,poly=True)
    energy_diff=max(abs(x["E"]-y["E"]) for x,y in zip(coarse["energy_by_gate"],run["energy_by_gate"]))
    assert energy_diff<3e-5
    assert abs(run["retarded_pair"]-coarse["retarded_pair"])<5e-6
    for row in run["energy_by_gate"]:
        assert END+row["retarded_support_radius"]<math.asin(1/math.sqrt(3))
    for kind,info in [("smooth",run),("archived_weight",original)]:
        # q=2g is the coefficient of the Weyl phase, so W uses unit field smears.
        W=np.array(info["covariance"])/GATE**2
        m=np.array(info["means"])
        s=float(m@np.linalg.solve(W,m))
        info["joint_unit_gain"]=dict(W=W.tolist(),eigenvalues=np.linalg.eigvalsh(W).tolist(),
            s=s,optimal_q_per_t=(np.linalg.solve(W,m)/s).tolist(),peak_envelope_t=2*math.sqrt(s),
            all_gain_single_probability_gap_envelope=.75*s*s*math.exp(-2))
        info["YY_plus"]=output_table(info)
        info["YY_minus"]=output_table(info,sign=-1)
        info["XX_plus"]=output_table(info,axes="XX")
        info["XY_plus"]=output_table(info,axes="XY")
        info["YX_plus"]=output_table(info,axes="YX")
        np.testing.assert_allclose(info["YY_plus"],np.array(info["YY_minus"])[::-1,::-1],atol=1e-13)
        np.testing.assert_allclose(output_table(info,relative=(0,0)),np.ones((2,2))/4,atol=1e-14)
        std=.5/GATE
        strong=1/(info["means"][1]*GATE)  # 2*g*mu = 2.
        var=info["covariance"][1][1]
        vis=lambda r: math.exp(-2*var*r*r)
        second=info["energy_by_gate"][1]
        info["strength_test"]={"largest_t_at_visibility_floor":2*info["means"][1]*GATE*math.sqrt(-math.log(.2)/(2*var)),
            "standard_first_unread_multiplier_on_strong_second":math.cos(2*info["retarded_pair"]*std*strong),
            "standard_g":.5,"strong_g":GATE*strong,"ratio_to_standard":strong/std,
            "v_standard_second":vis(std),"v_strong_second":vis(strong),
            "v_standard_required":.2**((std/strong)**2),
            "v_strong_floor_met":vis(strong)>=.2,
            "log_v_strong":-2*var*strong**2,
            "strong_second_energy":second["E"]*strong**2,"strong_second_switch_work":second["switch_work"]*strong**2,
            "strong_second_energy_lower":second["energy_bounds"][0]*strong**2,
            "weak_first_unread_visibility_multiplier_on_strong_second":math.cos(2*info["retarded_pair"]*strong)}
    return dict(baseline="7437bd1dec7e84d229c015009b07d698d9739af8",g=GATE,
                cutoff_comparison_max_energy_difference=energy_diff,
                weighted_SEC_refinement=abs(coarse["central_weighted_SEC"]-run["central_weighted_SEC"]),
                low_mode_certificate=visibility_certificate(),joint_certificate=certificate(),
                offset=offset_transfer(original["means"][1]),smooth=run,archived_weight=original)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=replay()
    if args.check:
        archived=json.loads((HERE/"result.json").read_text())
        def check(a,b,path):
            if isinstance(b,dict):
                assert a.keys()==b.keys(),path
                for k in b:
                    check(a[k],b[k],path+"."+k)
            elif isinstance(b,list) and b and isinstance(b[0],dict):
                assert len(a)==len(b)
                for j,v in enumerate(b):
                    check(a[j],v,f"{path}[{j}]")
            elif b is None or isinstance(b,(str,bool)):
                assert a==b,path
            else:
                np.testing.assert_allclose(a,b,atol=1e-10,rtol=2e-7,err_msg=path)
        check(result,archived,"receipt")
        print("PASS: same-clock instrument, energy balance, low-mode joint bound and four A/B doses for both apertures.")
    else:
        print(json.dumps(result,indent=2,allow_nan=False))
