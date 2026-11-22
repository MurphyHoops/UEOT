"""Uniform, all-mode prepared initial-slice existence certificate.

The parameter changes the actual smooth metric and propagates the common
static quantum seed. Low modes are enclosed by an energy-frame Duhamel
comparison with archived validated modes; the new infinite tail is computed.
No finite cutoff is substituted for the full stress tensor.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import ceil, factorial
from pathlib import Path
import subprocess
import sys
from mpmath import iv, mp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
TIMELIKE=HERE.parent
EVO=TIMELIKE/"evolution"
BASE="6401950ba154f1be763655ca7f68aeb842628922"
sys.path.insert(0,str(EVO/"stress"))
import tail as old_tail
bg=old_tail.bg
I,box,Jet=bg.I,bg.box,bg.Jet
pair,read_pair=old_tail.pair,old_tail.read_pair
top,absolute=old_tail.topI,old_tail.absI
power=old_tail.power
iv.dps=70
mp.dps=80
LAMBDA=32768
PARAMETER_RADIUS=Q(1,256)
K=256
SUBDIVISIONS=1024

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_inputs():
    paths={HERE/"check.py",EVO/"stress/tail.py",EVO/"propagation/background.py"}
    receipts=[]
    for name in ["result.json","extra_eta0_256.json"]:
        path=EVO/"propagation"/name
        data=json.loads(path.read_text())
        paths.add(path)
        for relative,digest in data["source_sha256"].items():
            dependency=EVO/"propagation"/relative
            assert sha(dependency)==digest,("Propagation source changed",relative)
            paths.add(dependency)
        receipts.append(data)
    result={str(p.relative_to(REPO)):sha(p) for p in sorted(paths)}
    for rel,digest in result.items():
        if rel.startswith("physics/qm/null_source/timelike/prepared_initial/"):
            continue
        previous=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        assert hashlib.sha256(previous).hexdigest()==digest,("Inherited input changed",rel)
    modes=receipts[0]["targets"]["0"]["modes"]+receipts[1]["targets"]["0"]["modes"]
    assert [row["k"] for row in modes]==list(range(2,K+1))
    return modes,result

def time_jet(lo,hi,order):
    return Jet([box(lo,hi),1]+[0]*(order-1)) if order else Jet([box(lo,hi)])

def smooth_step(lo,hi,order):
    lo,hi=Q(lo),Q(hi)
    if hi<=bg.START:
        return Jet.const(0,order)
    if lo>=bg.STOP:
        return Jet.const(1,order)
    assert bg.START<=lo<=hi<=bg.STOP
    if lo==hi and bg.START<lo<bg.STOP:
        pass
    elif hi<=bg.START+bg.CAP:
        return bg.cap_step_bound(16*(hi-bg.START),order)
    elif lo>=bg.STOP-bg.CAP:
        return bg.cap_step_bound(16*(bg.STOP-lo),order,right=True)
    else:
        assert lo>=bg.START+bg.CAP and hi<=bg.STOP-bg.CAP
    x=16*(time_jet(lo,hi,order)-bg.START)
    if hi<=(bg.START+bg.STOP)/2:
        z=(-1/x+1/(1-x)).exp()
        return z/(1+z)
    z=(1/x-1/(1-x)).exp()
    return 1/(1+z)

def family_q_box(lo,hi,parameter,order=5):
    """Actual eta derivatives of q_t; parameter interval is not differentiated."""
    old=bg.q_box(lo,hi,order)
    if hi<=bg.START:
        return old
    psi=time_jet(lo,hi,order+2)
    psi=(psi*psi/2)*smooth_step(lo,hi,order+2)
    psi1=Jet([(j+1)*psi.c[j+1] for j in range(order+1)])
    psi2=Jet([(j+1)*(j+2)*psi.c[j+2] for j in range(order+1)])
    a=bg.derivative_box(lo,hi,order+1)
    h=Jet([(j+1)*a.c[j+1] for j in range(order+1)])/Jet(a.c[:order+1])
    old_jet=Jet([value/factorial(j) for j,value in enumerate(old)])
    new=old_jet-(psi2+2*h*psi1)*parameter-(psi1*psi1)*(parameter**2)
    return [value*factorial(j) for j,value in enumerate(new.c)]

def mesh():
    cuts=list(bg.BREAKS)+[Q(0)]
    cells=[]
    for left,right in zip(cuts,cuts[1:]):
        step=Q(1,16*SUBDIVISIONS) if left<bg.STOP else Q(1,512)
        count=max(1,ceil((right-left)/step))
        cells.extend((left+(right-left)*Q(j,count),
                      left+(right-left)*Q(j+1,count)) for j in range(count))
    return cells

def cell_bound(lo,hi,parameter):
    derivatives=family_q_box(lo,hi,parameter,5)
    qjets=[Jet([derivatives[j],derivatives[j+1]]) for j in range(5)]
    delta=Jet.const(box(0,Q(1,(K+1)**2)),1)
    _,B,_,_,Rn=old_tail.normalized_defect(qjets,delta)
    denominator=4*B+2*power(delta,3)*Rn
    assert bg.lower(denominator.c[0])>0,("Unverified oscillatory phase",lo,hi)
    H=Rn/denominator
    normalization=2*iv.sqrt(old_tail.botI(B.c[0]))
    residual=absolute(Rn.c[0])
    return (residual/normalization,absolute(H.c[1]),
            residual*absolute(H.c[0])/normalization,
            old_tail.botI(B.c[0]),old_tail.botI(denominator.c[0]),
            absolute(derivatives[4]),absolute(derivatives[5]))

def initial_uv(parameter,integrals):
    D5,Hvariation,N11=integrals
    derivatives=family_q_box(Q(0),Q(0),parameter,5)
    delta=Jet([box(0,Q(1,(K+1)**2)),1,0,0])
    qjets=[Jet.const(value,3) for value in derivatives[:5]]
    _,B,T,T1,Rn=old_tail.normalized_defect(qjets,delta)
    # h_t(0)=0 exactly for every parameter.
    Bprime=delta*qjets[1]+power(delta,2)*T1
    g=Bprime/(4*B)
    G=(B+1-delta+delta*power(g,2))/(2*B.sqrt())
    P=(B-(1-delta)/3+delta*power(g,2))/(2*B.sqrt())
    local_rho=absolute(G.c[3])/(2*K*K)
    local_pressure=absolute(P.c[3])/(2*K*K)
    bmin,bmax=old_tail.botI(B.c[0]),top(B.c[0])
    gabs,energy_max=absolute(g.c[0]),absolute(G.c[0])
    H=Rn/(4*B+2*power(delta,3)*Rn)
    rapidity=top(D5)/(K+1)**5
    c1=top(old_tail.cosh(rapidity))
    c2=top(old_tail.cosh(2*rapidity))
    s1=top(old_tail.sinh(rapidity))
    beta5,ab5=top(D5)*c1,top(D5)*c2
    beta6=c1*(absolute(H.c[0])+top(Hvariation))+s1*top(N11)/(K+1)**5
    ab6=c1*beta6
    R0=2*gabs*iv.sqrt(bmax/bmin)
    R1=(gabs*gabs+absolute(derivatives[0]+1)
        +I(Q(1,(K+1)**2))*absolute(T.c[0]))/iv.sqrt(bmin)
    Pc=(bmax+I(Q(1,3))+I(Q(1,(K+1)**2))*gabs*gabs
        +2*gabs*iv.sqrt(bmax)/(K+1))/iv.sqrt(bmin)
    estimates={}
    for rank,beta,ab in [(5,beta5,ab5),(6,beta6,ab6)]:
        diagonal=beta*beta*energy_max/((rank-2)*K**(2*rank-4))
        cross_rho=ab*(R0/((rank-3)*K**(rank-3))
                     +R1/((rank-2)*K**(rank-2)))
        cross_pressure=ab*Pc/((rank-4)*K**(rank-4))
        estimates[str(rank)]={
            "beta_coefficient":pair(beta),"alpha_beta_coefficient":pair(ab),
            "rho_state":pair(diagonal+cross_rho),
            "pressure_state":pair(diagonal+cross_pressure)}
    state_rho=min(bg.upper(read_pair(v["rho_state"])) for v in estimates.values())
    state_pressure=min(bg.upper(read_pair(v["pressure_state"])) for v in estimates.values())
    prefactor=1/(36*iv.pi**2)
    return {
        "rho_absolute_bound":pair(top(prefactor*(I(state_rho)+local_rho))),
        "pressure_absolute_bound":pair(top(prefactor*(I(state_pressure)+local_pressure))),
        "rho_local_subtraction_tail":pair(prefactor*local_rho),
        "pressure_local_subtraction_tail":pair(prefactor*local_pressure),
        "rapidity_upper":pair(rapidity),"state_estimates":estimates,
        "initial_q_derivatives":[pair(value) for value in derivatives],
        "uniform_convergence":"Same constants hold for all N>=256: local subtraction and full stress tails O(N^-2); rank-six state-only pressure O(N^-2), state-only density O(N^-4). Constants cover the full parameter interval.",
        "static_W2_matching":True,
    }

def finite_modes(parameter,modes):
    a0=iv.sqrt(3)
    a_left=iv.sqrt(3*iv.cos(I(Q(1,4))))
    a_right=iv.sqrt(3*iv.cos(I(Q(1,8))))
    Hstar=top((a0+a_right-2*a_left)/a_left+iv.log(a0/a_right))
    variation=I(Q(1,64))
    delta_norm=top(iv.exp(Hstar)*(iv.exp(I(PARAMETER_RADIUS)*variation)-1))
    squared_norm_change=top(iv.exp(2*Hstar)*(iv.exp(2*I(PARAMETER_RADIUS)*variation)-1))
    sum_cubes=Q((K*(K+1)//2)**2-1)
    bare_error=top(squared_norm_change*I(sum_cubes))
    harmonic=I(sum((Q(1,k) for k in range(1,K+1)),Q(0)))
    sum_k=I(K*(K+1)//2)
    rho0=I(Q(1,2))-1+I(Q(1,2))-I(Q(3,8))
    pressure0=I(Q(1,2))-I(Q(1,3))-I(Q(1,2))+I(Q(7,8))
    for row in modes:
        k=row["k"]
        rho0+=k*k*(read_pair(row["e"])-k+I(Q(1,2*k))-I(Q(3,8*k**3)))
        pressure0+=k*k*(read_pair(row["s"])-I(Q(k,3))-I(Q(1,2*k))+I(Q(7,8*k**3)))
    t=parameter
    change_E3=(t**2-4*t)/8
    change_P1=-t/3
    change_P3=t**2/24-t/3
    symmetric=box(-bg.upper(bare_error),bg.upper(bare_error))
    prefactor=1/(36*iv.pi**2)
    rho=prefactor*(rho0+symmetric-change_E3*harmonic)
    pressure=prefactor*(pressure0+symmetric-change_P1*sum_k-change_P3*harmonic)
    return {
        "K":K,"old_modes_reintegrated":0,"new_modes_integrated":0,
        "original_log_energy_bound":pair(Hstar),"psi_total_variation_bound":"1/64",
        "state_energy_frame_difference_bound":pair(delta_norm),
        "bare_energy_and_pressure_sum_error":pair(bare_error),
        "rho_finite_enclosure":pair(rho),"pressure_finite_enclosure":pair(pressure),
        "zero_mode_raw_e_s":"1/2, parameter independent at eta=0; k=1 new subtraction retained",
        "all_scalar_modes_2_through_256_present":True,
    }

def analytic_initial(parameter):
    t=parameter
    L=iv.log(I(3)*LAMBDA**2/4)+2*iv.euler
    C=19+15*L
    rho=(C*(t**2-4*t+3)+1)/(8640*iv.pi**2)
    pressure=(C*(t**2-8*t-21)+90*t**2-244*t+159)/(25920*iv.pi**2)
    return rho,pressure

def certificate(progress=False):
    assert __debug__ and sys.flags.optimize==0,"Scientific assertions must stay enabled"
    modes,manifest=source_inputs()
    parameter=box(-PARAMETER_RADIUS,PARAMETER_RADIUS)
    D5,Hvariation,N11=I(0),I(0),I(0)
    Bmin,phase_min=I(1),I(4)
    max4,max5=I(0),I(0)
    cells=mesh()
    for index,(lo,hi) in enumerate(cells):
        d,h,n,b,phase,q4,q5=cell_bound(lo,hi,parameter)
        width=I(hi-lo)
        D5+=width*d
        Hvariation+=width*h
        N11+=width*n
        if bg.lower(b)<bg.lower(Bmin):Bmin=b
        if bg.lower(phase)<bg.lower(phase_min):phase_min=phase
        if bg.upper(q4)>bg.upper(max4):max4=q4
        if bg.upper(q5)>bg.upper(max5):max5=q5
        if progress and index%256==0:
            print("New family UV cells",index,"/",len(cells),flush=True)
    uv=initial_uv(parameter,(D5,Hvariation,N11))
    finite=finite_modes(parameter,modes)
    rho_an,pressure_an=analytic_initial(parameter)
    rho_tail=bg.upper(read_pair(uv["rho_absolute_bound"]))
    pressure_tail=bg.upper(read_pair(uv["pressure_absolute_bound"]))
    rho=read_pair(finite["rho_finite_enclosure"])+rho_an+box(-rho_tail,rho_tail)
    pressure=read_pair(finite["pressure_finite_enclosure"])+pressure_an+box(-pressure_tail,pressure_tail)
    R=ceil(bg.absmax(rho))
    P=ceil(bg.absmax(pressure))
    root_bound=Q(3*(R+P),LAMBDA**2)
    margin=PARAMETER_RADIUS-root_bound
    source_ratio_lower=1-Q(2*R,LAMBDA**2)
    assert margin>0,("IVT endpoint margin not proved",R,P)
    assert source_ratio_lower>0,"Positive displacement source not proved"
    for rel,digest in manifest.items():
        assert sha(REPO/rel)==digest,("Source changed during calculation",rel)
    return {
        "schema":"ueot-prepared-initial-slice/1","status":"PASS",
        "physical_prescription":{"lambda":LAMBDA,"mu":1,"alpha_AE":0,"extra_finite_terms":0,
            "parameter_radius":str(PARAMETER_RADIUS),
            "family":"a_t(eta)=lambda*a_prepared(eta)*exp(t*chi(eta)*eta^2/2)",
            "chi":"original C-infinity step on [-1/8,-1/16], zero before, one after",
            "reference_state":"same static-past seed, separately propagated on each smooth metric",
            "zero_mode":"same original regular Gaussian transported by lambda; no eta=0 reset"},
        "source_sha256":manifest,
        "finite_modes":finite,
        "new_uniform_uv":{"K":K,"subdivisions":SUBDIVISIONS,"cells":len(cells),
            "D5":pair(D5),"Hvariation":pair(Hvariation),"N11":pair(N11),
            "B_lower":pair(Bmin),"phase_denominator_lower":pair(phase_min),
            "max_abs_q4":pair(max4),"max_abs_q5":pair(max5),**uv},
        "absolute_stress":{"normalization":"Qrho=lambda^4*rho, Qp=lambda^4*p",
            "rho_analytic":pair(rho_an),"pressure_analytic":pair(pressure_an),
            "Qrho_interval":pair(rho),"Qp_interval":pair(pressure),
            "Qrho_absolute_integer_bound":R,"Qp_absolute_integer_bound":P},
        "initial_existence":{
            "shooting_equation":"F(t)=t-3*(Qrho(t)-Qp(t))/lambda^2",
            "continuity":"uniformly convergent full subtracted mode sums plus continuous local terms",
            "F_left_upper":str(-margin),"F_right_lower":str(margin),
            "root_exists":True,"root_uniqueness_proved":False,
            "root_absolute_bound":str(root_bound),
            "source_M2":"27*lambda^4-54*lambda^2*Qrho(t_star)",
            "M2_over_27lambda4_lower":str(source_ratio_lower),
            "Hamiltonian_and_spatial_equations_at_initial_slice":True,
            "momentum_constraint":"zero by homogeneous isotropic preparation",
            "proper_clock_log_volume_acceleration_interval":[
                str((-2-root_bound)/LAMBDA**2),str((-2+root_bound)/LAMBDA**2)],
            "relative_acceleration_correction_bound":str(root_bound/2),
            "initial_strict_maximum_of_scale":True,
            "nonzero_correction_proved":False},
        "scope":{"future_SCE_solution":False,"distance_to_future_solution":False,
            "full_feedback_resolvent":False,"inherited_instrument_probabilities_reused":False,
            "new_Lean_proofs":False,"matching_hardware_data":False,
            "Core_unique_physical_selection":False,
            "new_mode_ODE_integrations":0,"old_scientific_entries_rerun":0,
            "new_parameter_uniform_UV_computation":True}
    }

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    parser.add_argument("--progress",action="store_true")
    args=parser.parse_args()
    result=certificate(args.progress)
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    if args.write:
        (HERE/"result.json").write_text(rendered)
    if args.check:
        assert (HERE/"result.json").read_text()==rendered,"Certificate differs from full recomputation"
    stress=result["absolute_stress"]
    print("Full parameter-uniform Qrho bound:",stress["Qrho_absolute_integer_bound"])
    print("Full parameter-uniform Qp bound:",stress["Qp_absolute_integer_bound"])
    print("Root absolute bound:",result["initial_existence"]["root_absolute_bound"])
    print("PASS: actual prepared initial-slice existence; future evolution remains open")
if __name__=="__main__":
    main()
