"""Independent geometric and contract audit for the overlap response increment.

Derives full four-dimensional tensor components directly. Does not import a
component checker, rerun an inherited checker, or integrate any mode ODE.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import subprocess
import sympy as s

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE="c57e2f411e58dc1dae60de8f3c97fbd680e46d8b"
PREFIX="physics/qm/null_source/timelike/"
OLD=[PREFIX+p for p in (
    "compatibility/CONTRACT.md","evolution/stress/README.md",
    "continuation/quantum/README.md","operational_response/CONTRACT.md",
    "operational_response/review.json")]+["physics/qm/status/CURRENT.json"]

def require(value,message):
    if not value: raise AssertionError(message)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(relative): return json.loads((HERE/relative).read_text())
def freeze():
    result={}
    for relative in OLD:
        p=REPO/relative
        archived=subprocess.check_output(["git","show",BASE+":"+relative],cwd=REPO)
        require(p.read_bytes()==archived,"Changed inherited science: "+relative)
        result[relative]=sha(p)
    paths=[HERE/p for p in ("review.py","README.md","CONTRACT.md","baseline_ci.json")]
    paths += [HERE/d/p for d in ("local","quantum","resolvent")
              for p in ("check.py","README.md","result.json")]
    for p in paths:result[str(p.relative_to(REPO))]=sha(p)
    return result

def full_geometry():
    t,x,p,q=s.symbols("t x p q",real=True)
    coords=(t,x,p,q); f=s.Function("f")(t); a=s.Function("a")(t)
    gamma=s.diag(1/(4*x*(1-x)),x,1-x)
    kv=s.Matrix([0,x,1-x])
    tau=s.simplify(kv*kv.T-gamma/3)
    S=lambda e:s.cancel(s.expand(e))
    def tensors(scale):
        g=s.diag(-scale**2,*[scale**2*gamma[i,i] for i in range(3)])
        gi=s.diag(*[1/g[i,i] for i in range(4)])
        h=s.zeros(4)
        for i,j in product(range(3),repeat=2):h[i+1,j+1]=scale**2*f*tau[i,j]
        dgi=-gi*h*gi
        @lru_cache(None)
        def G(i,j,k):
            return S(sum(gi[i,v]*(s.diff(g[v,k],coords[j])+s.diff(g[v,j],coords[k])-s.diff(g[j,k],coords[v]))/2 for v in range(4)))
        @lru_cache(None)
        def dG(i,j,k):
            return S(sum((dgi[i,v]*(s.diff(g[v,k],coords[j])+s.diff(g[v,j],coords[k])-s.diff(g[j,k],coords[v]))+gi[i,v]*(s.diff(h[v,k],coords[j])+s.diff(h[v,j],coords[k])-s.diff(h[j,k],coords[v])))/2 for v in range(4)))
        @lru_cache(None)
        def R(i,j,k,l):
            return S(s.diff(G(i,l,j),coords[k])-s.diff(G(i,k,j),coords[l])+sum(G(i,k,v)*G(v,l,j)-G(i,l,v)*G(v,k,j) for v in range(4)))
        @lru_cache(None)
        def dR(i,j,k,l):
            return S(s.diff(dG(i,l,j),coords[k])-s.diff(dG(i,k,j),coords[l])+sum(dG(i,k,v)*G(v,l,j)+G(i,k,v)*dG(v,l,j)-dG(i,l,v)*G(v,k,j)-G(i,l,v)*dG(v,k,j) for v in range(4)))
        Ric=s.Matrix(4,4,lambda j,l:S(sum(R(i,j,i,l) for i in range(4))))
        dRic=s.Matrix(4,4,lambda j,l:S(sum(dR(i,j,i,l) for i in range(4))))
        scalar=S(s.trace(gi*Ric));dscalar=S(s.trace(gi*dRic+dgi*Ric))
        assert dscalar==0
        return g,gi,h,dgi,G,dG,R,dR,Ric,dRic,scalar
    g,gi,h,dgi,G,dG,R,dR,Ric,dRic,scalar_curvature=tensors(s.Integer(1))
    assert scalar_curvature==6
    @lru_cache(None)
    def dC(i,j,k,l):
        r=sum(h[i,v]*R(v,j,k,l)+g[i,v]*dR(v,j,k,l) for v in range(4))
        z=(h[i,k]*Ric[l,j]+g[i,k]*dRic[l,j]-h[i,l]*Ric[k,j]-g[i,l]*dRic[k,j]-h[j,k]*Ric[l,i]-g[j,k]*dRic[l,i]+h[j,l]*Ric[k,i]+g[j,l]*dRic[k,i])/2
        z2=scalar_curvature*(h[i,k]*g[l,j]+g[i,k]*h[l,j]-h[i,l]*g[k,j]-g[i,l]*h[k,j])/6
        return S(r-z+z2)
    assert all(S(sum(gi[i,i]*dC(i,j,i,l)+dgi[i,i]*0 for i in range(4)))==0 for j,l in product(range(4),repeat=2))
    def covD(get,inds,der):
        value=s.diff(get(*inds),coords[der])
        for pos,idx in enumerate(inds):
            for v in range(4):
                c=G(v,der,idx)
                if c:
                    changed=list(inds);changed[pos]=v
                    value-=c*get(*changed)
        return S(value)
    def TT(i,j):
        return tau[i-1,j-1] if i>0 and j>0 else s.Integer(0)
    @lru_cache(None)
    def first_TT(i,j,k):
        return covD(TT,(i,j),k)
    assert S(sum(gi[i,i]*TT(i,i) for i in range(4))) == 0
    assert all(S(sum(gi[k,k]*first_TT(k,j,k) for k in range(4))) == 0 for j in range(4))
    for i,j in product(range(4),repeat=2):
        rough=S(sum(gi[k,k]*covD(first_TT,(i,j,k),k) for k in range(4)))
        assert S(rough+6*TT(i,j)) == 0
    assert S((kv.T*gamma.inv()*kv)[0]-1) == 0
    @lru_cache(None)
    def V(i,k,j):
        return S(sum(gi[d,d]*covD(dC,(i,k,j,d),d) for d in range(4)))
    HC=s.Matrix(4,4,lambda i,j:S(4*sum(gi[k,k]*covD(V,(i,k,j),k) for k in range(4))+2*sum(gi[k,k]*gi[d,d]*Ric[k,d]*dC(i,k,j,d) for k,d in product(range(4),repeat=2))))
    want=s.zeros(4);pol=s.diff(f,t,4)+20*s.diff(f,t,2)+64*f
    for i,j in product(range(3),repeat=2):want[i+1,j+1]=-pol*tau[i,j]
    assert HC.applyfunc(S)==want.applyfunc(S),(HC-want).applyfunc(S)
    g,gi,h,dgi,G,dG,R,dR,Ric,dRic,scalar_curvature=tensors(a)
    dRM=(gi*dRic+dgi*Ric).applyfunc(S)
    Hess=s.Matrix(4,4,lambda i,j:S(s.diff(scalar_curvature,coords[i],coords[j])-sum(G(v,i,j)*s.diff(scalar_curvature,coords[v]) for v in range(4))))
    dHess=s.Matrix(4,4,lambda i,j:S(-sum(dG(v,i,j)*s.diff(scalar_curvature,coords[v]) for v in range(4))))
    dHM=(gi*dHess+dgi*Hess).applyfunc(S)
    dHR=(2*scalar_curvature*dRM-2*dHM).applyfunc(S)
    DT=s.diff(f,t,2)+2*s.diff(a,t)/a*s.diff(f,t)+8*f
    TM=gamma.inv()*tau
    wantRM=s.zeros(4);wantHR=s.zeros(4)
    for i,j in product(range(3),repeat=2):
        wantRM[i+1,j+1]=DT*TM[i,j]/(2*a**2)
        wantHR[i+1,j+1]=(scalar_curvature*DT+s.diff(scalar_curvature,t)*s.diff(f,t))*TM[i,j]/a**2
    assert (dRM-wantRM).applyfunc(S)==s.zeros(4)
    assert (dHR-wantHR).applyfunc(S)==s.zeros(4)
    assert S(scalar_curvature-6*(s.diff(a,t,2)+a)/a**3)==0

    return {
        "route":"full four-dimensional Christoffel, Riemann, Ricci, Weyl and double covariant divergence",
        "Hopf_TT":"tau=K_flat tensor K_flat-gamma/3; K=partial_phi+partial_psi, unit global Hopf Killing field",
        "trace_zero":True,"divergence_zero":True,"rough_laplacian_eigenvalue":6,
        "cylinder_Bach_all_components":True,"Bach_00_and_0i_zero":True,
        "l2_operator_coefficients":[1,20,64],
        "generic_a_mixed_Ricci_variation":True,"generic_a_mixed_R2_variation":True,
        "scalar_curvature":"6*(a_second+a)/a^3",
        "imports_component_checker":False,"new_geometry_ODE_integrations":0}


def prescription_audit(local, quantum, resolvent):
    compatibility=(REPO/(PREFIX+"compatibility/CONTRACT.md")).read_text()
    stress=(REPO/(PREFIX+"evolution/stress/README.md")).read_text()
    require(r"\mu=1" in compatibility and r"\alpha=0" in compatibility,
            "Inherited mu and alpha were not recovered from the actual source")
    require("没有额外有限曲率项" in stress,"The no-extra-curvature contract changed")
    metric,ric,curvature,hessian,box=s.symbols("metric ric curvature hessian box")
    HR=2*curvature*ric-metric*curvature**2/2+2*(metric*box-hessian)
    HAE=2*hessian-2*(-metric)*(-box)-(-metric)*curvature**2/2+2*curvature*(-ric)
    require(s.expand(HAE+HR)==0,"AE-to-current complete tensor sign conversion")
    inherited=local["inherited_prescription"]
    require([inherited[k] for k in ("physical_mu","alpha_AE","Einstein_z","b_extra","c_extra")]
            ==[1,0,1,0,0],"Physical workpoint was reopened")
    require(not inherited["reference_TT_contacts_set_to_zero"],"Reference contacts silently dropped")
    qren=quantum["renormalization"]
    require(qren["inherited_physical_mu"]==1 and qren["inherited_alpha"]==0 and qren["c_extra"]==0,
            "Quantum prescription mismatch")
    require(not qren["new_finite_counterterms_added"] and not qren["reference_contacts_assumed_zero"],
            "Quantum reference contacts conflated with extra couplings")
    rp=resolvent["inherited_physical_point"]
    require([rp[k] for k in ("physical_mu","alpha_AE","z","b_extra","c_extra")]==[1,0,1,0,0],
            "Local inverse changed physical workpoint")
    require(not rp["four_data_of_explicit_nonzero_c_family_imposed_here"],
            "Auxiliary fourth-order data imposed on fixed physical workpoint")
    require(not resolvent["high_frequency_obstruction"]["applies_at_physical_workpoint"],
            "Nonzero deformation counterexample applied to vanishing extra coefficient")
    return {"physical_mu":1,"alpha_AE":0,"Einstein_z":1,"b_extra":0,"c_extra":0,
        "AE_H1_equals_minus_HR":True,"extra_couplings_reopened":False,
        "reference_contacts_assumed_zero":False,
        "actual_equation":"D_T h - 4 a_lambda^2 Pi_ref_TT[h] = 4 a_lambda^2 F"}

def independent_kernels(quantum,resolvent):
    u,p=s.symbols("u p",positive=True)
    ell=s.symbols("ell",integer=True,positive=True)
    # Independent Laplace factorization of the retarded Green kernel.
    transform=(1/(p*p+ell**2)-1/(p*p+(ell+2)**2))/(4*(ell+1))
    require(s.cancel(transform-1/((p*p+ell**2)*(p*p+(ell+2)**2)))==0,
            "Green normalization fails independent Laplace factorization")
    G=(s.sin(ell*u)/ell-s.sin((ell+2)*u)/(ell+2))/(4*(ell+1))
    jets=[s.simplify(s.diff(G,u,j).subs(u,0)) for j in range(4)]
    require(jets==[0,0,0,1],"Green zero-past data")
    for n in (2,3,17):
        Gn=G.subs(ell,n)
        require(s.expand(s.diff(Gn,u,4)+(2*n*(n+2)+4)*s.diff(Gn,u,2)
                         +(n*(n+2))**2*Gn)==0,"Four-dimensional reviewed operator / Green mismatch")
    # Independently derive convolution majorants with beta-polynomial integrals.
    v=s.symbols("v",nonnegative=True)
    for n in range(7):
        actual=s.integrate((u-v)*v**(2*n+3)/s.factorial(2*n+3),(v,0,u))
        require(s.simplify(actual-u**(2*n+5)/s.factorial(2*n+5))==0,"Volterra factorial majorant")
    # Rational Machin enclosure of pi is independent of the component's iv.pi.
    def atan_interval(x,terms=80):
        value=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(terms)),F(0))
        nextterm=(-1)**terms*x**(2*terms+1)/F(2*terms+1)
        return min(value,value+nextterm),max(value,value+nextterm)
    a0,a1=atan_interval(F(1,5));b0,b1=atan_interval(F(1,239))
    pi0,pi1=16*a0-4*b1,16*a1-4*b0
    beta0,beta1=1/(1920*pi1*pi1),1/(1920*pi0*pi0)
    advertised=list(map(F,quantum["physical_UV"]["beta_T_interval"]))
    require(advertised[0]<=beta0<beta1<=advertised[1],"UV interval missed independent rational pi enclosure")
    require(pi1*pi1<10,"Rational pi bound")
    spectral=s.Rational(1,60)*s.Rational(1,16)
    require(spectral/2==s.Rational(1,1920),"Spin-2 spectral/RSET factor two")
    state=quantum["Hadamard_state_difference"]
    require(state["input_vanishes_before_interval_start"],"Omitted previous forcing")
    require("SO(4)" in state["spatial_symmetry_for_scalar_contact"],"Local scalar contact needs spatial symmetry")
    require(state["zero_response_requires_pure_spatial_zero_mode_difference"] and
            not state["generic_SO4_invariant_state_difference_claimed_blind"],"Zero-mode blindness scope")
    require(F(state["full_bound_per_M8"][1])<F(275,468),
            "State-difference coefficient exceeds independent rational energy bound")
    # CE <= exp(3/16) <= 16/13, pi^2<10.
    require(F(10,6)*(F(16,13)/64+F(1,3))==F(275,468),"Independent complete state-difference cap")
    require(not state["actual_prepared_reference_difference_M8_numerically_certified"],
            "Uncomputed state norm silently certified")
    previous_epsilon=None
    for row in quantum["finite_part"]["cutoff_checks"]:
        require(F(row["absolute_difference_upper"][1])<=F(row["analytic_cutoff_error_upper"][0]),
                "Causal finite-part cutoff error failed")
        epsilon=F(row["epsilon"])
        require(previous_epsilon is None or epsilon<previous_epsilon,"Cutoff refinements not ordered")
        previous_epsilon=epsilon
    require(quantum["log_inverse"]["positive_real_pole"] and
            not quantum["log_inverse"]["stable_inverse_claimed"],"Growing pole omitted or stability overstated")
    # Exact spectral scale compensation and derivative-loss negative control.
    scale,beta,c,z=s.symbols("scale beta c z")
    require(s.expand(c+2*beta*scale+beta*(z-2*scale)-(c+beta*z))==0,"Logarithmic contact compensation")
    require(s.expand(c+beta*(z-2*scale)-(c+beta*z))==-2*beta*scale,
            "Uncompensated scale change must remain visible")
    cc=resolvent["constant_family"]
    require(cc["high_frequency_residual_cap_times_lambda2"]=="20" and
            cc["high_frequency_multiplication_cap_times_lambda2"]=="12","Local counterexample remainder constants")
    t=F(3,16);cosine=1-F(3,8)**2/2;r=1/cosine
    require(F(3,4)*32768**2==805306368,"Gamma coefficient")
    require((F(3,4)+t/2*F(3,2)*F(3,8))*32768**2==861929472,"A Einstein coefficient")
    require(6*r*r+t/2*24*F(3,8)*r**3==F(13467648,1685159),"A R2 coefficient")
    return {"Green_Laplace_factorization":True,"Green_initial_jets":[int(j) for j in jets],
        "Green_against_independent_l2_Bach":True,"Volterra_factorial_convolutions":True,
        "UV_beta_T_independent_rational_Machin_pi_enclosure":True,
        "spin2_spectral_RSET_normalization":True,
        "state_difference_full_geometric_coefficient_upper":str(F(275,468)),
        "state_difference_before_start_input_zero_required":True,
        "pure_zero_mode_blindness_not_generic_homogeneity":True,
        "logarithmic_scale_negative_control":True,"growth_pole_retained":True,
        "auxiliary_local_constants_and_domain":True}

def calculate():
    require(__debug__,"Scientific assertions disabled")
    frozen=freeze()
    local,quantum,resolvent=[read(d+"/result.json") for d in ("local","quantum","resolvent")]
    require(local["status"]=="EXACT_GENERAL_TT_WEYL_BACH_OPERATOR_VERIFIED","Local result did not pass")
    require(quantum["status"]=="CAUSAL_LOG_FINITE_PART_EXACT_NORMAL_FORM_INVERSE_AND_OVERLAP_STATE_DIFFERENCE",
            "Quantum result did not pass")
    require(resolvent["status"]=="EXPLICIT_LOCAL_PARAMETER_FAMILY_RESOLVENT_AND_GAIN_OBSTRUCTION_CERTIFIED",
            "Explicit local inverse did not pass")
    for value in (local,quantum,resolvent):
        for relative,expected in value["input_sha256"].items():
            require(sha(REPO/relative)==expected,"Component receipt source mismatch: "+relative)
    prescription=prescription_audit(local,quantum,resolvent)
    geometry=full_geometry()
    kernels=independent_kernels(quantum,resolvent)
    require(not quantum["scope"]["complete_quantum_feedback_resolvent_certified"] and
            not resolvent["scope"]["full_quantum_retarded_RSET_operator_inverted"],
            "Full quantum feedback falsely closed")
    result={
        "schema":"ueot-overlap-primary-review/1","status":"PASS","base_commit":BASE,
        "physical_prescription":prescription,"independent_geometry":geometry,
        "independent_kernels_and_constants":kernels,
        "local_geometry":{"full_closed_FLRW_Weyl_operator":True,"mixed_R2_operator":True,
            "all_l_factorization":"(d_eta^2+l^2)(d_eta^2+(l+2)^2)"},
        "quantum_overlap":{"causal_log_finite_part_defined":True,
            "scalar_log_normal_form_exact_causal_inverse":True,
            "scalar_log_inverse_stable":False,
            "same_background_state_difference_Volterra_theorem":True,
            "actual_state_difference_M8_certified":False,
            "homogeneous_displacement_effective_TT_difference_zero":True,
            "raw_covariant_pressure_contact_discarded":False},
        "explicit_local_family":{"all_mode_finite_time_retarded_inverse":True,
            "requires_nonzero_extra_c":True,"applies_at_fixed_physical_point":False,
            "nonzero_C2_after_old_D_inverse_same_space_unbounded":True},
        "scope":{"full_quantum_feedback_resolvent":False,"full_nonlinear_SCE_solution":False,
            "full_quantum_noise_propagated_to_geometry":False,
            "fixed_reference_contacts_fully_assembled":False,
            "new_Lean_proofs":False,"new_matching_hardware_data":False,
            "Core_unique_physical_selection":False,"Core_read_only_GI_excluded":True},
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "old_scientific_checkers_executed":0,"input_sha256":frozen}
    require(frozen==freeze(),"Inputs changed during primary review")
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true");parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    if not (args.write or args.check):parser.error("use --write and/or --check")
    value=calculate()
    rendered=json.dumps(value,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"review.json"
    if args.write:target.write_text(rendered,encoding="utf-8")
    if args.check:require(target.read_text(encoding="utf-8")==rendered,"Primary review receipt mismatch")
    print("PASS: independent full 4D Hopf Bach/R2 tensors, preserved physical prescription, causal kernels and scope.")
    print("OPEN: complete fixed-reference TT polarization, full quantum feedback and nonlinear SCE.")
