"""Calibrate the archived local TT readout with certified radial integrals.

The signal is a specified external profile in the declared forced linear
tensor model. The induced covariance remains that of the archived background.
No nonlinear metric or perturbed-state quantum-noise claim is made.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import comb
import argparse,hashlib,json,subprocess
from mpmath import iv,mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
TL=HERE.parents[1]
BASE="f2b09fb2b8fd2235bde7017b060fc07ecc44b441"
M=7640
iv.dps=65
mp.dps=90

def I(x):
    if hasattr(x,"_mpi_"):return x
    if isinstance(x,mp.mpf):return iv.mpf(x)
    x=F(x);return iv.mpf(x.numerator)/x.denominator
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def lo(x):return F(pair(x)[0])
def hi(x):return F(pair(x)[1])
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))
def lower(x):return I(endpoint(x,0))
def ceilf(x):return -(-x.numerator//x.denominator)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def frozen_inputs():
    paths=[TL/"metric_response/tensor"/f for f in ["check.py","README.md","result.json"]]
    paths += [TL/"stress_kernel/noise/result.json",TL/"metric_response/verification.json"]
    result={}
    for p in paths:
        assert p.read_bytes()==subprocess.check_output(
            ["git","show",BASE+":"+str(p.relative_to(REPO))],cwd=REPO)
        result[p]=sha(p)
    for f in ["check.py","README.md"]:result[HERE/f]=sha(HERE/f)
    return result

def symbolic_polynomials():
    x=sp.symbols("x y z",real=True);v=sp.symbols("v",real=True)
    s=sp.symbols("s",real=True);f=sp.Function("f")(*x)
    seed=sp.diag(f,-f,0)
    ric=sp.Matrix(3,3,lambda i,j:sp.expand(sum(
        sp.diff(seed[k,j],x[i],x[k])+sp.diff(seed[k,i],x[j],x[k])
        for k in range(3))/2-sum(sp.diff(seed[i,j],x[k],2)
        for k in range(3))/2))
    sch=ric-sp.eye(3)*sp.trace(ric)/4
    cotton=sp.Matrix(3,3,lambda i,j:sp.expand(sum(
        sp.LeviCivita(i,k,l)*sp.diff(sch[l,j],x[k])
        for k,l in product(range(3),repeat=2))))
    assert cotton==cotton.T and sp.simplify(sp.trace(cotton))==0
    assert all(sp.simplify(sum(sp.diff(cotton[i,j],x[i])
        for i in range(3)))==0 for j in range(3))
    def D(p,i):
        return sp.expand(sp.diff(p,x[i])+2*x[i]*v*v*(sp.diff(p,v)-p))
    cache={(0,0,0):x[2]**3}
    for order in range(1,4):
        for aa in product(range(order+1),repeat=3):
            if sum(aa)!=order:continue
            i=next(i for i in range(3) if aa[i]);previous=list(aa);previous[i]-=1
            cache[aa]=D(cache[tuple(previous)],i)
    substitutions={}
    for derivative in cotton.atoms(sp.Derivative):
        aa=tuple(sum(n for sym,n in derivative.variable_count if sym==u) for u in x)
        substitutions[derivative]=cache[aa]
    p3=[sp.expand(z.xreplace(substitutions)) for z in cotton]
    p4=[D(z,i) for z in p3 for i in range(3)]
    p5=[D(z,i) for z in p4 for i in range(3)]
    # Cotton has only even angular polynomials up to degree 6:
    # spherical harmonics l=0,2,4,6 have total dimension 28.
    for p in p3:
        for powers,coef in sp.Poly(p,*x,v).terms():
            degree=sum(powers[:3]);assert degree<=6 and degree%2==0
    assert sum(2*l+1 for l in [0,2,4,6])==28
    def angular_norm(polys,den):
        full=sp.Poly(sp.expand(sum(p*p for p in polys)),*x,v)
        out=0
        for powers,coef in full.terms():
            xyz=powers[:3]
            if any(n%2 for n in xyz):continue
            angular=sp.prod(sp.factorial2(n-1) for n in xyz)/sp.factorial2(sum(xyz)+1)
            out+=coef*angular*s**(sum(xyz)//2)*v**powers[3]
        numerator=sp.Poly(sp.cancel(out.subs(v,1/(1-s))*(1-s)**den),s)
        assert sp.simplify(numerator.as_expr()/(1-s)**den-
                          out.subs(v,1/(1-s)))==0
        return [F(str(numerator.nth(k))) for k in range(numerator.degree()+1)]
    polys=[angular_norm(p3,12),angular_norm(p4,16),angular_norm(p5,20)]
    a,b,c,d,e=sp.symbols("a b c d e",real=True)
    tensor=sp.Matrix([[a,b,c],[b,d,e],[c,e,-a-d]])
    n=sp.Matrix([0,0,1])
    hh=[3*n[k]*tensor[i,j]+n[i]*tensor[k,j]+n[j]*tensor[i,k]
        -int(k==i)*(n.T*tensor[:,j])[0]-int(k==j)*(tensor[i,:]*n)[0]
        for k,i,j in product(range(3),repeat=3)]
    J=sp.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
    rot=J*tensor-tensor*J
    assert sp.expand(sum(z*z for z in hh)-15*sum(z*z for z in tensor)+
                     sum(z*z for z in rot))==0
    # Christoffel linear map has squared Euclidean Frobenius norm 7|u|^2.
    uu=sp.symbols("u0:3",real=True)
    Gamma=[int(k==i)*uu[j]+int(k==j)*uu[i]-int(i==j)*uu[k]
           for k,i,j in product(range(3),repeat=3)]
    assert sp.expand(sum(z*z for z in Gamma)-7*sum(z*z for z in uu))==0
    # The same identity applied to each derivative direction controls dGamma.
    scale,V,G,sigma=sp.symbols("scale V G sigma",positive=True)
    assert sp.simplify((scale**2*V)/(scale*G)**2-V/G**2)==0
    return polys,{
        "Cotton_same_seed_and_conformal_weight_as_parent":True,
        "angular_monomial_average":"prod((alpha_i-1)!!)/(sum(alpha_i)+1)!! for even powers; zero otherwise",
        "Cotton_angular_harmonic_degrees":[0,2,4,6],
        "angular_reproducing_kernel_dimension":28,
        "connection_identity":"sum|H_k(t)|^2=15*|x|^2*|t|^2-|[J_x,t]|^2",
        "connection_coefficient_15_independently_checked":True,
        "Christoffel_Frobenius_identity":"|Gamma(u)|_F^2=7*|u|^2",
        "second_spatial_derivative_index_convention":"sum over all ordered (a,b,i,j) of d_a d_b t_ij; both mixed orderings retained",
        "common_positive_test_rescaling_leaves_calibrated_variance_unchanged":True,
        "calibration_time_Green_term":"integral A^2*(psi_second+2*A_prime/A*psi_prime)=0",
        "calibration_gain":"G_tau=(integral A^2*psi)*(||D tau||_2^2+2||tau||_2^2)",
        "physical_profile":"h_theta=theta*tau/U on the readout support; smooth fixed continuation outside",
        "profile_sup_norm_equal_to_one_claimed":False,
    }

def bernstein_coefficients(poly):
    n=len(poly)-1
    return [sum(poly[j]*F(comb(k,j),comb(n,j)) for j in range(k+1))
            for k in range(n+1)]

def halve(coeffs):
    row=list(coeffs);left=[row[0]];right=[row[-1]]
    while len(row)>1:
        row=[(a+b)/2 for a,b in zip(row,row[1:])]
        left.append(row[0]);right.append(row[-1])
    return left,list(reversed(right))

def radial_certificates(polys):
    r0=iv.tan(I(F(1,16)))
    omega_min=lower(2/(1+r0*r0))
    n=2048;cut=F(63,64);tail_v=64
    sums=[I(0),I(0),I(0)]
    tails=[I(0),I(0),I(0)]
    sup2=F(0);cells=0
    pows=[3,5,7];dens=[12,16,20]
    def walk(left,right,coefficients,depth):
        nonlocal sup2,cells
        if left>=cut:
            assert left==cut and right==1
            for j,(p,d) in enumerate(zip(pows,dens)):
                cap=max(abs(x) for x in coefficients[j])
                # v^d exp(-2v) is decreasing for v>=64>=d/2.
                tails[j]=upper(I((1-cut)/2)*omega_min**(-p)*
                               I(cap)*I(tail_v)**d*iv.exp(-2*tail_v))
            cap=max(abs(x) for x in coefficients[0])
            sup2=max(sup2,hi(I(28)*omega_min**(-6)*I(cap)*
                             I(tail_v)**12*iv.exp(-2*tail_v)/M**2))
            return
        if depth==0:
            assert right<=cut
            cells+=1
            ss=box(left,right)
            vv=1/(1-ss)
            Om=2/(1+r0*r0*ss)
            exponential=iv.exp(-2*vv)
            for j,(p,d) in enumerate(zip(pows,dens)):
                cmin=max(F(0),min(coefficients[j]));cmax=max(coefficients[j])
                assert cmax>=0
                polynomial=box(cmin,cmax)
                common=exponential*vv**d*polynomial
                integrand=iv.sqrt(ss)*Om**(-p)*common/2
                sums[j]+=I(right-left)*integrand
                if j==0:
                    sup2=max(sup2,hi(I(28)*Om**(-6)*common/M**2))
            return
        pairs=[halve(c) for c in coefficients]
        mid=(left+right)/2
        walk(left,mid,[z[0] for z in pairs],depth-1)
        walk(mid,right,[z[1] for z in pairs],depth-1)
    walk(F(0),F(1),[bernstein_coefficients(p) for p in polys],11)
    assert cells==2016
    radial=[s+box(0,hi(t)) for s,t in zip(sums,tails)]
    B=4*iv.pi*r0**3*radial[0]/M**2
    A=4*iv.pi*r0*radial[1]/M**2
    C=4*iv.pi/r0*radial[2]/M**2
    assert lo(B)>0 and lo(A)>0 and lo(C)>0
    correction=upper(15*r0*r0*upper(B))
    assert lo(A)>hi(correction)
    energylo=lower((iv.sqrt(lower(A))-iv.sqrt(correction))**2+2*lower(B))
    energyhi=upper((iv.sqrt(upper(A))+iv.sqrt(correction))**2+2*upper(B))
    # Fix an explicit rational upper bound for the physical calibration profile.
    U=F(ceilf(hi(iv.sqrt(I(sup2)))*10**8),10**8)
    assert U*U>=sup2 and 0<U<1
    return r0,omega_min,B,A,C,box(lo(energylo),hi(energyhi)),U,{
        "radial_variable":"s=(r/r0)^2",
        "exact_angular_numerator_coefficients_ascending":[list(map(str,p)) for p in polys],
        "denominator_powers":[12,16,20],
        "Bernstein_dyadic_depth":11,"regular_cells":cells,
        "exponential_tail_starts_at_s":"63/64","tail_v_min":tail_v,
        "tail_method":"positive weight times Bernstein numerator cap and decreasing v^d*exp(-2v)",
        "radial_integrals":list(map(pair,radial)),
        "radial_tail_upper":list(map(pair,tails)),
        "tau_L2_squared":pair(B),
        "weighted_flat_first_derivative_squared":pair(A),
        "weighted_flat_second_derivative_squared":pair(C),
        "spatial_calibration_energy_interval":pair(box(lo(energylo),hi(energyhi))),
        "tau_sup_squared_upper":str(sup2),
        "fixed_rational_profile_U":str(U),
        "sup_norm_U_is_a_certificate_not_exact_maximum":True,
    }

def time_integral():
    total=I(0);N=1024
    for j in range(N):
        left=F(-1)+F(2*j,N);right=F(-1)+F(2*(j+1),N)
        maxabs=max(abs(left),abs(right))
        minabs=F(0) if left<=0<=right else min(abs(left),abs(right))
        blo=F(0) if maxabs==1 else lo(iv.exp(-1/(1-I(maxabs)**2)))
        bhi=hi(iv.exp(-1/(1-I(minabs)**2)))
        xx=box(left,right)
        total+=I(right-left)*3*iv.cos(I(F(3,16))+xx/16)*box(blo,bhi)/32
    assert lo(total)>0
    return total

def result_calculation():
    assert __debug__,"Do not disable scientific assertions"
    frozen=frozen_inputs()
    parent=json.loads((TL/"metric_response/tensor/result.json").read_text())
    oldnoise=json.loads((TL/"stress_kernel/noise/result.json").read_text())
    assert parent["compact_TT_test"]["normalizer_M_integer"]==M
    assert parent["scope"]["full_quantum_RSET_metric_response_included"] is False
    assert parent["all_mode_noise"]["old_new_TT_noise_difference"]==0
    polys,symbolic=symbolic_polynomials()
    r0,om,B,A,C,energy,U,radial=radial_certificates(polys)
    timeweight=time_integral()
    Gtau=timeweight*energy
    gain=Gtau/I(U)
    gainlo=lower(gain)
    assert lo(gainlo)>0
    # A short L2 bound replaces the previous very coarse pointwise E_Q bound.
    g=upper(2*iv.sqrt(7)*r0)
    dg=upper(iv.sqrt(7)*(2*iv.sqrt(3)+4*r0*r0))
    cov2=upper(iv.sqrt(upper(C))+
        (2*r0+5*g/om)*iv.sqrt(upper(A))+
        (iv.sqrt(3)/om+5*g*r0/om+(2*dg+6*g*g)/om**2)*iv.sqrt(upper(B)))
    lap=upper(iv.sqrt(3)*cov2)
    L=[upper(parse(x)) for x in oldnoise["spacetime_constants"]["time_derivative_L1_upper"]]
    volume=upper(parse(parent["readout"]["spatial_support_volume"]))
    EQ=upper(3*iv.sqrt(volume)*(
        (L[2]+2*iv.tan(I(F(1,4)))*L[1])*iv.sqrt(upper(B))+
        L[0]*(lap+2*iv.sqrt(upper(B)))))
    assert hi(EQ)<F(parent["readout"]["pointwise_strain_error_gain_upper"][1])
    CT=upper(parse(parent["all_mode_noise"]["C_T_upper"]))
    lam=32768
    variance=upper(I(U)**2*CT/lam**4)
    score_variance=upper(variance/gainlo**2)
    score_rms=upper(iv.sqrt(score_variance))
    assert hi(score_rms)<F(1,5000)
    point_error=F(1,1000000)
    other_score_bias=F(1,2000)
    score_bias=upper(EQ*I(point_error)/gainlo+I(other_score_bias))
    assert hi(score_bias)<F(1,1000)
    # Keep all 256 attempted records and all failure labels. At least 240
    # successes are used; otherwise a predetermined fallback is an error.
    N=256;minimum_success=240;failure_cap=F(1,100)
    q=F(17,256)
    KL=I(q)*iv.log(I(q/failure_cap))+(1-I(q))*iv.log(I((1-q)/(1-failure_cap)))
    failure_tail=upper(iv.exp(-N*KL))
    margin=F(1,250)
    noise_risk=upper(N*score_variance/(minimum_success**2*I(margin)**2))
    total_risk=upper(noise_risk+failure_tail)
    assert hi(total_risk)<F(1,100000)
    # Sufficient pointwise error budget if the other half of total bias
    # is assigned to reconstruction/transfer/calibration drift.
    point_budget=lower(I(F(1,2000))*gainlo/EQ)
    assert lo(point_budget)>point_error
    result={
        "schema":"ueot-calibrated-local-tensor-readout/1",
        "status":"CALIBRATED_TT_PROFILE_AND_COMPLETE_RECORD_GATE_CERTIFIED",
        "reviewed_base":BASE,"symbolic":symbolic,"radial_certificate":radial,
        "calibration":{
            "lambda":lam,"time_weight_integral_A2_psi":pair(timeweight),
            "profile":"h_theta=theta*tau/U during the original compact readout",
            "fixed_rational_U":str(U),"profile_Frobenius_sup_bound":"1",
            "profile_has_exact_unit_sup_norm":False,
            "theta_is_arbitrary_strain_reconstruction":False,
            "raw_tau_profile_gain_interval":pair(Gtau),
            "normalized_profile_gain_interval":pair(gain),
            "normalization_for_score":"divide observed O by the certified lower bound on G_tau/U",
            "normalized_gain_lower":pair(gainlo),
            "score_mean_theta0":"0","score_mean_theta1":"at least 1/100",
            "raw_readout_variance_upper":pair(variance),
            "raw_readout_RMS_upper":pair(upper(iv.sqrt(variance))),
            "calibrated_score_variance_upper":pair(score_variance),
            "calibrated_score_RMS_upper":pair(score_rms),
            "theta_1_over_100_signal_to_RMS_lower":pair(lower(I(F(1,100))/score_rms)),
            "normalized_bias_gain_upper":pair(upper(EQ/gainlo)),
            "improved_pointwise_strain_error_gain_upper":pair(EQ),
            "covariant_second_derivative_L2_upper":pair(cov2),
            "rough_Laplacian_L2_upper":pair(lap),
            "pointwise_reconstruction_error_budget":str(point_error),
            "other_normalized_bias_budget":str(other_score_bias),
            "total_normalized_bias_upper":pair(score_bias),
            "allowed_pointwise_error_if_other_bias_le_1_over_2000":pair(point_budget),
        },
        "complete_record_gate":{
            "hypotheses":"external specified profile coefficient theta=0 versus theta=1/100",
            "fixed_number_of_all_starts":N,"minimum_success_records":minimum_success,
            "retain_all_failure_labels":True,"heralded_failure_conditional_probability_cap":str(failure_cap),
            "successful_record_score":"O/gain_lower; additive bias uniformly at most 1/1000",
            "threshold":"1/200",
            "decision":"with at least 240 successes, mean successful score >=1/200 selects theta=1/100; otherwise theta=0; if fewer than 240 successes use fixed fallback theta=0",
            "low_success_event_counted_as_error_in_uniform_bound":True,
            "failure_count_error_event":"at least 17 failed starts",
            "failure_tail_KL_interval":pair(KL),
            "failure_tail_upper":pair(failure_tail),
            "noise_margin":"1/250",
            "martingale_noise_risk_upper":pair(noise_risk),
            "per_hypothesis_total_error_upper":pair(total_risk),
            "proof":"failure conditional-MGF Chernoff plus E[M_N^2]<=N*sigma^2 and K>=240",
            "independence_required_if_full_conditional_contract_is_given":False,
            "conditional_zero_mean_and_variance_bound_per_success_required":True,
            "stress_noise_Gaussian_assumed":False,
            "postselection_or_failure_cost_deleted":False,
            "arbitrary_optional_stopping_certified":False,
            "real_hardware_starts":0,
        },
        "scope":{
            "same_original_compact_TT_observable":True,
            "signal_profile_is_externally_specified":True,
            "distinguishes_old_new_homogeneous_source_preparations":False,
            "same_unperturbed_background_induced_covariance_model":True,
            "requires_a_record_law_realizing_declared_mean_covariance_and_failure_contract":True,
            "actual_quantum_geometry_measurement_instrument_constructed":False,
            "finite_theta_perturbed_state_noise_transferred":False,
            "nonlinear_metric_remainder_controlled":False,
            "full_quantum_RSET_feedback_included":False,
            "full_nonlinear_SCE_constructed":False,
            "actual_hardware_calibration_performed":False,
            "Core_unique_physical_selection":False,
        },
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for p,h in frozen.items():assert sha(p)==h,"Input changed during calibration"
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args();result=result_calculation()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Calibration receipt mismatch"
    c=result["calibration"];g=result["complete_record_gate"]
    print("Certified profile U:",c["fixed_rational_U"])
    for key in ["raw_tau_profile_gain_interval","normalized_profile_gain_interval","calibrated_score_RMS_upper","improved_pointwise_strain_error_gain_upper","total_normalized_bias_upper"]:
        print(key,[float(F(x)) for x in c[key]])
    print("256-start complete-record error upper:",float(F(g["per_hypothesis_total_error_upper"][1])))
    print("PASS: nonzero normalized TT calibration, all-mode score noise, complete failure-aware conditional gate.")
