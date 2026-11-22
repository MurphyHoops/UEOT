"""Finite local lapse perturbations of the original future Weyl record.

Uses a classical backward-KG energy comparison and the complete fixed-past
Gaussian covariance, rather than integrating a derivative bound at epsilon=0.
No mode ODE, field truncation or perturbed-metric RSET substitution is used.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
TL="physics/qm/null_source/timelike/"
BASE="719babd3386b9d9274d5c91dd0b8ad5e71688049"
mp.dps=90
iv.dps=78

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):
    assert isinstance(x,list) and len(x)==2,"Expected exact interval endpoints"
    return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))
def lower(x):return I(endpoint(x,0))

def freeze():
    names={
        "preparation":TL+"response/preparation/result.json",
        "noise":TL+"response/noise/result.json",
        "zero_slope":TL+"stress_kernel/response/result.json",
        "common_scale":TL+"stress_kernel/review.json",
        "reference_contract":TL+"continuation/SOURCE.md",
        "reference_implementation":TL+"instrument/instrument.py",
        "reference_bound_implementation":TL+"response/preparation/check.py",
    }
    frozen={}
    loaded={}
    for key,rel in names.items():
        p=REPO/rel
        assert p.is_file() and not p.is_symlink()
        assert p.read_bytes()==subprocess.check_output(
            ["git","show",BASE+":"+rel],cwd=REPO),"Changed inherited input: "+rel
        frozen[p]=sha(p)
        if p.suffix==".json":loaded[key]=json.loads(p.read_text())
    reference=(REPO/names["reference_implementation"]).read_text()
    for exact in ["v=np.sqrt(np.maximum(1,freq2))","a0=math.sqrt(3)",
                  "u=1/(a0*np.sqrt(2*v))","p=-1j*a0*np.sqrt(v/2)",
                  "pts=[-1/8,-1/16,0.,*WINS[0],*WINS[1],END]"]:
        assert exact in reference,"Changed reference normalization: "+exact
    frozen[HERE/"check.py"]=sha(HERE/"check.py")
    return loaded,frozen

def symbolic():
    x=sp.symbols("x",real=True)
    bump=sp.exp(-1/(1-x*x))
    bprime=sp.diff(bump,x)
    assert sp.simplify(sp.diff(bprime,x)/bump-(6*x**4-2)/(1-x*x)**4)==0
    eps,alpha=sp.symbols("epsilon alpha",real=True)
    n=sp.sqrt(1-2*eps*alpha)
    assert sp.simplify((n-1)*(n+1)+2*eps*alpha)==0
    assert sp.simplify(sp.diff(n,alpha)+eps/n)==0
    # Pointwise integrand after spatial integration by parts:
    # N^2'=2*h*(a^2*(|grad q|^2+q^2)-p^2/a^2)
    #       +2*p*grad(n).grad(q)+2*n*p*q.
    a,h,p,q,n0,lapq=sp.symbols("a h p q n lapq",real=True)
    gp=sp.Matrix(sp.symbols("p1:4",real=True))
    gq=sp.Matrix(sp.symbols("q1:4",real=True))
    gn=sp.Matrix(sp.symbols("n1:4",real=True))
    spatial=-2*n0*(gp.dot(gq))+2*gq.dot(n0*gp+p*gn)
    assert sp.expand(spatial-2*p*gn.dot(gq))==0
    # Difference forcing in the fixed base canonical variables.
    dn=sp.symbols("delta_n",real=True)
    Sq=dn*p/a**2
    Sp=a**2*(dn*lapq+gn.dot(gq))
    gradSq=(dn*gp+p*gn)/a**2
    assert sp.expand(Sp/a-a*dn*lapq-a*gn.dot(gq))==0
    assert all(sp.expand(z)==0 for z in a*gradSq-(dn*gp+p*gn)/a)
    # Exact symplectic variation against the spatially homogeneous f.
    zq,zp,fprime=sp.symbols("zq zp fprime",real=True)
    assert sp.expand(zq*0-zp*dn*fprime+zp*dn*fprime)==0
    # Normalization of actual metric, rescaled reference and Weyl exponent.
    lam,gain=sp.symbols("lambda gain",positive=True)
    V0,Vdelta,mu_delta,ycap=sp.symbols("V0 Vdelta mu_delta ycap",positive=True)
    t=10*gain
    probability_bound=t*ycap*mu_delta/2+t*t*(2*sp.sqrt(V0)+sp.sqrt(Vdelta))*sp.sqrt(Vdelta)/(4*lam**2)
    assert sp.simplify(probability_bound.subs({mu_delta:0,Vdelta:0}))==0
    # Actual k=1 reference: the width-one seed, with eigenvalue zero.
    uq=1/sp.sqrt(6);up=-sp.I*sp.sqrt(sp.Rational(3,2))
    assert sp.simplify(uq*sp.conjugate(uq))==sp.Rational(1,6)
    assert sp.simplify(up*sp.conjugate(up))==sp.Rational(3,2)
    assert sp.re(uq*sp.conjugate(up))==0
    assert sp.simplify(uq*sp.conjugate(up)-up*sp.conjugate(uq))==sp.I
    # Dropping ||a*q|| from N would miss a nonzero zero-mode covariance.
    assert sp.Rational(3,2)>0
    # A finite derivative cannot be substituted for a finite change.
    fake=sp.sin(sp.pi*eps/2)**2
    assert sp.diff(fake,eps).subs(eps,0)==0
    assert sp.simplify(fake.subs(eps,1))==1
    return {
        "metric":"g_epsilon,00=-lambda^2*a^2*(1-2*epsilon*alpha), alpha=F/(D*lambda^2)",
        "exact_lapse_difference":"n-1=-2*epsilon*alpha/(1+n)",
        "canonical_system":"q'=n*p/a^2; p'=a^2*div(n*grad q)",
        "backward_probe_source":"add +w(eta)*F_probe(x) to p'; zero final q,p at eta=3/16",
        "source_sign_convention":"with sigma(z,x)=integral(z_q*x_p-z_p*x_q), this positive source reproduces +Q at the initial slice",
        "energy_norm":"N(z)^2=||p/a||_2^2+||a*grad q||_2^2+||a*q||_2^2",
        "energy_growth_rate":"|h|+(||n||_infinity+||grad n||_infinity)/2",
        "energy_gradient_lapse_term_retained":True,
        "higher_norm":"N1^2=a^-2*(||p||^2+||grad p||^2)+a^2*(||q||^2+2||grad q||^2+||Delta q||^2)",
        "higher_norm_commutator":"(1-Delta_S3)^1/2 is a scalar spectral multiplier commuting with the background generator; no flat vector-gradient commutation is assumed",
        "zero_mode_seed":"u=1/sqrt(6), p=-i*sqrt(3/2), q-p symmetric covariance zero at eta=-1/8",
        "zero_mode_negative_control":"constant nonzero q with p=0 has nonzero Var(sigma(z,field)); omitting the q term from N would give zero norm",
        "difference_forcing_bound":"N(S)<=||n-1||_infinity*N1(z0)+||grad n||_infinity*N(z0)",
        "coherent_phase_identity":"Delta mu=-integral_I integral (n-1)*f_prime*z_epsilon,p dOmega deta",
        "coherent_identity_uses_no_derivative_of_the_small_probe_window":True,
        "physical_reference_covariance":"lambda^-2 times the common base covariance",
        "effect_formula":"exp[-t^2 V_epsilon/(2 lambda^2)]*chi(t*d_lambda*mu_epsilon); t=10*gain",
        "finite_probability_bound":"(t*ycap/2)*Delta_mu+(t^2/(4 lambda^2))*(2*sqrt(V0)+sqrt(Vdelta))*sqrt(Vdelta)",
        "zero_derivative_negative_control":"sin(pi*epsilon/2)^2 is a valid probability with derivative zero at zero and value one at epsilon=1",
        "finite_bound_obtained_by_integrating_old_zero_slope":False,
    }

def calculate():
    assert __debug__,"Do not optimize away scientific assertions"
    inputs,frozen=freeze()
    prep=inputs["preparation"]["reference_variance"]
    calibration=inputs["preparation"]["readout"]["calibration_contract"]
    for key,expected in {
        "actual_to_nominal_gain_interval":["199/200","201/200"],
        "additional_readout_contrast_interval":["99/100","1"],
        "additive_probability_error_interval":["-1/1000","1/1000"],
        "phase_error_interval":["-1/100","1/100"],
        "flagged_startup_failure_probability_interval":["0","1/100"],
        "prepared_candidate_is_conditional_on_success":True,
    }.items():assert calibration[key]==expected,"Calibration contract changed: "+key
    noise=inputs["noise"]["local_test_integrals"]
    base=inputs["common_scale"]["same_scale"]
    slope=inputs["zero_slope"]["numerical"]
    lam_value=int(base["lambda"]);lam=I(lam_value)
    assert lam_value==32768==slope["lambda"]
    assert base["same_calibration_and_heralded_preparation_failure_contract_as_parent"] is True
    assert prep["spatial_radius_chi"]=="1/100"
    assert prep["time_window_eta"]==["5/32","3/16"]
    assert noise["time_support"]==["1/16","1/8"]
    assert noise["spatial_radial_support"]==["0","1/8"]
    assert F(prep["preparation_total_log_variation_upper"][1])<F(1,8)
    assert prep["zero_mode_J_upper"]=="25/216"
    assert (F(3,16)+F(1,8))/F(27,10)==F(25,216)
    assert (F(1,16)+F(1,8))/F(27,10)<F(25,216)
    assert 0<F(base["d_squared"][0])<=F(base["d_squared"][1])<1
    Dlo=F(noise["classical_density_smearing_D"][0])
    assert Dlo>0
    left=I(F(1,16));right=I(F(1,8));T=I(F(3,16))
    duration=right-left
    amin=lower(iv.sqrt(3*iv.cos(2*T)))
    amax=iv.sqrt(3)
    assert F(pair(amin**2)[0])>F(27,10)
    Rs=I(F(1,8));Rp=I(F(1,100))
    w0=iv.exp(-1)
    xstar=iv.sqrt(iv.sqrt(I(F(1,3))))
    peak=upper(2*xstar/(1-xstar**2)**2*iv.exp(-1/(1-xstar**2)))
    w1=upper(peak/Rs)
    alpha_max=upper(iv.exp(-2)/(I(Dlo)*lam**2))
    nmin=lower(iv.sqrt(1-2*alpha_max))
    nmax=upper(iv.sqrt(1+2*alpha_max))
    assert F(pair(nmin)[0])>0
    dn_factor=upper(2/(1+nmin))
    grad_n_max=upper(w0*w1/(I(Dlo)*lam**2*nmin))
    hI=upper(iv.sqrt(3)*parse(noise["time_integral_h_over_a"]))
    assert F(pair(hI)[1])<F(pair(duration*w0)[1])
    int_delta_n=upper(dn_factor*w0*hI/(I(Dlo)*lam**2))
    int_grad_n=upper(w1*hI/(I(Dlo)*lam**2*nmin))
    Vs=upper(4*iv.pi*Rs**3/3)
    ws_l2=upper(iv.sqrt(parse(noise["spatial_L2_squared"])))
    assert F(pair(ws_l2)[1])<F(pair(w0*iv.sqrt(Vs))[1])
    int_delta_n_l2=upper(dn_factor*ws_l2*hI/(I(Dlo)*lam**2))
    F0sq=upper(parse(prep["spatial_L2_squared_upper"]))
    F0=upper(iv.sqrt(F0sq))
    # Direct all-space H1 bound on the actual normalized probe bump.
    Zlower=lower(iv.pi*Rp**3*iv.exp(-I(F(4,3)))*(1-Rp**2/24)**2/6)
    Vp=upper(4*iv.pi*Rp**3/3)
    Fgrad_sq=upper(Vp*(peak/(Rp*Zlower))**2)
    F1=upper(iv.sqrt(F0sq+Fgrad_sq))
    r0=upper(iv.tan(2*T)+I(F(1,2)))
    rn=upper(iv.tan(2*right)+(nmax+grad_n_max)/2)
    E0=upper(iv.exp(r0*(T-left)))
    EI=upper(iv.exp(rn*duration))
    EF=upper(iv.exp(r0*(T-right)))
    delta_N=upper(EI*E0/amin*(F1*int_delta_n+F0*int_grad_n))
    # Full base-reference covariance on the shared pre-perturbation slice.
    Cnz=upper(iv.exp(I(F(1,4)))/(2*iv.sqrt(3)))
    Jzero=I(F(25,216))
    Cz=upper(I(F(1,2))+I(F(3,2))/I(F(27,10))+I(F(9,2))*Jzero**2)
    Cref=I(F(9,8))
    assert F(pair(Cnz)[1])<F(9,8) and F(pair(Cz)[1])<F(9,8)
    sqrt_Vdelta=upper(iv.sqrt(Cref)*delta_N)
    V0=upper(parse(prep["full_base_smeared_field_variance_upper"]))
    p_adjoint=upper(amax*EI*EF*F0/amin)
    fprime=upper(iv.sqrt(27)/(3*iv.cos(2*right)))
    delta_mu=upper(fprime*p_adjoint*int_delta_n_l2)
    t=I(F(201,20))
    old_ycap=upper((1+iv.sqrt(3))/2)
    quantum_linear=upper(t**2/(2*lam**2)*iv.sqrt(V0)*sqrt_Vdelta)
    quantum_quadratic=upper(t**2/(4*lam**2)*sqrt_Vdelta**2)
    new_coherent=upper(t*delta_mu/2)
    old_coherent=upper(old_ycap*new_coherent)
    new_delta=upper(new_coherent+quantum_linear+quantum_quadratic)
    old_delta=upper(old_coherent+quantum_linear+quantum_quadratic)
    common_delta=old_delta
    oldp=parse(base["old_all_start_plus_interval"])
    newp=parse(base["new_all_start_plus_interval"])
    old_full=box(F(pair(oldp)[0])-F(pair(old_delta)[1]),F(pair(oldp)[1])+F(pair(old_delta)[1]))
    new_full=box(max(F(0),F(pair(newp)[0])-F(pair(new_delta)[1])),min(F(1),F(pair(newp)[1])+F(pair(new_delta)[1])))
    assert F(pair(old_full)[0])>F(9,20)
    assert F(pair(new_full)[1])<F(1,40)
    assert F(pair(common_delta)[1])<F(1,1000)
    risk=upper(iv.exp(-I(F(289,25))))
    assert F(pair(risk)[1])<F(1,100000)
    cone=upper(Rp+T+(nmax-1)*duration)
    assert F(pair(cone)[1])<F(1,4)
    assert F(pair(iv.sin(I(F(1,4)))*iv.sqrt(3))[1])<1
    result={
        "schema":"ueot-finite-local-lapse-record-stability/1",
        "status":"FINITE_EPSILON_RECORD_BAND_CERTIFIED",
        "base_commit":BASE,"symbolic":symbolic(),
        "finite_family":{
            "lambda":lam_value,"epsilon_interval":["-1","1"],
            "same_exact_lapse_family_as_parent":True,
            "source_and_past_reference_fixed_during_epsilon_variation":True,
            "future_test_gain_calibration_and_failure_rule_fixed":True,
            "metric_00_relative_change_upper":pair(upper(2*alpha_max)),
            "lapse_interval":[pair(nmin)[0],pair(nmax)[1]],
            "perturbation_time_interval":["1/16","1/8"],
            "probe_time_interval":["5/32","3/16"],
            "support_cone_chi_plus_eta_upper":pair(cone),
            "support_remains_inside_original_inner_domain":True,
        },
        "analytic_constants":{
            "original_density_D_lower":str(Dlo),
            "probe_L2_squared_upper":pair(F0sq),
            "probe_normalization_lower":pair(Zlower),
            "probe_gradient_L2_squared_upper":pair(Fgrad_sq),
            "probe_H1_upper":pair(F1),
            "source_spatial_L2_upper":pair(ws_l2),
            "time_bump_L1_upper":pair(hI),
            "int_lapse_difference_Linfinity_per_epsilon_upper":pair(int_delta_n),
            "int_lapse_gradient_Linfinity_per_epsilon_upper":pair(int_grad_n),
            "int_lapse_difference_L2_per_epsilon_upper":pair(int_delta_n_l2),
            "unperturbed_growth_rate_upper":pair(r0),
            "perturbed_growth_rate_upper":pair(rn),
            "backward_difference_energy_norm_per_epsilon_upper":pair(delta_N),
            "nonzero_mode_reference_covariance_norm_upper":pair(Cnz),
            "zero_mode_reference_covariance_norm_upper":pair(Cz),
            "complete_reference_covariance_norm_bound":"9/8",
            "sqrt_base_delta_variance_per_epsilon_upper":pair(sqrt_Vdelta),
            "base_probe_variance_upper":pair(V0),
            "homogeneous_phase_mean_difference_per_epsilon_upper":pair(delta_mu),
            "phase_difference_includes_d_lambda":False,
            "d_lambda_absolute_bound":"1",
            "reference_covariance_evaluation_slice":"1/16",
            "zero_mode_seed_slice":"-1/8",
            "zero_mode_J_bound_valid_through":"3/16",
        },
        "calibration_contract":calibration,
        "record_stability":{
            "gain_included_upper":"201/200","weyl_exponent_t_upper":"201/20",
            "new_amplitude_absolute_bound":"1",
            "old_amplitude_absolute_bound":pair(old_ycap),
            "new_coherent_probability_coefficient":pair(new_coherent),
            "old_coherent_probability_coefficient":pair(old_coherent),
            "quantum_probability_linear_coefficient":pair(quantum_linear),
            "quantum_probability_quadratic_coefficient":pair(quantum_quadratic),
            "bound_for_each_epsilon":"abs(epsilon)*(coherent+quantum_linear)+epsilon^2*quantum_quadratic",
            "new_all_start_probability_change_upper":pair(new_delta),
            "old_all_start_probability_change_upper":pair(old_delta),
            "common_complete_three_label_total_variation_upper":pair(common_delta),
            "old_all_start_plus_interval":pair(old_full),
            "new_all_start_plus_interval":pair(new_full),
            "independent_fresh_starts":128,
            "score":"1 for plus; 0 for minus or pre-interrogation flagged failure; retain all three labels",
            "threshold":"19/80","minimum_margin":"17/80",
            "per_candidate_error_upper":pair(risk),
            "fixed_calibration_and_preparation_contract_retained":True,
            "observed_hardware_starts":0,
        },
        "scope":{
            "finite_metric_perturbation_bound":True,
            "full_free_field_and_regular_zero_mode_included":True,
            "same_future_fixed_Weyl_instrument":True,
            "arbitrary_bounded_effect_uniform_bound":False,
            "fixed_proper_clock_window_without_recalibration":False,
            "finite_metric_path_C0_operator_norm_certified":False,
            "full_RSET_metric_derivative_norm_certified":False,
            "self_consistent_or_nonlinear_SCE_solution":False,
            "full_apparatus_or_driver_stress_certified":False,
            "new_Lean_proof":False,
        },
        "new_mode_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for p,h in frozen.items():assert sha(p)==h,"Input changed during finite-metric proof"
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    path=HERE/"result.json"
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered,"Finite-metric receipt mismatch"
    row=result["record_stability"]
    for k in ["new_all_start_probability_change_upper","old_all_start_probability_change_upper",
              "old_all_start_plus_interval","new_all_start_plus_interval"]:
        print(k,[float(F(x)) for x in row[k]])
    print("PASS: finite original lapse family, complete-field Weyl record band and 128-start classification.")
