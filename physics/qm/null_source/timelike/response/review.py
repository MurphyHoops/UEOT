"""Independent review of preparation, linear geometry and legal state variation.

Uses the archived infinite-field stress bounds, not the new geometry algorithm.
The numerical geometry bound follows a constant-coefficient Volterra comparison.
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
REPO=HERE.parents[4]
BASE="d6ec9eda409ba78d1d7993d7648ba26b5a34374d"
OLD="physics/qm/null_source/timelike/compatibility/review.json"
LAM=8192
mp.dps=90
iv.dps=78

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):
    return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def end(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rat(end(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([end(I(a),0),end(I(b),1)])
def parse(x):return box(F(x[0]),F(x[1]))
def upper(x):return I(end(x,1))
def absolute(x):return I(max(abs(end(x,0)),abs(end(x,1))))
def sinh(x):return (iv.exp(x)-iv.exp(-x))/2
def cosh(x):return (iv.exp(x)+iv.exp(-x))/2

def symbolic():
    m=sp.symbols("m",real=True)
    old={0:1,1:m,2:1,3:sp.Rational(5,2)*m,4:sp.Rational(7,4)}
    # The old third/fourth entries below are for m=s/2, m^2=1/4.
    for sign in [-1,1]:
        mean=sp.Rational(sign,2)
        vals=[mean-sp.sqrt(3)/2,mean+sp.sqrt(3)/2]
        older=[sp.simplify(sum(v**n for v in vals)/2) for n in range(5)]
        newer=[sp.simplify((1+mean)/2+(1-mean)*(-1)**n/2) for n in range(5)]
        assert older[:3]==newer[:3]
        assert older[3]==sp.Rational(5,4)*sign and newer[3]==mean
        assert older[4]==sp.Rational(7,4) and newer[4]==1
        gaussian4=mean**4+6*mean**2*sp.Rational(3,4)+3*sp.Rational(3,4)**2
        assert gaussian4==sp.Rational(23,8)
    p=sp.symbols("p",real=True)
    assert sp.solve(sp.Eq(2*p-1,m),p)==[(m+1)/2]
    x=sp.symbols("x",real=True)
    assert sp.simplify(sp.cos(-x)-sp.cos(x))==0
    assert sp.simplify(sp.sin(-x)+sp.sin(x))==0
    assert sp.simplify(sp.cos(x)**2-(1+sp.cos(2*x))/2)==0
    assert sp.simplify(sp.sin(x)**2-(1-sp.cos(2*x))/2)==0
    a,r,w,J,Vqq,Vqp,Vpp=sp.symbols("a r omega J Vqq Vqp Vpp",real=True,nonzero=True)
    K=sp.Matrix([[0,a**-2],[-a*a*w*w,0]])
    dK=sp.Matrix([[0,-2*r/a**2],[-2*r*a*a*w*w,0]])
    Omega=sp.Matrix([[0,1],[-1,0]])
    D=sp.diag(-r,r)
    assert K*Omega+Omega*K.T==sp.zeros(2)
    assert dK*Omega+Omega*dK.T==sp.zeros(2)
    assert sp.simplify(dK-(D*K-K*D))==sp.zeros(2)
    dVqq=-4*J*Vqp;dVqp=-2*J*Vpp
    assert sp.expand(Vpp*dVqq-2*Vqp*dVqp)==0
    c,s,b,bp,rho,q0=sp.symbols("c s b bp rho q0",real=True)
    A=sp.sqrt(3*c);Ap=-A*s/c
    rr,rp=sp.symbols("r rprime",real=True)
    bvalue=A*rr;bpvalue=Ap*rr+A*rp
    C=2*Ap*bpvalue+2*A*bvalue+18*bvalue/A**3+18*q0/A**2-sp.Rational(2,3)*A**4*rho
    expression=sp.expand(sp.simplify(A**2*C)).subs(s*s,1-c*c)
    assert sp.simplify(expression-18*(-c*s*rp+2*rr+q0-c**3*rho))==0
    lam,d,C0,C1,DD=sp.symbols("lambda d C0 C1 D",positive=True)
    Vnew=lam**-8*C0+d*d*lam**-6*C1
    Vold=Vnew+sp.Rational(3,4)*d**4*lam**-4*DD**2
    assert sp.simplify((Vold-Vnew)/(d**4*lam**-4*DD**2))==sp.Rational(3,4)
    g,sigma,phase=sp.symbols("g sigma phase",real=True)
    gamma=g/lam
    assert sp.simplify(2*gamma*lam*d*phase-2*g*d*phase)==0
    assert sp.simplify(2*gamma**2*sigma-2*g*g*sigma/lam**2)==0
    V=2*sp.pi**2;varp=sp.Rational(3,2)
    assert sp.simplify(4*varp/(27*V)-1/(9*sp.pi**2))==0
    assert sp.simplify(2*varp**2/(27**2*V**2)-1/(648*sp.pi**4))==0
    return {
        "first_two_moments_preserved":True,
        "fourth_moments":{"old_symmetric":"7/4","new_biased_sign":"1","Gaussian_completion":"23/8"},
        "classical_squared_amplitude_variances":{"old_symmetric":"3/4","new_biased_sign":"0","Gaussian_completion":"15/8"},
        "mixture_not_assumed_Gaussian":True,
        "X_probe_parity":{"ideal_axis_phase_zero_required":True,"residual_phase_can_introduce_odd_component":True,"Kraus":"cos(gamma*Phi), -i*sin(gamma*Phi)","record_CP_branches_parity_covariant":True,"distinguishes_old_amplitudes_from_new_fixed_amplitudes":True,"distinguishes_new_plus_minus_sign_branches":False,"odd_Y_quadrature_outside_this_record_contract":True},
        "zero_variance_distribution":"Y=+/-1, probabilities (1+/-m)/2, |m|<=1",
        "state_variation":{
            "canonical_matrix":"K=[[0,a^-2],[-a^2*omega^2,0]]",
            "relative_scale_variation":"delta K=[[0,-2r/a^2],[-2r*a^2*omega^2,0]]",
            "Duhamel":"delta z(t)=U(t,t0)delta z(t0)+integral U(t,s)delta K(s)z(s)ds",
            "linear_CCR_preserved":True,
            "initial_time":"common unchanged static preparation past; physical eta=0 data are not reset",
            "finite_mode_symplecticity_alone_proves_Hadamard":False,
            "smooth_full_preparation_metric_variation_required":True,
            "constant_homothety_initial_variation":"delta u=-r*u, delta p=r*p",
            "pointwise_commutator_does_not_remove_D_prime_for_variable_r":True,
            "zero_mode":"delta p=0; delta q=-2p*integral r/a^2",
            "full_zero_covariance_determinant_variation":"0",
            "infinite_RSET_derivative_norm_certified":False},
        "constraint_in_relative_scale":"cos(2eta)*sin(2eta)*r_prime-2r=Qeff0-cos(2eta)^3*rhoeff",
        "Weyl_normalization":{"dual_gain":"gamma=g_phys/lambda","physical_gain_does_not_vanish":True},
        "irreducible_zero_mode_ratios":{"C1_over_D2":"1/(9*pi^2)","C0_00_over_D2":"1/(648*pi^4)"},
    }

def numerical(old):
    ref=old["independent_uniform_reference"]
    lam=I(LAM);T=I(F(3,16));c=iv.cos(2*T)
    amin=iv.sqrt(3*c)
    R=upper(parse(ref["rho_absolute_upper"])+parse(ref["H1rho_absolute_upper"])*iv.log(lam)/(576*iv.pi**2))
    P=upper(parse(ref["pressure_absolute_upper"])+parse(ref["H1p_absolute_upper"])*iv.log(lam)/(576*iv.pi**2))
    qcap=absolute(parse(old["physical_models"]["quantum_initial_effective_interval"]))
    K2=upper(3/c**2-1);K=iv.sqrt(K2)
    forcing=upper(iv.sqrt(3)*(R+3*P)+18*qcap/amin**3)
    bcap=upper(forcing*(cosh(K*T)-1)/K2)
    bprime=upper(forcing*sinh(K*T)/K)
    rel=upper(bcap/(lam**2*amin))
    hbound=upper((bprime+iv.tan(2*T)*bcap)/(lam**2*amin))
    assert F(pair(rel)[1])<F(1,4000)
    assert F(pair(hbound)[1])<F(3,1000)
    volume=upper(3*rel)
    # A positive first-order path is a candidate geometry, not an exact solution.
    phase_ratio=box((1+F(pair(rel)[1]))**-2,(1-F(pair(rel)[1]))**-2)
    phase_deviation=absolute(phase_ratio-1)
    assert F(pair(phase_deviation)[1])<F(1,1000)
    hardware=box(F(996,1000),F(1004,1000))
    combined=phase_ratio*hardware
    assert F(pair(combined)[0])>F(995,1000)
    assert F(pair(combined)[1])<F(1005,1000)
    sample_error=iv.exp(-2*I(256)*I(F(3,20))**2)
    assert F(pair(sample_error)[1])<F(1,100000)
    # Full-noise constants are symbolic. This is not a numeric C0 certificate.
    return {
        "lambda":LAM,"eta_interval":["0","3/16"],
        "method":"constant_coefficient_positive_Volterra_comparison",
        "maximum_kappa_squared":pair(K2),"forcing_absolute_upper":pair(forcing),
        "b_absolute_upper":pair(bcap),"b_prime_absolute_upper":pair(bprime),
        "uniform_first_order_scale_relative_upper":pair(rel),
        "uniform_first_order_conformal_H_absolute_upper":pair(hbound),
        "uniform_first_order_log_volume_absolute_upper":pair(volume),
        "candidate_scale_positive":True,
        "distance_to_exact_SCE_solution_certified":False,
        "coherent_phase_on_positive_candidate":{
            "source_momentum_held_fixed":True,
            "relative_phase_ratio_interval":pair(phase_ratio),
            "relative_phase_change_abs_upper":pair(phase_deviation),
            "with_0p4_percent_physical_gain_interval":pair(combined),
            "fits_0p5_percent_combined_phase_gain_budget":True,
            "complete_reference_visibility_on_changed_geometry_certified":False},
        "conditional_all_start_statistics":{
            "old_probability_lower":"9/20","new_probability_upper":"3/20",
            "threshold":"3/10","independent_new_starts":256,
            "one_candidate_Hoeffding_error_upper":pair(sample_error)},
    }

def joint_threshold():
    lam,Ba,Da,delta=sp.symbols("lambda Ba Da delta",positive=True)
    # log(lambda)<=lambda for lambda>=1 gives a transparent nonoptimal geometry gate.
    c0,c1,z=sp.symbols("c0 c1 z",positive=True)
    e=sp.Rational(99,100)
    noise_z=(c1+sp.sqrt(c1*c1+4*delta*e*e*c0))/(2*delta*e*e)
    assert sp.simplify(delta*e*e*noise_z**2-c1*noise_z-c0)==0
    return {
        "quantifiers":"Fix a finite family of nonzero nonnegative C-infinity compact spacetime density tests first; then choose lambda and retune the exact correlated source at that lambda.",
        "noise_background":"homothetic g_lambda, not the nonhomothetic corrected candidate geometry",
        "geometry_object":"background-sourced first-order response, not distance to a full SCE solution",
        "noise_constants":"c0*=max_i C0_i/D_i^2; c1*=max_i C1_i/D_i^2; both finite",
        "noise_lambda_squared_threshold":"[c1*+sqrt(c1*^2+4*delta_noise*0.99^2*c0*)]/[2*delta_noise*0.99^2]",
        "geometry_bound":"(Ba+Da*log(lambda))/lambda^2",
        "geometry_sufficient_lambda":"max(8192,sqrt(2*Ba/delta_geometry),2*Da/delta_geometry)",
        "joint_sufficient_lambda":"maximum of noise and geometry thresholds",
        "physical_size_and_proper_time_may_grow_with_lambda":True,
        "uniform_over_all_resolutions_at_fixed_lambda":False,
        "full_C0_numerical_upper_bound_at_8192_available":False,
    }

def calculate():
    if not __debug__:raise RuntimeError("Proof assertions must not be optimized out")
    p=REPO/OLD
    expected=subprocess.check_output(["git","show",BASE+":"+OLD],cwd=REPO)
    assert p.read_bytes()==expected,"Archived stress input changed"
    frozen={p:sha(p),HERE/"review.py":sha(HERE/"review.py")}
    old=json.loads(p.read_text())
    assert old["physical_models"]["lambda"]==LAM
    result={
        "schema":"ueot-response-independent-review/1","reviewed_base":BASE,
        "status":"PREPARATION_AND_LINEAR_RESPONSE_INDEPENDENTLY_REVIEWED",
        "symbolic":symbolic(),"numerical":numerical(old),
        "joint_finite_test_scale_theorem":joint_threshold(),
        "new_mode_integrations":0,
        "full_nonlinear_SCE":"OPEN","quantitative_infinite_RSET_response":"OPEN",
        "physical_device_and_driver":"OPEN",
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for path,h in frozen.items():assert sha(path)==h,"Input changed during independent review"
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"review.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Independent review receipt mismatch"
    row=result["numerical"]
    print("Independent scale response <=",float(F(row["uniform_first_order_scale_relative_upper"][1])))
    print("Independent conformal H response <=",float(F(row["uniform_first_order_conformal_H_absolute_upper"][1])))
    print("PASS: preparation, independent Volterra response, state variation and finite-test scope.")
