"""Full all-mode quadratic stress noise for the existing local spacetime test.

The state is the archived static-prepared pure quasifree reference.  Low and
mixed blocks use spectral Bessel bounds; the high positive-frequency block
uses three integrations by parts; the actual preparation remainder uses the
archived W2 Bogoliubov certificate.  No mode ODE is integrated.
"""
from fractions import Fraction as F
from pathlib import Path
from math import factorial
import argparse
import hashlib
import json
import subprocess
import sys
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
TIMELIKE=HERE.parents[1]
BASE="29d49e3eee6299e2085492b0e061288b8166b5fa"
K=256
mp.dps=90
iv.dps=70
sys.path.insert(0,str(TIMELIKE/"evolution/propagation"))
sys.path.insert(0,str(TIMELIKE/"evolution/stress"))
import background as bg
import tail as old_tail
iv.dps=70
mp.dps=90
Jet=bg.Jet

def I(x):
    if hasattr(x,"_mpi_"):return x
    if isinstance(x,mp.mpf):return iv.mpf(x)
    x=F(x)
    return iv.mpf(x.numerator)/x.denominator
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,man,power,_=x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**power
def pair(x):return [str(rational(endpoint(x,j))) for j in [0,1]]
def hi(x):return F(pair(x)[1])
def lo(x):return F(pair(x)[0])
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))
def absolute(x):return I(max(abs(endpoint(x,0)),abs(endpoint(x,1))))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def trunc(j,n):return Jet(j.c[:n+1])
def deriv(j):return Jet([(i+1)*j.c[i+1] for i in range(j.n)])
def power(j,n):return old_tail.power(j,n)

def frozen_inputs():
    paths=[
        "response/noise/check.py","response/noise/result.json",
        "evolution/propagation/background.py","evolution/stress/tail.py",
        "evolution/stress/tail_K256_M1024.json","continuation/SOURCE.md",
        "compatibility/review.py","compatibility/review.json",
        "response/CONTRACT.md",
    ]
    frozen={}
    for rel in paths:
        p=TIMELIKE/rel
        archive=subprocess.check_output(["git","show",BASE+":"+str(p.relative_to(REPO))],cwd=REPO)
        assert archive==p.read_bytes(),("archived input changed",rel)
        frozen[p]=sha(p)
    frozen[HERE/"check.py"]=sha(HERE/"check.py")
    return frozen

def algebra():
    z=sp.symbols("z",real=True)
    x=sp.symbols("x",real=True)
    p2=4*z**4-12*z**3+6*z*z
    p3=-2*z**3+14*z*z-21*z+6
    # b''=p2(z)e^-z; b^(3)=4*x*z^3*p3(z)e^-z, z=(1-x^2)^-1.
    b=sp.exp(-1/(1-x*x))
    assert sp.simplify(sp.diff(b,x,2)-p2.subs(z,1/(1-x*x))*b)==0
    assert sp.simplify(sp.diff(b,x,3)-4*x/(1-x*x)**3*p3.subs(z,1/(1-x*x))*b)==0
    assert sp.Poly(p3,z).count_roots(1,sp.oo)==2
    assert p3.subs(z,sp.Rational(159,100))<0<p3.subs(z,sp.Rational(8,5))
    assert p3.subs(z,5)>0>p3.subs(z,sp.Rational(51,10))
    # Pair-creation normalization: C0=2||P||^2=||B||^2/2, B=2P.
    pp=sp.symbols("P",real=True)
    assert sp.expand((2*pp)**2/2-2*pp**2)==0
    # Bessel/Cauchy use every real harmonic label, followed by degeneracy k^2.
    k=sp.symbols("k",positive=True)
    assert sp.simplify(k*k*k*k*k**-10-k**-6)==0
    assert sp.simplify(k*k*k*k**-10-k**-7)==0
    return {
        "pair_creation":"C0=2*sum_nm |P_nm|^2=(1/2)*||B||_HS^2; B=2P",
        "P_nm":"(1/2)*integral h*a^2*(u_n_prime*u_m_prime*M_nm+u_n*u_m*N_nm) d_eta",
        "real_spatial_harmonics":True,
        "zero_mode_in_low_block":True,
        "low_high_block_multiplicity":2,
        "spatial_M_row":"sum_l |M_kl|^2 <= ||w||_infinity^2",
        "spatial_M_weighted_row":"sum_l omega_l*|M_kl|^2 <= w0*(w1+w0*omega_k)",
        "spatial_N_weighted_row":"sum_l |N_kl|^2/omega_l <= sqrt(2)*(w0^2*omega_k^3+w0*w1*omega_k^2)",
        "N_zero_column":"0; never divide by zero-mode frequency",
        "bump_third_derivative_extrema_polynomial":"-2*z^3+14*z^2-21*z+6",
        "bump_extrema_two_roots_above_one":True,
        "literal_absolute_square_of_singular_Wightman_kernel_used":False,
        "mixture_Gaussianized":False,
    }

def spatial_and_time_constants(old):
    integrals=old["local_test_integrals"]
    d=parse(integrals["classical_density_smearing_D"])
    h0=upper(iv.sqrt(3)*parse(integrals["time_integral_h_over_a"]))
    w0=iv.exp(-1)
    zstar=(3+iv.sqrt(3))/2
    xstar=iv.sqrt(iv.sqrt(I(F(1,3))))
    max_b1=2*xstar*zstar*zstar*iv.exp(-zstar)
    w1=8*max_b1
    def b2(z):return (4*z**4-12*z**3+6*z*z)*iv.exp(-z)
    # At x>=0, b'' has just these two extrema; the endpoint values are
    # b''(0)=-2/e and b''(1)=0. Dropping the negative 2*b''(0) is safe.
    min_box=b2(box(F(159,100),F(8,5)))
    max_box=b2(box(5,F(51,10)))
    l0=h0
    l1=2*w0
    l2=32*4*max_b1
    l3=32**2*4*(absolute(min_box)+absolute(max_box))
    return d,w0,w1,[upper(v) for v in [l0,l1,l2,l3]],{
        "D_interval":pair(d),"spatial_w_infinity":pair(w0),
        "spatial_gradient_w_infinity":pair(w1),
        "bump_second_derivative_at_negative_extremum_enclosure":pair(min_box),
        "bump_second_derivative_at_positive_extremum_enclosure":pair(max_box),
        "time_derivative_L1_upper":[pair(v) for v in [l0,l1,l2,l3]],
        "test_unchanged":"b(32*(eta-3/32))*b(8*chi)",
        "eta_support":["1/16","1/8"],"radial_support":"chi<1/8",
    }

def positive_phase_constants(time_l1):
    # Every k>K is enclosed simultaneously; these are actual time jets.
    qv=bg.q_box(F(1,16),F(1,8),7)
    q=[Jet([qv[j+n]/factorial(n) for n in range(4)]) for j in range(5)]
    delta=Jet.const(box(0,F(1,(K+1)**2)),3)
    _,B,_,T1,Rn=old_tail.normalized_defect(q,delta)
    Wscaled=B.sqrt()
    sigma=Wscaled+power(delta,3)*Rn/(2*Wscaled)
    t=Jet([box(F(1,16),F(1,8)),1,0,0])
    sn,cs=(2*t).sincos()
    hh=-sn/cs
    Bprime=delta*q[1]+power(delta,2)*T1
    g=hh+Bprime/(4*B)
    assert lo(B.c[0])>F(1,2) and hi(B.c[0])<2
    assert hi(absolute(g.c[0]))<1
    assert lo(sigma.c[0])>F(1,2)
    # |a*u_W2|<=k^-1/2 and |a*u'_W2|<=2*k^1/2.
    cp=(iv.sqrt(upper(B.c[0]))+absolute(g.c[0])/(K+1))/(iv.sqrt(2)*I(lo(B.c[0]))**I(F(1,4)))
    cu=1/(iv.sqrt(2)*I(lo(B.c[0]))**I(F(1,4)))
    assert hi(cp)<2 and hi(cu)<1
    fourth=B.sqrt().sqrt()
    rec=fourth.inverse()
    eps=Jet.const(box(0,F(1,K+1)),3)
    real=eps*g*rec
    imag=fourth
    # The two copies enclose independent k and l. S=(k*sigma_k+l*sigma_l)/(k+l)
    # has each time-jet coefficient inside the same common sigma enclosure.
    akin_re=real*real-imag*imag
    akin_im=2*real*imag
    agrad=rec*rec
    def coeffs(amplitude):
        rows=[]
        for j in range(4):
            h=Jet([I(F(1,factorial(j))) if n==j else I(0) for n in range(4)])
            f=h*amplitude
            for n in range(3):
                f=deriv(f/trunc(sigma,f.n))
            rows.append(f.c[0])
        return rows
    re,im,gr=coeffs(akin_re),coeffs(akin_im),coeffs(agrad)
    kc=[iv.sqrt(absolute(a)**2+absolute(b)**2) for a,b in zip(re,im)]
    gc=[absolute(x) for x in gr]
    lk=upper(sum((a*b for a,b in zip(kc,time_l1)),I(0)))
    lg=upper(sum((a*b for a,b in zip(gc,time_l1)),I(0)))
    return lk,lg,{
        "IBP_order":3,
        "phase":"phi_k_prime=W_k+R_k/(2*W_k)=k*sigma_k",
        "W2_B_interval":pair(B.c[0]),"sigma_interval":pair(sigma.c[0]),
        "g_absolute_upper":pair(absolute(g.c[0])),
        "kinetic_WKB_mode_factor_upper":pair(cp),
        "field_WKB_mode_factor_upper":pair(cu),
        "kinetic_h_derivative_coefficients_abs_upper":[pair(x) for x in kc],
        "gradient_h_derivative_coefficients_abs_upper":[pair(x) for x in gc],
        "kinetic_IBP_L1_upper":pair(lk),"gradient_IBP_L1_upper":pair(lg),
        "boundary_terms":"all vanish because the original bump is C-infinity flat",
        "two_frequencies_not_replaced_by_frequency_difference":True,
    }

def calculate():
    assert __debug__,"Do not optimize away proof assertions"
    frozen=frozen_inputs()
    old=json.loads((TIMELIKE/"response/noise/result.json").read_text())
    uv=json.loads((TIMELIKE/"evolution/stress/tail_K256_M1024.json").read_text())
    assert uv["K"]==K
    uniform=uv["uniform_physical_UV_tail"]
    assert uniform["eta_interval"]==["0","3/16"]
    symbols=algebra()
    D,w0,w1,Lh,constants=spatial_and_time_constants(old)
    lk,lg,phase=positive_phase_constants(Lh)
    H=upper(parse(old["all_mode_preparation_growth"]["mode_derivative_bound_factor"]))
    amin2=3*iv.cos(I(F(1,4)))
    assert hi(I(F(3,2))/amin2)<lo(H),"zero mode must fit the common low-block kinetic bound"
    S3=I(F(K*K*(K+1)*(K+1),4))
    S4=I(F(K*(K+1)*(2*K+1)*(3*K*K+3*K-1),30))
    sx=w0*w0*S4+w0*w1*S3
    quarter2=iv.sqrt(iv.sqrt(2))
    nll=upper(H*Lh[0]*(w0*iv.sqrt(K*S3)+quarter2*iv.sqrt(sx)))
    nlh=upper(H*Lh[0]*(1+quarter2)*iv.sqrt(sx))
    nmain=upper((lk*w0/iv.sqrt(K)+lg*quarter2*iv.sqrt(w0*w0/K+w0*w1/(2*K*K)))/2)
    D5=upper(parse(uniform["integration_D5"]))
    imax=upper(D5/(K+1)**5)
    E5=upper(iv.exp(imax)*D5)
    eta_max=upper(E5/(K+1)**5)
    assert hi(eta_max)<1
    # The factor 32 dominates 16*sqrt(2)+4*2^(1/4).
    assert hi(16*iv.sqrt(2)+4*quarter2)<32
    nerror=upper(32*Lh[0]*E5*iv.sqrt(w0*w0/(5*K**5)+w0*w1/(6*K**6)))
    nhh=upper(nmain+nerror)
    C0=upper((nll*nll+2*nlh*nlh+nhh*nhh)/2)
    c0=hi(C0)/lo(D)**2
    c1=F(old["certificate"]["local_test_all_mode_linear_coefficient_c1_upper"])
    eps=F(1,100)
    target=F(1,100)
    lam=8192
    def relative(L):return (c0/F(L**4)+c1/F(L*L))/(1-eps)**2
    while relative(lam)>=target:lam*=2
    assert lam<=2**30,"A finite-scale exit was not obtained within the declared cap"
    assert relative(lam)<target
    c0_budget=target*(1-eps)**2*8192**4-c1*8192**2
    result={
        "schema":"ueot-full-quadratic-stress-noise/1","base_commit":BASE,
        "status":"COMPLETE_QUADRATIC_NOISE_UPPER_AND_EXPLICIT_WEAK_NOISE_SCALE",
        "symbolic_checks":symbols,"spacetime_constants":constants,
        "positive_frequency_high_block":phase,
        "block_bounds":{
            "K":K,"all_mode_kinetic_factor_upper":pair(H),
            "zero_mode_kinetic_factor_upper":pair(I(F(3,2))/amin2),
            "low_low_Hilbert_Schmidt_upper":pair(nll),
            "one_low_high_Hilbert_Schmidt_upper":pair(nlh),
            "high_positive_main_Hilbert_Schmidt_upper":pair(nmain),
            "old_preparation_D5":pair(D5),
            "maximum_high_mode_rapidity":pair(imax),
            "preparation_remainder_E5":pair(E5),
            "preparation_remainder_eta_max":pair(eta_max),
            "high_remainder_Hilbert_Schmidt_upper":pair(nerror),
            "high_high_total_Hilbert_Schmidt_upper":pair(nhh),
            "C0_absolute_upper":pair(C0),
            "formula":"C0 <= (N_LL^2+2*N_LH^2+(N_HH_positive+N_HH_remainder)^2)/2",
            "uniform_remainder":"|alpha_tilde-1|+|beta_tilde| <= E5/k^5, k>K",
            "old_mean_stress_tail_used_as_noise_tail":False,
            "old_W2_Bogoliubov_preparation_bound_reused":True,
        },
        "certificate":{
            "c0_over_D2_upper":str(c0),"c0_over_D2_upper_decimal":float(c0),
            "c1_over_D2_upper":str(c1),
            "lambda_certified":lam,
            "full_relative_variance_upper":str(relative(lam)),
            "full_relative_variance_upper_decimal":float(relative(lam)),
            "relative_variance_target":str(target),
            "mean_relative_defect_bound_used":str(eps),
            "source_family":"exact correlated source retuned at every lambda",
            "test":"original local F=b(32*(eta-3/32))*b(8*chi)",
            "lambda8192_upper":str(relative(8192)),
            "lambda8192_upper_decimal":float(relative(8192)),
            "lambda8192_one_percent_certified":relative(8192)<target,
            "lambda8192_one_percent_failure_proved":False,
            "lambda8192_c0_sufficient_budget":str(c0_budget),
            "scale_optimality_proved":False,
            "full_nonlinear_SCE_solution":False,
            "new_matching_hardware_data":False,
        },
        "new_mode_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for p,h in frozen.items():assert sha(p)==h,("input changed",str(p))
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    p=HERE/"result.json"
    if args.write:p.write_text(rendered)
    if args.check:assert p.read_text()==rendered,"Full quadratic-noise receipt mismatch"
    c=result["certificate"]
    print("C0/D^2 full-spectrum upper:",c["c0_over_D2_upper_decimal"])
    print("Explicit lambda:",c["lambda_certified"])
    print("Full relative variance upper:",c["full_relative_variance_upper_decimal"])
    print("At 8192 conservative upper:",c["lambda8192_upper_decimal"])
    print("PASS: complete original-test quadratic noise and explicit weak-noise scale; zero new mode ODE.")
