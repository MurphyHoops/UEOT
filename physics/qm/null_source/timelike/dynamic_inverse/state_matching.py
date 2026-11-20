"""Fresh canonical covariance, AE logarithmic mismatch, and legal fast-mode identities."""
import sympy as sp
from common import *
def result():
    h,V,j,l,dj,dl,a=sp.symbols("h V j l dj dl a",real=True)
    q=-1-V;f=-j;q2=-l
    E3=(q*q-2*(h*h-1)*q+2*h*f)/8
    P3=-q*q/8-q2/12-(3*h*h+1)*q/12+h*f/4
    de=sp.expand(E3.subs(j,j+dj)-E3)
    dp=sp.expand(P3.subs({j:j+dj,l:l+dl})-P3)
    assert de==-h*dj/4 and dp==dl/12-h*dj/4
    log_rho=-de/(4*sp.pi**2*a**4);log_p=-dp/(4*sp.pi**2*a**4)
    assert sp.simplify(log_rho-h*dj/(16*sp.pi**2*a**4))==0
    assert sp.simplify(log_p-(h*dj/(16*sp.pi**2*a**4)-dl/(48*sp.pi**2*a**4)))==0
    # All-order triangular Riccati structure: explicit first eight coefficients.
    jets=sp.symbols("V0:10",real=True)
    def Dt(e):return sp.expand(sum(sp.diff(e,jets[i])*jets[i+1] for i in range(9)))
    ric=[None,-jets[0]]
    for n in range(1,8):
        ric.append(sp.expand(Dt(ric[n])+sum(ric[z]*ric[n-z] for z in range(1,n))))
    for n in range(1,9):
        assert sp.diff(ric[n],jets[n-1])==-1
        assert not any(ric[n].has(t) for t in jets[n:])
    eps=sp.symbols("eps",positive=True)
    X=eps/2+V*eps**3/4+(3*V**2-l)*eps**5/16
    Y=j*eps**3/8+(6*V*j-sp.symbols("V3"))*eps**5/32
    Z=sp.series((sp.Rational(1,4)+Y*Y)/X,eps,0,4).removeO()
    energy=Z-2*h*Y+(h*h+eps**-2)*X
    pressure=Z-2*h*Y+(h*h-eps**-2/3)*X
    t=sp.symbols("t",positive=True)
    convert={eps:t/sp.sqrt(1-t*t)}
    ek=sp.series(energy.subs(convert),t,0,4).removeO().expand()
    pk=sp.series(pressure.subs(convert),t,0,4).removeO().expand()
    assert sp.simplify(ek.coeff(t,3)-E3)==0
    assert sp.simplify(pk.coeff(t,3)-P3)==0
    # True incoming/Jost transport, not a frozen finite-time covariance.
    sigma,w,u,x=sp.symbols("sigma omega u x",positive=True)
    mode=sigma/(sigma-2*sp.I*w)
    modeprime=(sigma-sp.I*w)*mode
    dX=sp.simplify((mode+sp.conjugate(mode))*u/(2*w))
    dY=sp.simplify(sp.re(modeprime-sp.I*w*sp.conjugate(mode))*u/(2*w))
    dZ=sp.simplify(2*sp.re(sp.I*w*modeprime)*u/(2*w))
    assert sp.simplify(dX-sigma**2*u/(w*(sigma**2+4*w*w)))==0
    assert sp.simplify(dY-sigma**3*u/(2*w*(sigma**2+4*w*w)))==0
    assert sp.simplify(dZ+w*sigma**2*u/(sigma**2+4*w*w))==0
    assert sp.simplify(w*dX/2+dZ/(2*w))==0
    assert sp.simplify(sp.limit(w**3*dY,w,sp.oo)-sigma**3*u/8)==0
    rho0=sp.Rational(3,2)/x;drho=-3*u/x
    dconstraint=sp.simplify(-sp.Rational(2,3)*x*(2*rho0*u+drho))
    assert dconstraint==0
    dcurvature=6*(sigma*sigma-2)*u/x
    eta=sp.symbols("eta",real=True)
    J=sp.symbols("J",real=True,nonzero=True)
    h_example=J*eta**2/2
    V_example=sp.diff(h_example,eta)+h_example*h_example
    assert V_example.subs(eta,0)==0
    assert sp.diff(V_example,eta).subs(eta,0)==J
    assert sp.diff(V_example,eta,2).subs(eta,0)==0
    assert log_rho.subs(h,0)==0 and log_p.subs({h:0,dl:0})==0
    assert (dj/8).subs(dj,J)!=0
    # Flat switching gives identical infinite initial jets, which permits old Cauchy data.
    fast=json.loads((HERE/"fast_root.json").read_text())
    assert fast["fast_greater_than_twice_slow"]
    # Exact bidisc Jost construction: denominator, norm and Wronskian identities.
    lam,ww=sp.symbols("lambda omega",positive=True)
    denom=lam*(lam-2*sp.I*ww)
    assert sp.simplify(denom*sp.conjugate(denom)-lam**2*(lam**2+4*ww**2))==0
    Fp,Fm,Dp,Dm,VV=sp.symbols("Fplus Fminus Dplus Dminus potential")
    DDp=2*sp.I*ww*Dp+VV*Fp
    DDm=-2*sp.I*ww*Dm+VV*Fm
    assert sp.expand(Fm*DDp-Fp*DDm-2*sp.I*ww*(Dm*Fp+Fm*Dp))==0
    sf=box(fast["fast_conformal_growth_rate"])
    rz=iv.mpf(1)/100
    rw=1/(100*exact((sf*sf).b))
    theta_bound=SLOW*rz+sf*rw
    potential_bound=SLOW*SLOW*rz+sf*sf*rw+theta_bound**2
    contraction=potential_bound/(2*iv.sqrt(3)*SLOW)
    assert below(potential_bound,"0.051")
    assert below(contraction,"0.008")
    return {
      "canonical_identification":"phi=v/a, pi=a*(v'-h*v); fix a,h before identifying Cauchy covariances",
      "delta_E3":str(de),"delta_P3":str(dp),
      "single_field_frozen_rho_log_coefficient":str(log_rho),
      "single_field_frozen_p_log_coefficient":str(log_p),
      "two_field_frozen_rho_log_coefficient":str(2*log_rho),
      "two_field_frozen_p_log_coefficient":str(2*log_p),
      "h_zero_caveat":"The energy logarithm vanishes at h=0; this does not by itself certify or disprove a finite full RSET.",
      "frozen_state_abstract_CCR_positivity_disproved":False,
      "single_slice_both_stress_sums_finite_iff":"h*delta V'=0 and delta V''=0, at fixed a,h,V and old Hadamard covariance",
      "finite_stress_nonHadamard_counterexample":"a_new=A*exp(J*eta^3/6), a_old=A, old static Cauchy covariance at eta=0",
      "finite_one_slice_stress_is_full_Hadamard":False,
      "Riccati_first_eight":[str(e) for e in ric[1:]],
      "Riccati_highest_jet_coefficient":-1,
      "all_order_Hadamard_matching_theorem":"STATE_MATCHING.md; current smooth homogeneous S3 pure-high-mode / finite-thermal-shell class",
      "matching_all_jets_requires_analytic_geometry":False,
      "Hadamard_matching_equals_same_incoming_state":False,
      "leading_synchronized_cross_covariance":"delta Re(v* v')=delta V'/(8*omega^3)+O(omega^-5)",
      "leading_bare_minus_AE_log_cancellation_checked":True,
      "leading_correction_alone_is_full_Hadamard_proof":False,
      "actual_Jost_delta_X":str(dX),"actual_Jost_delta_Y":str(dY),"actual_Jost_delta_Z":str(dZ),
      "first_Wronskian_variation":0,
      "fixed_incoming_delta_rho":"-3*u/x",
      "linear_Hamiltonian_defect":0,
      "fast_mode_curvature_variation":str(dcurvature),
      "fast_mode_is_gauge":False,
      "same_slow_first_two_past_coefficients_fix_fast_amplitude":False,
      "nonlinear_solution_nonuniqueness_proved":False,
      "exact_bidisc_Jost_state_construction":True,
      "Jost_equation":"F_plus=1+K_plus(V*F_plus), multiplier K_plus=1/[lambda*(lambda-2i*omega)]; conjugate partner has +2i*omega",
      "Jost_construction_condition":"u_00=0, Theta^2*u in A; hence V_00=0 and finite norm(V)_A",
      "Jost_iteration_power_bound":"norm((K*M_V)^j)<= [norm(V)/(2*omega_k*s_*)]^j/j!",
      "Jost_small_norm_condition_required":False,
      "Jost_V_to_F_map_entire":True,
      "Jost_bound":"norm(F_k)_A <= exp(norm(V)_A/(2*omega_k*s_*))",
      "Jost_Wronskian_Theta_derivative_exact":0,
      "same_actual_zero_mode":"q=Q+(P/A^2)*(eta-eta_ref+Theta_inverse(exp(-2*u)-1)); same incoming Q,P and unchanged eta_ref",
      "bidisc_Hadamard_scope":"Real smooth geometry along every strictly interior bidisc history; full repeated UV expansion on compact time intervals, not a same-radius RSET bound",
      "example_off_shell_geometry":"u=z+w, Rz=1/100, Rw=1/(100*sigma_upper^2)",
      "example_bidisc_Rz":outward(rz),"example_bidisc_Rw":outward(rw),
      "example_potential_norm_bound":outward(potential_bound),
      "example_Jost_contraction_ratio_bound":outward(contraction),
      "example_Jost_norm_exponential_bound":outward(iv.exp(contraction)),
      "example_is_exact_SCE_solution":False,
      "full_renormalized_nonlinear_map_closed":False
    }
if __name__=="__main__":finish("state_matching.py",result(),["fast_root.py","fast_root.json"])
