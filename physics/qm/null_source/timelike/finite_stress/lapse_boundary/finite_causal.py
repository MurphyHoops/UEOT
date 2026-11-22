"""Finite-cutoff principal coefficient and complete counterterm Ward identities."""
import sympy as s
from common import iv,load,box,above,below,outward,require,finish
h,V,V1,V2,V3,ell,Hk,a,V0=s.symbols("h V V1 V2 V3 ell Hk a V0",real=True)
a3=V1+h*V;a4=V2+2*h*V1+V*V
H1=-36*a3*h+72*V*h*h+18*V*V+36*h*h-18
T1=-36*a4+144*a3*h-216*V*h*h+108*V*V+72*V-72*h*h
H3=3*h**4+6*h*h+3;T3=12*V*h*h-12*h**4+12*V-12*h*h
ran=(-H1/6+H3)/2880-H1/1728+(H1*(2+ell)/32-s.Rational(9,4)*(h*h*V+h*h))/36
tan=(-T1/6+T3)/2880-T1/1728+(T1*(2+ell)/32-s.Rational(9,8)*(4*a3*h-10*V*h*h+3*V*V+4*V-6*h*h+1))/36
pan=(ran-tan)/3
gamma=(19+15*ell-30*Hk)/(360*V0*a*a)
pressure_coefficient=(-Hk/12+4*s.diff(pan,V2))/(V0*a*a)
density_coefficient=-s.Rational(2,3)*(h*Hk/4+4*s.diff(ran,V1))/(V0*a*a)
require(s.simplify(pressure_coefficient-gamma)==0,"Pressure highest coefficient")
require(s.simplify(density_coefficient-2*h*gamma)==0,"Density highest coefficient")
def D(expr):
    return s.diff(expr,h)*(V-h*h)+s.diff(expr,V)*V1+s.diff(expr,V1)*V2+s.diff(expr,V2)*V3+s.diff(expr,ell)*2*h
Ae=h*h/2;Ap=Ae-V/3
Ce=V*V/8+h*h*V/4-h*V1/4
Cp=-V*V/8+h*h*V/4-h*V1/4+V2/12
require(s.simplify(D(Ae)-h*Ae+3*h*Ap)==0,"Order1 subtraction Ward")
require(s.simplify(D(Ce)-h*Ce+3*h*Cp)==0,"Order3 subtraction Ward")
require(s.simplify(D(ran)-h*tan)==0,"Full fixed local AE Ward")
inputs=["joint_history/history.json","nonlinear_history/KERNELS.md",
        "finite_stress/lapse_boundary/RETARDED_RESPONSE.md",
        "finite_stress/lapse_boundary/CAUSAL_DOMAINS.md"]
A=box(load(inputs[0])["cases"]["unfiltered"]["A"])
rho=iv.mpf("1e-25");ell_actual=iv.ln(A*A/4)+2*iv.euler+2*iv.mpf([-1,1])*rho
require(below(ell_actual,23),"Actual local log")
require(above(iv.ln(1000001),"13.8"),"Harmonic lower bound")
gamma_abs_lower=(iv.mpf("13.8")-iv.mpf(364)/30)/(12*(2*iv.pi**2)*A*A*iv.exp(2*rho))
require(above(gamma_abs_lower),"Nondegenerate finite-cutoff pressure IVP")
finish("finite_causal.py",dict(
 reference_k1_subtractor_retained=True,
 pressure_local_highest_coefficient="(19+15*ell-30*H_K)/(360*V0*a^2)",
 density_local_highest_coefficient="2*h*gamma4K",
 full_fixed_local_and_subtraction_Ward_exact=True,
 sufficient_cutoff_for_nonzero_principal_coefficient=1000000,
 absolute_principal_coefficient_strict_lower=outward(gamma_abs_lower),
 finite_K_prepared_causal_inverse="Peano-Baker fundamental matrix, initial transport retained",
 finite_K_numerical_mode_or_Green_solution_computed=False,
 actual_background_is_exactly_finite_K_on_shell=False,
 off_shell_linearized_Ward_defect="w_prime*(2*S_K-E_K)",
 all_field_inverse_convergence_proved=False,
 K_uniform_inverse_bound_proved=False,
 C8_to_C0_operator_tail_implies_inverse_convergence=False,
 actual_noise_is_flat_start_smooth_forcing=False),
 inputs,proof="FINITE_CAUSAL.md")
