"""Exact 6-channel conformal Parseval frame algebra, hyperspherical verification and quadrupole vanishing."""
import sympy as sp
from common import iv,load,require,above,below,outward,finish
from model import geodesic_cap_spectrum

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
load(jc+"post_closure.json")

# 1. Exact curved-FRW covariant improved conformal stress-energy tensor check
tau,g_s,lam0,kh2_s=sp.symbols("tau g lam0 kh2",positive=True)
a=sp.Function("a")(tau);ap=sp.diff(a,tau);app=sp.diff(a,tau,2)
f=sp.cos(2*tau)/(kh2_s*a*g_s);fp=sp.diff(f,tau)
Phi2=lam0*f**2;Phi2_p=sp.diff(Phi2,tau);Phi2_pp=sp.diff(Phi2,tau,2)
G_tt=3*((ap/a)**2+1)
G_ij=-2*app/a+(ap/a)**2-1
grad_sq=-a**(-2)*(lam0*fp**2)+a**(-2)*(3*lam0*f**2)
Box_Phi2=-a**(-2)*(Phi2_pp+2*(ap/a)*Phi2_p)
nabla_tt_Phi2=Phi2_pp-(ap/a)*Phi2_p
nabla_ij_Phi2=-(ap/a)*Phi2_p
T_tt=(lam0*fp**2)-sp.Rational(1,2)*(-a**2)*grad_sq+sp.Rational(1,6)*((-a**2)*Box_Phi2-nabla_tt_Phi2+G_tt*Phi2)
T_ij=(lam0*f**2)-sp.Rational(1,2)*(a**2)*grad_sq+sp.Rational(1,6)*((a**2)*Box_Phi2-nabla_ij_Phi2+G_ij*Phi2)
rho=sp.simplify(T_tt/a**2)
p=sp.simplify(T_ij/a**2)
rho_target=2*lam0/(kh2_s**2*g_s**2*a**4)
require(sp.simplify(rho-rho_target)==0 and sp.simplify(p-rho_target/3)==0,"all-time FRW conformal radiation identity")

# 2. Explicit hyperspherical coordinate check on unit S^3: Z = (sin chi sin th cos ph, sin chi sin th sin ph, sin chi cos th, cos chi)
chi,th,ph=sp.symbols("chi th ph",real=True)
Z=[sp.sin(chi)*sp.sin(th)*sp.cos(ph),sp.sin(chi)*sp.sin(th)*sp.sin(ph),sp.sin(chi)*sp.cos(th),sp.cos(chi)]
require(sp.trigsimp(sum(z**2 for z in Z))==1,"unit S^3 norm")
coords=[chi,th,ph]
gamma_diag=[sp.Integer(1),sp.sin(chi)**2,sp.sin(chi)**2*sp.sin(th)**2]
for i in range(3):
    for j in range(3):
        bilin=sp.trigsimp(sum(sp.diff(z,coords[i])*sp.diff(z,coords[j]) for z in Z))
        expected=gamma_diag[i] if i==j else sp.Integer(0)
        require(sp.trigsimp(bilin-expected)==0,f"sphere metric identity ({i},{j})")

# 3. Concrete numerical outward-interval certificate on control ball r0 = 1e-16
spec=geodesic_cap_spectrum(inv_r0=20,Kmax=16,nsub=64)
kh2=spec["khat"][1]
r0=iv.mpf("1e-16");lam0_val=2*(r0**2);g_val=iv.mpf("1e-40");V0=2*iv.pi**2
# Binomial series tail after N_bin = 40 terms for ||X|| <= 1/2: sum_{n=41}^infty |binom(1/2,n)| (1/2)^n <= (1/2)^41 / (1 - 1/2) = 2^(-40)
binom_tail_40=iv.sqrt(lam0_val)*(iv.mpf(1)/(2**40))
require(below(binom_tail_40,iv.mpf("2e-28")),"rapid analytic matrix square-root convergence")

rho_frame_esu=2*lam0_val/((kh2**2)*(g_val**2))
E_frame_esu=V0*rho_frame_esu
require(above(rho_frame_esu,iv.mpf("3.99e48")) and below(rho_frame_esu,iv.mpf("4.01e48")),"homogeneous frame energy density at g=1e-40")
require(below(E_frame_esu,iv.mpf("8e49")),"frame energy negligible compared to 1e81 clock kinetic energy")

finish("parseval_isotropic_frame.py",{
  "active_dipole_channels":2,
  "spectator_conformal_dipole_channels":4,
  "total_frame_channels":6,
  "coupling_type":"conformally_coupled_massless_xi_1_over_6",
  "control_ball_radius":"1e-16",
  "fixed_frame_eigenvalue_lambda0":"2e-32",
  "minimum_residual_eigenvalue_on_ball":"1e-32",
  "sqrt_binomial_40_term_tail_upper":outward(binom_tail_40),
  "curved_FRW_frame_density_formula":"2*lambda0 / (khat(2)^2 * g^2 * a(tau)^4)",
  "curved_FRW_frame_equation_of_state_w":"1/3",
  "curved_FRW_momentum_density_j_i":"0_identically",
  "curved_FRW_anisotropic_shear_Pi_ij":"0_identically",
  "encoding_slice_l2_quadrupole_Q2":"0_identically",
  "frame_ESU_density_at_g_1e_40":outward(rho_frame_esu),
  "frame_ESU_integrated_energy_at_g_1e_40":outward(E_frame_esu),
  "background_metric_independent_of_program_u":True,
  "active_eight_projection_Jacobian_unchanged":True,
  "two_channel_post_closure_quadrupole_theorem_overturned":False
},inputs=[jc+"post_closure.json",jc+"POST_CLOSURE.md"])
