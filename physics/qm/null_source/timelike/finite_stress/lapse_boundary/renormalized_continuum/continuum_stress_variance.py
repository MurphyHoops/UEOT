"""Exact O(K^5) sharp minimal-clock pressure variance vs uniform spacetime-smeared continuum stress variance."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
from model import frw_bounce_enclosure,eval_frw

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
load(jc+"sharp_charges.json");load(jc+"post_closure.json")
had=load(rc+"hadamard_cauchy_transport.json")

# 1. Exact oscillator Wick check for minimal-clock pressure p_X = 1/3 * (3/2 p^2 - 1/2 omega^2 q^2) and exact Faulhaber sum
w_s,k_s,K_s=sp.symbols("omega k K",integer=True,positive=True)
# q = (a + adag)/sqrt(2w), p = -i*sqrt(w/2)*(a - adag): coeff of (adag)^2 in (3/2 p^2 - 1/2 w^2 q^2) is -3w/4 - w/4 = -w;
# divided by 3 in p_X gives -(w/3)*(adag)^2, and ||(adag)^2 |0>||^2 = 2 -> mode variance = 2*(w/3)^2 = (2/9)*w^2!
mode_trace_pair_coeff=-sp.Rational(3,4)*w_s-sp.Rational(1,4)*w_s
require(sp.simplify(mode_trace_pair_coeff+w_s)==0,"additive kinetic+gradient pair coefficient in minimal-clock pressure")
pressure_sum=sp.simplify(sp.summation(sp.Rational(2,9)*(k_s**2)*(k_s**2-1),(k_s,2,K_s)))
expected_poly=(K_s-1)*K_s*(K_s+1)*(K_s+2)*(2*K_s+1)/45
require(sp.expand(pressure_sum-expected_poly)==0,"exact 2/45 K^5 minimal-clock sharp pressure variance formula")

sharp_p_var_K64=iv.mpf(2)/9*sum(iv.mpf(k*k)*(k*k-1) for k in range(2,65))
sharp_p_var_K512=iv.mpf(2)/9*sum(iv.mpf(k*k)*(k*k-1) for k in range(2,513))
require(above(sharp_p_var_K64,iv.mpf("4.7e7")) and above(sharp_p_var_K512,iv.mpf("1.5e12")),"exact O(K^5) sharp pressure blowup")

# 2. Uniform spacetime-smeared continuum stress variance on [1/2, 5/2] (dilation by 5 from [-1/5, 1/5]: B_{t,4} = B_4 / 5^4 < 2429):
B_t4=iv.mpf(1517824)/625
require(below(B_t4,2429),"exact 5^-4 temporal dilation bound")
zeta4=(iv.pi**4)/90
# All 11 scalar species (2 body + 6 conformal Parseval frame + 1 clock + 1 pointer + 1 beacon = 11 scalars), denominator (sqrt(3))^8 = 81:
N_species=11
vac_smeared_pair_var=4*N_species*(B_t4**2)*zeta4/81
require(below(vac_smeared_pair_var,iv.mpf("3.5e6")),"uniform K<=infinity spacetime-smeared vacuum stress variance")

hs_tot=box(had["body_continuum_HS_norm_squared_upper"])+box(had["minimal_clock_continuum_HS_norm_squared_upper"])
excited_fluct_var=4*vac_smeared_pair_var*(1+2*hs_tot)
require(below(excited_fluct_var,iv.mpf("1.5e7")),"uniform K<=infinity quantum mode stress variance")

# Integrated smeared energy functional int d^4x sqrt(-g) * (a(tau)^(-2) chi_t(tau) delta^mu_tau delta^nu_tau) T_{mu nu}:
# Canonical bar p_{X,0} = sqrt(V0)/g, Var(p_{X,0}) = 1/(4*a0) -> Var(1/2 p_{X,0}^2) = V0/(4*a0*g^2) + 1/(32*a0^2), scaled by a(tau)^(-4)
V0=2*iv.pi**2;g=iv.mpf(1)/10**40;a0=iv.mpf(4)
enc=frw_bounce_enclosure(N=220);a_max=eval_frw(enc,iv.mpf(5)/2)["a"]
clock_enthalpy_var_floor=V0/(4*a0*(g**2)*(a_max**4))
clock_enthalpy_var_upper=V0/(4*a0*(g**2))+iv.mpf("1e55")+excited_fluct_var
require(above(clock_enthalpy_var_floor,iv.mpf("1.23e80")) and below(clock_enthalpy_var_upper,iv.mpf("1.24e80")),"uniform continuum total smeared stress variance")

finish("continuum_stress_variance.py",{
  "sharp_slice_clock_pressure_variance_exact_formula":"(2/9) * sum_{k=2}^K k^2 (k^2 - 1)",
  "sharp_slice_clock_pressure_asymptotic_order":"(2/45) * K^5",
  "sharp_clock_pressure_variance_K64":outward(sharp_p_var_K64),
  "sharp_clock_pressure_variance_K512":outward(sharp_p_var_K512),
  "conformal_dipole_A_Z_sharp_variance_status":"finite_by_SHARP_CHARGES_conformal_cancellation",
  "general_sharp_slice_continuum_stress_variance_finite":False,
  "spacetime_test_window_tau":"[1/2, 5/2]",
  "temporal_bump_B4_L1_upper":outward(B_t4),
  "total_scalar_species_counted":N_species,
  "continuum_vacuum_smeared_pair_variance_upper":outward(vac_smeared_pair_var),
  "continuum_excited_quantum_mode_variance_upper":outward(excited_fluct_var),
  "continuum_total_smeared_energy_variance_lower":outward(clock_enthalpy_var_floor),
  "continuum_total_smeared_energy_variance_upper":outward(clock_enthalpy_var_upper),
  "uniform_in_K_up_to_infinity":True
},inputs=[jc+"sharp_charges.json",jc+"SHARP_CHARGES.md",jc+"post_closure.json",rc+"hadamard_cauchy_transport.json"])
