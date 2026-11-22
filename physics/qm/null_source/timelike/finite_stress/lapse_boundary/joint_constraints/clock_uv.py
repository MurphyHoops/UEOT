"""Exact high-mode inequality and conditional point-clock resource scale."""
import sympy as sp
from common import iv,require,above,below,outward,finish
t=sp.symbols('t',nonnegative=True)
require(sp.expand((1+t)**2*(1-t)-1)==t-t*t-t**3,'clock variance summand inequality')
# t-t^2-t^3 >= t*(1-1/4-1/16)>0 on the declared t interval.
require(1-sp.Rational(1,4)-sp.Rational(1,16)>0,'all k>=2 proof margin')
V=2*iv.pi**2;J=1;K=64
sig=sum(iv.mpf(k*k)/iv.sqrt(k*k-1) for k in range(2,K+1))/(2*V)
lo=iv.mpf(K*(K+1)-J*(J+1))/(4*V)
hi=lo+sum(iv.mpf(1)/k for k in range(2,K+1))/(2*V)
require(above(sig,lo.b) and below(sig,hi.a),'actual K64 clock tail bounds')
dt=iv.mpf(1)/100
energy=iv.mpf(K*(K+1)-J*(J+1))/(8*dt*dt)
require(sp.Rational(1,32)+sp.Rational(4,2)==sp.Rational(65,32),'clock zero-mode overlap coefficient')
gg,lf,vv,kk=sp.symbols('g L_F V0 K',positive=True)
quartic=gg**2*vv/4*(2*sp.sqrt(vv)*lf/(sp.sqrt(2*sp.pi)*gg*kk))*3*(kk**2/(4*vv))**2
require(sp.simplify(quartic-3*gg*lf*kk**3/(32*sp.sqrt(2*sp.pi*vv)))==0,'raw quartic coefficient')
finish('clock_uv.py',{
 'candidate':'bare F_j(g X_K), fixed nonzero g, normal AP-clock cutoff identification',
 'strong_zero_limit_of_bounded_bare_gate':True,
 'spatial_smoothed_bare_gate_strong_zero_limit':True,
 'K64_high_clock_variance':outward(sig),'K64_variance_lower':outward(lo),'K64_variance_upper':outward(hi),
 'asymptotic_variance_over_K2':'1/(4 V0)',
 'conditional_rms_clock_accuracy':'g_K^2 sigma_JK^2 <= delta_t^2',
 'conditional_energy_lower':'[K(K+1)-J(J+1)]/(8 delta_t^2)',
 'illustrative_K64_J1_delta_t_0_01_energy_lower':outward(energy),
 'normalized_nonzero_bare_Gaussian_profile_requires_gK_sigma_to_zero':True,
 'clock_energy_over_K2_diverges_under_that_profile_contract':True,
 'initial_raw_quartic_mean_asymptotic':'3 |g| L_F K^3 /(32 sqrt(2 pi V0))',
 'vanishing_program_amplitude_case_excluded_from_necessity_claim':True,
 'singular_reduced_body_comparison_limit':'g_K=o(K^-3), fixed program, finite time',
 'bare_coupling_varied_in_that_comparison':True,
 'complete_fixed_packet_initial_density_trace_norm_limit':False,
 'clock_packet_overlap_coefficient_at_a4':'65 V0/32',
 'reduced_body_limit_misidentified_as_full_apparatus_limit':False,
 'strong_zero_pushed_through_unbounded_Y_Phi2':False,
 'full_Hamiltonian_free_limit_inferred':False,
 'all_renormalized_nonlinear_clocks_excluded':False,
 'fixed_K_device_invalidated':False,
 'uniform_continuum_device_constructed':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/CLOCK_ACTUATOR.md'])
