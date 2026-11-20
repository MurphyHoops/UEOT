"""Complete global records, local noise decomposition and actual thermal response."""
from common import *
history=json.loads((HERE/"history.json").read_text())
instrument=json.loads((HERE/"instrument.json").read_text())
assert history["status"]==instrument["status"]=="PASS"
oldabs=box(OLD_RESPONSE["full_characteristic_bracket_absolute_upper"])
rate=iv.mpf([1,3])
ratio=1+12/(rate**2+12)
maximum_occupation=iv.mpf(".020")
thermal_upper=2*J*maximum_occupation*ratio/3
assert below(thermal_upper,".01801")
fullabs=oldabs+thermal_upper
assert below(fullabs,4)
cases={}
for name in ["success","failure"]:
    row=history["cases"][name]
    x=box(row["x"]);A=iv.sqrt(x);n=box(row["thermal_occupation_per_oscillator"])
    v=box(row["variance_S0"])
    V=2*iv.pi**2*A**3
    Es=iv.pi**2*M/A**3
    Ec=2*V*B(x)/x**2+(U0X0/X0)*V-1/(2*A)
    Omega=iv.sqrt(3)/A
    zero_variance=Es**2*v
    thermal_variance=24*n*(1+n)/x
    total_variance=zero_variance+thermal_variance
    density_variance=total_variance/V**2
    relative_variance=density_variance/(3/(2*x))**2
    assert above(thermal_variance) and above(zero_variance)
    assert above(relative_variance,".01")
    growth_error=8/(3*x)
    character_at_1=iv.mpf(-3)+iv.mpf([-4,4])*2/x
    character_at_3=iv.mpf(5)+iv.mpf([-4,4])*2/x
    assert below(character_at_1,0) and above(character_at_3)
    cases[name]={"Ec":outward(Ec),"Es":outward(Es),"Omega":outward(Omega),
       "mean_H":outward(3*iv.pi**2*A),
       "variance_H_zero":outward(zero_variance),"variance_H_thermal":outward(thermal_variance),
       "variance_H_complete":outward(total_variance),"variance_density_complete":outward(density_variance),
       "relative_density_RMS":outward(iv.sqrt(relative_variance)),
       "characteristic_at_1":outward(character_at_1),"characteristic_at_3":outward(character_at_3),
       "absolute_growth_s_minus_2_upper":outward(growth_error),
       "proper_time_growth_rate":outward(iv.mpf([2-growth_error.b,2+growth_error.b])/A)}
finish("response.py",{
 "complete_H":"Ec+Es*S0+sqrt(3)/A*N; N independent NB(shape=8, mean=8*n)",
 "complete_Laplace":"exp(-s*Ec)*L_i(s*Es)*(1+n*(1-exp(-s*sqrt(3)/A)))^(-8)",
 "variance_H":"Es^2*v_i+24*n*(1+n)/x",
 "variance_density":"M2^2*v_i/(4*x^6)+6*n*(1+n)/(pi^4*x^4)",
 "local_noise":"2*N_high,i + (2*pi^2*M2*mu_i)*N_linear,i + (2*pi^2*M2)^2*v_i*C_i tensor C_i",
 "local_noise_definitions":"T[psi+P*f0]=Q_high+P*L_high+P^2*C; kernels symmetrized connected",
 "zero_high_cross_noise_retained":True,"high_quadratic_noise_retained":True,
 "new_local_noise_kernel_numerically_summed":False,
 "joint_old_new_all_O2_invariant_records_equal":True,
 "geometry_label_included_in_equivalence":True,
 "original_first_field_marginal_unchanged":False,
 "thermal_pressure_response":"-(4/3)*rho_th*(1+s^2/(s^2+12))*epsilon",
 "characteristic_correction":"4*J*n/(3*x)*(s^2+24)/(s^2+12)",
 "thermal_bracket_upper":outward(thermal_upper),
 "full_characteristic_bracket_absolute_upper":outward(fullabs),
 "all_AE_contacts_retained":True,"positive_growth_root_exists":True,
 "same_n0_symbol_reused_without_state_correction":False,
 "nonlinear_instability_theorem_claimed":False,"cases":cases,
 "fixed_state_linear_FLRW_stochastic_constraint_still_obstructed":True,
 "physical_gravity_instrument_constructed":False},
 extra=("history.json","instrument.json"))
