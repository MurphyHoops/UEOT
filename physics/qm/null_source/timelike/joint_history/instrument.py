"""Actual smooth two-record filter, including failure and state backreaction."""
from common import *
r=filter_data()
assert above(NU,"3.6e11") and below(NU,"3.8e11")
assert above(r["success_probability"],"0.49999999999925") and below(r["success_probability"],"0.5")
for name in ["success_mean_drop","failure_mean_rise"]:
    assert above(r[name],"1.8749e-13") and below(r[name],"1.8751e-13")
for name in ["success_variance","failure_variance"]:
    assert above(r[name],"0.18749") and below(r[name],"0.18751")
assert above(r["success_mean"]) and above(r["failure_mean"])
assert above(1/NU0-r["failure_mean_rise"])
assert above(1-Q)
finish("instrument.py",{
 "filter":{"observable":"S0=(P1^2+P2^2)/(2*pi^2*M2), identity on nonzero modes",
           "q":"1/2","t":"1e-12","K1":"sqrt(q)*exp(-t*S0/2)",
           "K0":"sqrt(1-q*exp(-t*S0))","complete_CP_TP_instrument":True,
           "both_momentum_multipliers_smooth_Schwartz_preserving":True},
 "nu0":outward(NU0),"nu_preparation":outward(NU),
 "input_mean":outward(MU),"input_variance":outward(VAR),
 "posterior":{k:outward(v) for k,v in r.items()},
 "complete_posterior_Laplace":{"success":"Z(t+s)/Z(t)",
       "failure":"(Z(s)-q*Z(t+s))/(1-q*Z(t))",
       "input":"Z(s)=(1+2*s/nu)^(-1)*E_R exp(-s*R/(1+2*s/nu))"},
 "success_canonical_state":{"conditional_coherent_momentum":"kappa*(y,z)/c",
       "centered_VarP":"x0/(4*c)","desheared_VarQ":"c/x0",
       "actual_VarQ":"c/x0+beta[g]^2*x0/(4*c)","actual_CovQP":"beta[g]*x0/(4*c)"},
 "failure_state_claimed_Gaussian":False,
 "original_full_first_field_marginal_preserved":False,
 "S0_is_complete_energy_after_thermal_preparation":False,
 "fixed_background_nonselective_stress_records_preserved":True,
 "preservation_extended_to_record_dependent_geometry_preparation":False,
 "local_causal_device_constructed":False})
