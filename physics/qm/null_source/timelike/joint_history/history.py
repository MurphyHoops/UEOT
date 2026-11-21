"""Directed enclosures for one complete mean history per actual filter record."""
from common import *
r=filter_data()
assert above(X0,4*32768**2) and below(X0,9*32768**2)
assert below(E(X0),0)
assert above(U0X0,1) and below(U0X0,"1.0000000001")
assert above(NU0,"1.8e11") and below(NU0,"1.9e11")
hlo,hhi=iv.mpf(".004"),iv.mpf(".0045")
coarse=interval(hlo,hhi)
phi_lo=shifted_phi(hlo);phi_hi=shifted_phi(hhi)
assert below(phi_lo,iv.mpf(".96")/(4*iv.pi**2))
assert above(phi_hi,iv.mpf("1.04")/(4*iv.pi**2))
derivative=(12*U0X0-6-K/X0)-2*(12*U0X0-3)*coarse/X0+12*U0X0*coarse**2/X0**2
assert above(derivative,"5.999")
data={"unfiltered":(iv.mpf(1),MU,VAR),
      "success":(1+NU0*r["success_mean_drop"],r["success_mean"],r["success_variance"]),
      "failure":(1-NU0*r["failure_mean_rise"],r["failure_mean"],r["failure_variance"])}
cases={}
for name,(label,mu,var) in data.items():
    assert above(label,".96") and below(label,"1.04")
    h=coarse
    a=12*U0X0-6-K/X0
    b=12*U0X0-3
    # Every exact root in the preceding enclosure belongs to this image.
    # The initial bracket supplies existence; G'>0 supplies uniqueness.
    for _ in range(6):
        image=(label/(4*iv.pi**2)+b*h**2/X0-4*U0X0*h**3/X0**2)/a
        left=max(h.a,image.a);right=min(h.b,image.b)
        assert bool(left<=right)
        h=iv.mpf([left,right])
    assert above(h,".004") and below(h,".0045")
    x=X0-h
    occupation=shifted_thermal(h)/J
    assert above(occupation,".017") and below(occupation,".020")
    assert above(x,4*32768**2) and below(x,9*32768**2)
    cases[name]={"r":outward(label),"mu":outward(mu),"variance_S0":outward(var),
         "x0_minus_x":outward(h),"x":outward(x),"A":outward(iv.sqrt(x)),
         "thermal_occupation_per_oscillator":outward(occupation),
         "rho_total":outward(3/(2*x)),"pressure_total":outward(-1/(2*x)),
         "unique_positive_radius_root":True,"thermal_occupation_nonnegative":True}
finish("history.py",{
 "fixed_M2":outward(M),"fixed_U0":outward(U0X0/X0),"x0":outward(X0),
 "U0_times_x0":outward(U0X0),"old_mean":outward(MU_OLD),
 "preparation":{"zero_centered_VarP":"x0/4","zero_desheared_VarQ":"1/x0",
     "nonzero_modes":"static vacuum at each actual geometry; both complete k=2 shells thermal",
     "thermal_real_oscillators":8,"same_U0_for_all_records":True,
     "same_original_full_state_as_predecessor":False},
 "root_proof":{"coarse_h":[".004",".0045"],"phi_at_lower":outward(phi_lo),
     "phi_at_upper":outward(phi_hi),"phi_derivative_on_bracket":outward(derivative),
     "image_refinements":6,"uses_correlated_old_root_identities":True,
     "positive_root_uniqueness":"G'=3*G/x+3*x+2*kappa>0 on G>0"},
 "cases":cases,"all_eta_real_mean_history":True,
 "mean_constraint_and_spatial_equation_residuals":"identically zero, algebra.py identities",
 "normal_time_derivatives_of_mean_residuals":"identically zero for every order",
 "positive_normal_Hadamard_state_each_record":True,
 "source_second_moment_fixed_along_each_history":"M2*mu_i",
 "parameters_reselected_in_time":False,"local_preparation_controller_constructed":False,
 "operator_constraint_solved":False})
