"""Certified complete-source tail, positive finite clock, and distinct residuals."""
import sympy as s
from common import *
ES=iv.pi**2*M2/A**3
u=OMEGA/ES
lam=exact(1000)
den=1-lam/NU0
thermal_den=1-N*(iv.exp(lam*u)-1)
assert above(den) and above(thermal_den)
rhi=1+iv.sqrt(3)/2
logB=-iv.log(den)+lam*rhi/den+iv.log((1+iv.exp(-lam*(rhi-1)/den))/2)-8*iv.log(thermal_den)-2*lam
B=iv.exp(logB)
tail1=ES*B/(iv.exp(1)*lam)
tail2=4*ES**2*B/(iv.exp(2)*lam**2)
T=exact(1)/24
distance=T*iv.sqrt(tail2)
assert below(iv.sqrt(tail2),"2.37e-27")
assert below(distance,"9.88e-29")
R=exact(4)
zmin=1-2*iv.exp(-32)
varlo=exact(1)/4-(R*iv.sqrt(2/iv.pi)/2+exact(1)/2)*iv.exp(-32)
varhi=1/(4*zmin)
rmslo=iv.sqrt(varlo);rmshi=iv.sqrt(varhi+tail2)
assert above(rmslo,".4999999999999") and below(rmshi,".5000000000001")
g0sq=1/iv.sqrt(2*iv.pi)*(1-iv.exp(-R**2)/(R*iv.sqrt(iv.pi)))**2
windowprob=2*T*iv.cos(exact(1)/3)**2*g0sq
assert above(windowprob,".029")
E0=exact("2.01")*ES+9
meanH=ES*box(CASE["mu"])+8*N*OMEGA
clockbase=E0-meanH
clockmean=clockbase+iv.mpf([0,tail1.b])
mean_original_total=3*iv.pi**2*A
fraction=clockmean/mean_original_total
assert above(fraction,".134") and below(fraction,".135")
# Exact maxima for exponential-moment tail control.
z,k=s.symbols("z k",positive=True)
assert s.simplify(s.diff(z*z*s.exp(-k*z),z).subs(z,2/k))==0
assert s.simplify((z*z*s.exp(-k*z)).subs(z,2/k))==4*s.exp(-2)/k**2
assert s.simplify(s.diff(z*s.exp(-k*z),z).subs(z,1/k))==0
finish("positive_clock.py",{
 "Es_proper_energy_scale":outward(ES),"thermal_quantum_over_Es":outward(u),
 "Chernoff_s":1000,"zero_MGF_denominator":outward(den),
 "thermal_MGF_denominator":outward(thermal_den),"log_tail_probability_upper":outward(logB),
 "tail_probability_upper":outward(B),"cap_error_energy_first_moment_upper":outward(tail1),
 "cap_error_energy_second_moment_upper":outward(tail2),
 "cap_error_energy_RMS_upper":outward(iv.sqrt(tail2)),
 "proper_time_window":"[-1/24,1/24]","conditional_trace_distance_upper":outward(distance),
 "initial_density_derivative_trace_norm_error_upper":outward(2*iv.sqrt(tail2)),
 "clock_packet_variance_lower":outward(varlo),"clock_packet_variance_upper":outward(varhi),
 "full_constraint_RMS_lower":outward(rmslo),"full_constraint_RMS_upper":outward(rmshi),
 "positive_clock_energy_support_lower":1,"positive_clock_energy_support_upper":outward(E0+8),
 "clock_window_probability_lower":outward(windowprob),
 "mean_clock_energy":outward(clockmean),"mean_clock_energy_fraction_of_original_total":outward(fraction),
 "source_tail_discarded":False,"full_bare_source_marginal_unchanged":False,
 "conditional_source_at_zero_exact":True,"all_unbounded_RSET_derivatives_certified":False,
 "capped_generator_claimed_original_full_local_QFT":False,
 "Einstein_history_or_local_clock_apparatus_constructed":False})
