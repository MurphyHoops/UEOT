"""New once-selected quiet source window and exact mean-family sensitivity."""
from common import iv,load,box,above,below,outward,require,finish
inputs=["dynamic_seed/bounds.json","dynamic_inverse/fast_root.json",
        "joint_history/history.json","finite_stress/geometry_matching.json",
        "nonlinear_history/EXISTENCE.md"]
s=box(load(inputs[0])["positive_root_s"])
sf=box(load(inputs[1])["fast_conformal_growth_rate"])
h=load(inputs[2])["cases"]["unfiltered"];A=box(h["A"])
p=4*box(h["thermal_occupation_per_oscillator"]);om=iv.sqrt(3);V0=2*iv.pi**2
c=iv.exp(-20000);T=iv.mpf(1)/50;rho=iv.mpf("1e-25")
Rz=iv.mpf("1e-28");Ry=iv.mpf("1e-51")
zz=c*iv.exp(s*T);yy=iv.mpf("1.1")*c*iv.exp(sf*T)
require(below(zz,Rz) and below(yy,Ry) and below(c,"1e-55"),"New history invalid")
W=lambda x:(1+x)**4*iv.ln(iv.e+x)
rT=W(s)*zz+W(sf)*yy;C0=iv.mpf("2e20")*6400/(2*(1-iv.mpf(".128")))
t=rT+C0*rT*rT;tq=iv.exp(-1100)
require(below(iv.ln(rT),-1159) and below(iv.ln(t),-1158) and below(t,tq),"Future E4 bound")
ell=T/4;K=200;require(bool((ell*200).a<=1) and bool((ell*200).b>=1),"Smoother scale enclosure")
Sm=iv.mpf(201)**5/5+iv.mpf(16)/9*200**6/200
require(below(Sm,"6.4e11"),"Full static vacuum sum")
S2=iv.mpf(401)**2;S3=iv.mpf(401)**3
require(below(4*tq*S3,1),"Dynamic pressure correction")
require(below(p,".08") and below(om,2),"Low state range")
low=(om/50)**2+4*p*(1-p)*(3*om)**2+20*(om/2)**2
require(below(low,24),"Complete low-mode budget")
pratio=iv.mpf(533340)/(iv.mpf(".49")*V0*A*A)
rratio=iv.mpf(".1")/(iv.mpf("1.49")*V0*A*A)
require(below(pratio,"1e-5") and below(rratio,"1e-12"),"Quiet source ratios")
# Conservative positive sum of all density components beyond profile.
density_coefficient=om/50+2*om*20*tq+iv.sqrt(20)*tq*S2/3+2*tq*S2
require(below(density_coefficient,".1"),"Full density budget")
# Both coordinates below a single dimensionless radius.
radius=zz/Rz+yy/Ry
delta=rho/Ry*2*radius/(1-radius)**2
require(below(iv.ln(delta),-500),"Exact-family derivative bound")
d=iv.mpf("1e-100")
require(below(delta,d),"Rounded derivative bound")
ef=iv.exp(sf*T);es=iv.exp(s*T)
Zlo=(1-d)*ef-(1+d)**2/(1-d)*es
slopehi=(sf-s)*(1+d)+2*d/(1-d)
gain=Zlo/slopehi
require(above(iv.ln(gain),18709),"Conformal anchored fast sensitivity")
# Compare scale at the same proper time from the common initial slice.
correction=rho*iv.exp(2*rho)*((1+d)*(ef-1)/sf+(1+d)**2/(1-d)*(es-1)/s)
propergain=(Zlo-correction)/slopehi
require(above(iv.ln(propergain),18709),"Proper-time fast sensitivity")
finish("quiet_window.py",dict(
 new_initial_slow_amplitude_exact="exp(-20000)",
 new_finite_slice_fast_root="unique b(c), 0.9c<b(c)<1.1c, U(-c,b(c))=0",
 original_fixed_c_history_extended=False, parameters_reselected_in_time=False,
 conformal_duration="1/50", proper_duration_model_units=outward(A*T*iv.exp(iv.mpf([-1,1])*rho)),
 log_future_E4_seed_upper=outward(iv.ln(rT)), log_future_E4_U_upper=outward(iv.ln(t)),
 exact_smoother="three length-T/4 normalized boxes convolved with C-infinity unit mollifier supported +/-T/16; centered T/2",
 complete_static_high_pressure_sum_upper=outward(Sm),
 complete_source_pressure_relative_RMS_upper=outward(pratio),
 complete_source_density_relative_RMS_upper=outward(rratio),
 initial_source_sigma_changed=False,
 log_family_derivative_error_upper=outward(iv.ln(delta)),
 log_fast_exponential=outward(sf*T),
 log_initial_h_normalized_scale_sensitivity_lower=outward(iv.ln(gain)),
 log_same_proper_time_scale_sensitivity_lower=outward(iv.ln(propergain)),
 family_tangent_respects_same_incoming_state_transport=True,
 family_tangent_holds_finite_slice_raw_density_fixed=False,
 stochastic_metric_variance_or_forced_gain_computed=False,
 all_local_tensor_tests_weak_noise=False, preparation_precision_physically_implemented=False),
 inputs,proof="QUIET_WINDOW.md")
