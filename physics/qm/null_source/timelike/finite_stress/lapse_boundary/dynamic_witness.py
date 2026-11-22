"""Actual-history interval witnesses; frozen prior outputs are read, never executed."""
from common import iv, load, box, exact, above, below, outward, require, finish
inputs = ["dynamic_seed/bounds.json", "dynamic_inverse/fast_root.json",
          "joint_history/history.json", "finite_stress/geometry_matching.json", "finite_stress/BOUNDARY_STATE.md",
          "finite_stress/lapse_boundary/TENSOR_NOISE.md"]
s = box(load(inputs[0])["positive_root_s"])
sf = box(load(inputs[1])["fast_conformal_growth_rate"])
hist = load(inputs[2])["cases"]["unfiltered"]
A = box(hist["A"]); p = 4*box(hist["thermal_occupation_per_oscillator"])
prior = load(inputs[3])
V0=2*iv.pi**2; om=iv.sqrt(3); c=iv.mpf("1e-55"); rho=iv.mpf("1e-25")
W=lambda x:(1+x)**4*iv.ln(iv.e+x)
Ws,Wf,W2=W(s),W(sf),W(2*s)
C0=iv.mpf("2e20")*6400/(2*(1-iv.mpf(".128")))
Rx=iv.exp(s/sf); Ry=iv.e; wm=iv.mpf("1.1")*c
rT=Ws*c*Rx+Wf*wm*Ry
require(below(rT,rho/2),"Future seed leaves contraction ball")
Delta=C0*(Ws*c*Rx)**2/W2+C0*rT**2/Wf
r=c*Rx+wm*Ry+Delta
t=r+r*r/4; F0=1/(1-t); F1=t/(1-t)
D0=2*om*r*F0/(1-r); D2=r*D0+2*om*r*F1
err=iv.exp(4*r)*(F1*D0+D2+D0*D0/(2*om))+(iv.exp(4*r)-1)*2*om*r
T=1/sf; theta=2*om*T
imag=lambda lam:2*om**2*lam/(lam*lam+4*om**2)
blow=c*imag(s)-wm*Ry*imag(sf)-theta*om*(c*Rx+wm*Ry)-om*Delta-err/2
bup=om*r+err/2
require(above(blow/c,".7"),"Positive-window density witness failed")
dr_lo=32*p*(iv.mpf(".7")*c/(V0*A**4))**2
dr_hi=32*p*(bup/(V0*A**4))**2
require(below(iv.exp(iv.mpf(2)/3),2),"Bump mu2 lower bound")
sigma=om/(100*A)
absrho_lo=sigma*sigma*iv.exp(-12*rho)/(128*V0*V0*A**6)
ratio_rho=dr_hi/absrho_lo
M=450000
require(below(M*T,".5"),"Coherent-band phase bound failed")
require(above(iv.mpf(7)/24-8*rho,iv.mpf(1)/4),"Dynamic pressure envelope bound failed")
SM=M*(M-1)*(M+1)*(M+2)*(2*M+1)//10-12
# Independent polynomial check at several small M, not 450000 enumerated modes.
for m in (3,4,11,31):
    require(sum(k**4-k*k for k in range(3,m+1))==
            m*(m-1)*(m+1)*(m+2)*(2*m+1)//10-12,"Closed power sum wrong")
pressure_var_lo=iv.mpf(SM)/(4*V0*V0*A**8)
pressure_rms_lo=iv.sqrt(pressure_var_lo)
mean_upper=iv.exp(2*rho)*(rho+(1+rho*rho)/2)/(A*A)
pressure_ratio=pressure_rms_lo/mean_upper
require(above(pressure_ratio,400),"Absolute pressure budget not separated")
pressure_contrast_ratio=96*p/SM
require(below(pressure_contrast_ratio,"3e-27"),"Pressure contrast baseline bound failed")
require(above(s,"1.5") and below(p,1) and above(p),"Frozen input ranges")
finish("dynamic_witness.py",dict(
 future_seed_E4_upper=outward(rT), future_remainder_A_upper=outward(Delta),
 actual_U_A_upper=outward(r), density_pair_imag_lower_over_c=outward(blow/c),
 density_pair_absolute_upper_numerator=outward(bup),
 density_noise_difference_lower_bound=outward(dr_lo),
 density_noise_difference_upper_bound=outward(dr_hi),
 density_absolute_profile_lower_bound=outward(absrho_lo),
 density_contrast_over_absolute_upper=outward(ratio_rho),
 pressure_coherent_vacuum_band=[3,M], band_power_sum=str(SM),
 conformal_duration=outward(T), proper_duration_reused=prior["corrected_proper_duration_bounds"],
 absolute_pressure_variance_lower_bound=outward(pressure_var_lo),
 absolute_pressure_RMS_lower_bound=outward(pressure_rms_lo),
 absolute_mean_pressure_upper_bound=outward(mean_upper),
 pressure_RMS_over_mean_lower_bound=outward(pressure_ratio),
 pressure_contrast_over_absolute_upper=outward(pressure_contrast_ratio),
 test_domain="all nonnegative unit C-infinity tests compactly supported in the same actual I",
 same_once_selected_history=True, time_units="model only", metric_error_claimed=False,
 all_window_filters_or_histories_excluded=False,
 source_charge_RMS_implies_weak_full_stress_noise=False),inputs,proof="DYNAMIC_WITNESS.md")
