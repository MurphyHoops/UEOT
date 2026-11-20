"""Actual correlated matter boundary state, global noise and resource budgets."""
import json,hashlib
import sympy as s
from common import *
old_witness=json.loads((TIMELIKE/"total_source/history_witness.json").read_text())
assert old_witness["status"]=="PASS"
assert old_witness["beta2_strict_lower"]=="33/100000"
assert old_witness["beta2_strict_upper"]=="1/600"
assert old_witness["zero_mode_relative_propagator_exact_identity"] is True
for rel,digest in old_witness["source_sha256"].items():
    assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest
n=box(CASE["thermal_occupation_per_oscillator"])
mu=box(CASE["mu"])
prob=4*n
eps=iv.sqrt(3)/A
vol=V0*A**3
kappaE=K2/(2*A**3)
ez=kappaE*mu
estar=ez+2*prob*eps
e0=estar
e2=estar-2*eps
sigma=eps/100
assert above(prob) and below(prob,1) and above(e2-sigma)
assert below(sigma/kappaE,iv.mpf(1)/100)
Rlo=(e2-kappaE/100)/kappaE
Rhi=(e0+kappaE/100)/kappaE
assert above(Rlo,iv.mpf(7)/5) and below(Rhi,iv.mpf(3)/2)
gap1=iv.sqrt(iv.mpf(7)/5)-1
gap2=iv.sqrt(RHI)-iv.sqrt(iv.mpf(3)/2)
assert above(gap2) and below(gap2,gap1.a)
tail_log=-NU0*gap2**2
rho_mean=3/(2*A**2)
density_rms_upper=1/(100*V0*A**4)
density_relative_upper=1/(150*V0*A**2)
qratio_lower=iv.pi**2*ez*X0/(4*A**3*sigma**2)
pplus=(sigma**2/(3*vol**2)
 +(iv.mpf(200000)/27+(16+56*prob-16*prob**2)/3)/(V0**2*A**8))
pminus=(sigma**2/(3*vol**2)
 +(iv.mpf(200000)/27+(16+24*prob-16*prob**2)/3)/(V0**2*A**8))
Dnew=8*prob*4*(iv.sqrt(3)/(3*V0*A**4))**2
contrast=iv.mpf("0.9")*prob*4*(iv.mpf(33)/100000)**2/(1+iv.mpf(1)/360000)**3
assert above(Dnew) and above(contrast)
p,E,w,sg,m2=s.symbols("p E w sg m2",real=True)
E0=E+2*p*w
E2=E-2*(1-p)*w
assert s.expand((1-p)*E0+p*E2-E)==0
variance_z=s.expand(sg**2*m2+(1-p)*(E0-E)**2+p*(E2-E)**2)
variance_shell=4*p*(1-p)*w**2
covariance=s.expand((1-p)*(E0-E)*(-2*p*w)+p*(E2-E)*(2*(1-p)*w))
assert s.simplify(covariance+variance_shell)==0
assert s.simplify(variance_z+variance_shell+2*covariance-sg**2*m2)==0
assert s.simplify((1-p)*E0**2+p*E2**2-E**2-4*w**2*p*(1-p))==0
# Exact finite-support Fock algebra, not a numerical occupation cutoff.
vac=(0,)*8
def add(a,b,scale=1):
    out=dict(a)
    for k,v in b.items():
        out[k]=s.simplify(out.get(k,0)+scale*v)
        if out[k]==0:del out[k]
    return out
def lower(state,j):
    out={}
    for k,v in state.items():
        if k[j]:
            t=list(k);t[j]-=1;t=tuple(t)
            out[t]=out.get(t,0)+s.sqrt(k[j])*v
    return out
def raise_(state,j):
    out={}
    for k,v in state.items():
        t=list(k);t[j]+=1;t=tuple(t)
        out[t]=out.get(t,0)+s.sqrt(k[j]+1)*v
    return out
def pair(state,up=False):
    out={}
    op=raise_ if up else lower
    for j in range(8):out=add(out,op(op(state,j),j))
    return out
def inner(a,b):return s.simplify(sum(s.conjugate(v)*b.get(k,0) for k,v in a.items()))
def branch(species):
    out={}
    for j in range(4*species,4*(species+1)):
        k=list(vac);k[j]=2;out[tuple(k)]=s.Rational(1,2)
    return out
a1,a2=branch(0),branch(1)
plus={k:v/s.sqrt(2) for k,v in add(a1,a2).items()}
minus={k:v/s.sqrt(2) for k,v in add(a1,a2,-1).items()}
vacuum={vac:s.Integer(1)}
for state,expected in [(vacuum,16),(plus,56),(minus,24)]:
    assert inner(state,state)==1
    Q=add(pair(state),pair(state,True))
    assert inner(Q,Q)==expected
for state in [plus,minus]:
    for j in range(8):
        for k in range(8):
            assert inner(state,raise_(lower(state,k),j))==(s.Rational(1,4) if j==k else 0)
            assert inner(state,lower(lower(state,k),j))==0
assert pair(plus)=={vac:s.Integer(4)} and pair(minus)=={}
Qplus=16*(1-p)+56*p
Qminus=16*(1-p)+24*p
assert s.expand(Qplus-Qminus)==32*p
assert s.expand(16*p*(1-p)+Qplus-(16+56*p-16*p**2))==0
assert s.expand(16*p*(1-p)+Qminus-(16+24*p-16*p**2))==0
assert s.Rational(1200)**2/s.Integer(144)*s.Rational(20,27)==s.Rational(200000,27)
assert 1-s.Rational(12,24)==s.Rational(1,2)

# Exact Bargmann coefficients and actual normalized NOON sums.
ac,be,bc,zz,ww,y=s.symbols("ac be bc zz ww y",nonzero=True)
kernel=s.exp(be*zz**2/(2*ac)+zz*ww/ac-bc*ww**2/(2*ac))
v22=s.diff(kernel,zz,2,ww,2).subs({zz:0,ww:0})/2
v20=s.diff(kernel,zz,2).subs({zz:0,ww:0})/s.sqrt(2)
v02=s.diff(kernel,ww,2).subs({zz:0,ww:0})/s.sqrt(2)
v22=s.factor(v22.subs(be*bc,y))
v20v02=s.factor((v20*v02).subs(be*bc,y))
assert s.simplify(v22-(1-y/2)/ac**2)==0
assert s.simplify(v20v02+y/(2*ac**2))==0
for state,expected in [(plus,(1-4*y)/ac**6),(minus,1/ac**6)]:
    amplitude=sum(s.conjugate(cj)*ck*(v22 if j==k else v20v02)/ac**4
                  for j,cj in state.items() for k,ck in state.items())
    assert s.simplify(amplitude-expected)==0
assert s.simplify(1-(1-4*y)/(1+y)-5*y/(1+y))==0
assert s.simplify(1-1/(1+y)-y/(1+y))==0
assert s.simplify(E0+4*w-(E2+6*w))==0
assert s.Rational(1,5)/24+(s.Rational(1,3)**2)/(8*(1-s.Rational(1,3)/2))==s.Rational(1,40)
assert above(1-5*prob) and above(1-2*prob)

finish("boundary_state.py",{
 "original_two_field_action_retained":True,
 "new_gravity_or_clock_model_introduced":False,
 "normal_rank_two_correlated_source":True,
 "new_source_preserves_complete_original_bare_state":False,
 "mean_unfiltered_zero_energy":outward(ez),
 "shell_N2_probability":outward(prob),
 "minimum_zero_energy_center":outward(e2),
 "example_sigma":outward(sigma),
 "sigma_is_support_width_not_energy_RMS":True,
 "all_parameters_fixed_on_one_initial_slice":True,
 "example_global_density_RMS_strict_upper":outward(density_rms_upper),
 "example_global_density_relative_RMS_strict_upper":outward(density_relative_upper),
 "same_original_static_total_mean_RSET":True,
 "same_total_mean_functional_requires_common_shift_invariant_transport":True,
 "complete_W2_between_new_NOON_signs_same":True,
 "complete_W2_new_equals_original":False,
 "standard_normal_matter_energy_point_spectrum_empty":True,
 "exact_normal_zero_energy_variance_possible":False,
 "zero_width_trace_one_normal_limit_claimed":False,
 "complete_spatial_average_rho_p_covariance_derived":True,
 "all_absolute_local_tensor_noise_components_computed":False,
 "cross_k_N_and_pair_covariances_computed_not_assumed_independent":True,
 "raw_equal_time_pressure_noise_value_used":False,
 "smeared_pressure_plus_RMS_strict_upper":outward(iv.sqrt(pplus)),
 "smeared_pressure_minus_RMS_strict_upper":outward(iv.sqrt(pminus)),
 "smeared_pressure_plus_relative_to_rho_mean_RMS_strict_upper":outward(iv.sqrt(pplus)/rho_mean),
 "local_pressure_difference_amplitude":outward(Dnew),
 "same_smooth_test_pressure_variance_difference_strict_lower":outward(Dnew/4),
 "balanced_prescribed_full_field_influence_contrast_strict_lower":outward(contrast),
 "exact_correlated_nonGaussian_homogeneous_boundary_factor_derived":True,
 "common_canonical_endpoint_and_implementable_evolutions_required":True,
 "unrestricted_infinite_vacuum_phase_newly_computed":False,
 "exact_static_total_energy_characteristic_function_checked":True,
 "B_plus_modulus_lower":outward(1-5*prob),
 "B_minus_modulus_lower":outward(1-2*prob),
 "zero_profile_log_domain":"real |A^3 sigma DeltaI|<=1, declared decreasing even bump",
 "zero_profile_quadratic_cumulant_error_bound":"|z|^4/40",
 "full_metric_Gaussian_closure_error_claimed":False,
 "positive_type_Gram_implies_actual_instrument_claimed":False,
 "source_window_conformal":[0,2],
 "source_window_proper_duration":outward(2*A),
 "test_support_conformal":[0.5,1.5],
 "old_short_response_window_or_metric_stability_claimed":False,
 "example_initial_Qsum_relative_to_frozen_Qsum_lower":outward(qratio_lower),
 "Q_spread_cost_claimed_to_be_apparatus_energy":False,
 "new_P2_over_K2_support_for_sigma_at_most_kappaE_over_100":[1.4,1.5],
 "old_probability_in_new_support_log_upper":outward(tail_log),
 "bare_trace_distance_lower":"1-exp(the certified old-support probability log upper)",
 "P_nondemolition_heralding_probability_log_upper":outward(tail_log),
 "same_original_source_realized_by_this_preparation":False,
 "autonomous_energy_conserving_closed_preparation_lowers_total_variance":False,
 "actual_autonomous_preparation_constructed":False,
 "full_geometry_matter_device_CTP_constraint_baseline":"OPEN",
 "metric_or_instrument_signal_claimed":False},
 extra=["../total_source/history_witness.json","../total_source/HISTORY_WITNESS.md",
 "../total_source/INFLUENCE.md","../total_source/PRESSURE_NOISE.md",
 "../total_source/COHERENCE.md","../joint_history/HISTORY.md"])
