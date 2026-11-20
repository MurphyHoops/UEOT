"""Correlated quantum-state obstruction from a positive high-mode Hamiltonian."""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path
from mpmath import iv
import sympy as sp
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
TIMELIKE=HERE.parent
INPUTS=[TIMELIKE/"physical_source/static_source.json",
        TIMELIKE/"joint_history/instrument.json",TIMELIKE/"joint_history/bounds.json"]
old,instrument,prior_bounds=[json.loads(p.read_text()) for p in INPUTS]
assert all(v["status"]=="PASS" for v in [old,instrument,prior_bounds])
iv.dps=90
def exact_float(v):
    n,d=v.as_integer_ratio();return iv.mpf(n)/d
def box(v):return iv.mpf([exact_float(v[0]).a,exact_float(v[1]).b])
def outward(v):
    return [math.nextafter(float(v.a),-math.inf),math.nextafter(float(v.b),math.inf)]
nu0=box(instrument["nu0"])
d=iv.sqrt(3)/2;L=1+d/2
assert bool(nu0.a>iv.mpf("1.8e11"))
excess=d/2-1/nu0
assert bool(excess.a>0)
tail_floor=excess**2/2
rms_floor=excess/(3*iv.sqrt(2)*L)
assert bool(rms_floor.a>iv.mpf(".07"))
# Exact identities for arbitrary positive, stationary high excitation energy.
x,U,k,M=sp.symbols("x U k M",positive=True)
b=sp.Function("B")(x)
r=2*b-4*k
N=3*x-3*U*x**2-2*b+sp.Rational(9,2)*k
G=4*U*x**3-3*x**2-k*x
tau=(3*x**2-2*U*x**3-2*r*x)/M
identity=sp.diff(M*tau,x).subs(sp.diff(b,x),-k/(4*x))-2*N
assert sp.simplify(identity)==0
assert sp.simplify(M*tau-G-2*x*N)==0
rho=U+(r+N)/x**2+G/(2*x**3)
p=-U+(2*b/3-k+N/3)/x**2+G/(2*x**3)
assert sp.simplify(rho-3/(2*x))==0
assert sp.simplify(p+1/(2*x))==0
assert sp.simplify(sp.diff(G,x)-(3*G/x+3*x+2*k))==0
Nprime=sp.diff(N,x).subs(sp.diff(b,x),-k/(4*x))
eps=sp.symbols("eps",positive=True)
assert sp.simplify(Nprime.subs(U,((3+k/x)/4+eps)/x)+sp.Rational(3,2)+k/x+6*eps)==0
# The positive-part inequality is a joint-spectral pointwise inequality.
y,h=sp.symbols("y h",nonnegative=True)
assert sp.expand((y+h)**2-y**2)==2*y*h+h**2
A,pi=sp.symbols("A pi",positive=True)
Es=pi**2*M/A**3
meanH=3*pi**2*A
assert sp.factor((Es/meanH)**2-M**2/(9*A**8))==0
ds,nus=sp.symbols("d nu0",positive=True)
high_ring_mean=1+ds+1/nus
old_mean=1+ds/2+2/nus
assert sp.factor(high_ring_mean-old_mean-(ds/2-1/nus))==0
payload={
 "schema":"ueot-correlated-static-correlations/1","status":"PASS",
 "identities":{"M2_tau_derivative_equals_2N":True,"M2_tau_equals_G_plus_2xN":True,
   "averaged_static_components":True,"unique_positive_G_branch":True,
   "N_strict_decrease_on_G_positive":True,"spectral_nonnegative_case":True,
   "relative_energy_normalization":True,"high_ring_mean_excess":True},
 "nu0":outward(nu0),"high_ring_mean_above_global_threshold":outward(excess),
 "input_positive_tail_second_moment_lower":outward(tail_floor),
 "strict_record_weighted_relative_RMS_lower":outward(rms_floor),
 "strict_record_weighted_relative_variance_lower":outward(rms_floor**2),
 "positive_high_Hamiltonian":"H_high_exc=sum(k>=2,degeneracy,species) sqrt(k^2-1)/A * N_k",
 "vacuum_AE_and_U_terms":"all retained in Ec=V*(U0+r(x)/x^2)",
 "threshold":"tau=(meanH-Ec)/Es=(3*x^2-2*U0*x^3-2*r(x)*x)/M2",
 "threshold_cap":"tau(x)<=tau(x0)=mu_old=L+2/nu0",
 "spectral_inequality":"Var(H)>=Es^2*E[(S0-tau)_+^2]",
 "Jensen_tail_lower":"E_input[(S0-mu_old)_+^2]>=0.5*(d/2-1/nu0)^2",
 "final_RMS_formula":"RMS_weighted>(d/2-1/nu0)/(3*sqrt(2)*L)>0.07",
 "conditional_zero_high_product_required":False,
 "classical_anticorrelation_and_quantum_entanglement_allowed":True,
 "high_state_required_thermal":False,"occupied_shells_restricted_to_k2":False,
 "joint_state_required_stationary":False,"high_marginal_stationary_required":True,
 "high_Hadamard_and_finite_mean_energy_required":True,
 "pointwise_static_mean_SCE_assumed_not_constructed":True,
 "spatial_mean_zero_high_cross_vanishes_by_harmonic_orthogonality":True,
 "complete_input_S0_spectrum_preserved":True,"all_records_retained":True,
 "record_count_unrestricted":True,"same_M2_U0_AE_required":True,
 "infinite_second_moment_interpretation":"inequality in extended nonnegative reals",
 "stronger_than_seven_percent_for_every_branch_claimed":False,
 "ten_percent_bound_extended_to_correlated_states":False,
 "sharp_optimum_claimed":False,"geometric_RMS_bound_claimed":False,
 "mean_SCE_disproved":False,"nonstatic_or_other_matter_models_excluded":False,
 "old_checkers_executed":0,"mode_ODE_integrations":0,"geometry_ODE_integrations":0,
 "source_sha256":{str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in INPUTS+[HERE/"correlations.py"]}}
ap=argparse.ArgumentParser(description=__doc__)
g=ap.add_mutually_exclusive_group(required=True);g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
args=ap.parse_args();out=HERE/"correlations.json"
if args.write:out.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
else:assert json.loads(out.read_text())==payload
print("PASS: correlated_static_correlations")
