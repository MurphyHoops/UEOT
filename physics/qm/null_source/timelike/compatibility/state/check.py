#!/usr/bin/env python3
"""State/geometry compatibility certificates; no new mode ODE is solved.

The exact old modes are defined by the frozen preparation problem; interval
receipts enclose them. Rounded centers are not used as exact quantum states.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
TIMELIKE = HERE.parents[1]
mp.mp.dps = 70
mp.iv.dps = 70
iv = mp.iv
INPUTS = (
    TIMELIKE/"evolution/propagation/result.json",
    TIMELIKE/"evolution/propagation/extra_eta0_256.json",
    TIMELIKE/"evolution/propagation/background.py",
    TIMELIKE/"evolution/propagation/finite_modes.py",
    TIMELIKE/"evolution/propagation/extra_eta0.py",
    TIMELIKE/"instrument/instrument.py",
)


def I(x):
    if hasattr(x,"_mpi_"): return x
    if isinstance(x, float): x=Q.from_float(x)
    else: x=Q(x)
    return iv.mpf(x.numerator)/x.denominator


def lo(x): return mp.make_mpf(x._mpi_[0])
def hi(x): return mp.make_mpf(x._mpi_[1])
def box(a,b): return iv.mpf([I(a).a,I(b).b])
def read_pair(x): return box(Q(x[0]),Q(x[1]))


def rational(x):
    sign,man,exp,_=x._mpf_
    return Q((-1 if sign else 1)*man)*Q(2)**exp


def pair(x): return [str(rational(lo(x))),str(rational(hi(x)))]
def upper_point(x): return I(rational(hi(x)))
def lower_point(x): return I(rational(lo(x)))


def nonnegative(x):
    return box(max(Q(0),rational(lo(x))),max(Q(0),rational(hi(x))))


def source_hashes():
    return {str(p.relative_to(TIMELIKE)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in INPUTS}


def symbolic():
    lam=sp.symbols("lambda",positive=True)
    J=sp.Matrix([[0,1],[-1,0]])
    S=sp.diag(1/lam,lam)
    assert S*J*S.T==J
    phase=sp.symbols("J0",real=True)
    covariance=sp.Matrix([[sp.Rational(1,6)+sp.Rational(3,2)*phase**2,
                          sp.Rational(3,2)*phase],
                         [sp.Rational(3,2)*phase,sp.Rational(3,2)]])
    assert sp.det(covariance)==sp.Rational(1,4)
    assert sp.simplify(sp.det(S*covariance*S.T))==sp.Rational(1,4)
    k=sp.symbols("k",positive=True)
    old=k-sp.Rational(1,2)/k+sp.Rational(3,8)/k**3
    static=k-sp.Rational(1,2)/k-sp.Rational(1,8)/k**3
    assert sp.simplify(k*k*(old-static)-1/(2*k))==0
    c,R,P,Q0=sp.symbols("c R P Q0",real=True,nonzero=True)
    M=27*lam**4-54*lam**2*Q0
    target=1/(2*lam**2*c**3)
    classical=M/(54*lam**6*c**3)
    assert sp.simplify(classical+R/lam**4-target
                       -(R-Q0/c**3)/lam**4)==0
    assert sp.simplify(classical+P/lam**4-target
                       -(P-Q0/c**3)/lam**4)==0
    assert sp.simplify((classical+R/lam**4-target).subs({c:1,R:Q0}))==0
    x,mu4=sp.symbols("x mu4",real=True)
    moments={0:sp.Integer(1),1:sp.Integer(0),2:sp.Rational(3,4),
             3:sp.Integer(0),4:mu4}
    def expectation(poly):
        return sp.expand(sum(coefficient*moments[power[0]]
                             for power,coefficient in sp.Poly(poly,x).terms()))
    y=sp.Rational(1,2)+x
    assert expectation(y*y)==1
    var_y_squared=sp.simplify(expectation(y**4)-expectation(y*y)**2)
    assert var_y_squared==mu4+sp.Rational(3,16)
    assert expectation((x*x-sp.Rational(3,4))**2)==mu4-sp.Rational(9,16)
    assert var_y_squared.subs(mu4,sp.Rational(9,16))==sp.Rational(3,4)
    return {
        "constant_homothety_canonical_map_symplectic":True,
        "zero_mode_full_Cauchy_covariance_determinant":"1/4",
        "zero_mode_scaled_covariance_determinant":"1/4",
        "old_dynamic_to_static_subtraction_difference":"k^2*(d_old-d_static)=1/(2*k)",
        "tuned_source_second_moment":"27*lambda^4-54*lambda^2*Q0",
        "tuned_source_coherent_amplitude_squared":"1-2*Q0/lambda^2",
        "density_defect":"lambda^-4*(R-Q0*c^-3)",
        "pressure_defect":"lambda^-4*(P-Q0*c^-3)",
        "initial_density_constraint_exact":True,
        "relative_component_defect":"2*c^3*abs(Q_component-Q0*c^-3)/lambda^2",
        "symmetric_source_Y_second_moment":"1",
        "symmetric_source_Var_Y_squared":"E[X^4]+3/16",
        "symmetric_source_Var_Y_squared_lower":"3/4",
        "bounded_original_A_candidate_attains_lower":True,
        "smooth_stress_variance_bound":"Var(A) >= (3/4)*A_f^2 for centered reference and A_f!=0",
        "variance_denominator_scope":"classical displacement mean contribution squared; not total mean squared",
        "small_mean_equation_defect_implies_small_stress_noise":False,
    }


def static_seed(last=1024):
    residual=I(Q(1,8))
    for k in range(2,last+1):
        ki=I(k)
        residual += ki*ki*iv.sqrt(ki*ki-1)-ki**3+ki/2+1/(8*ki)
    lower=-I(1)/(32*last*last*(1-I(1)/(last+1)**2))
    upper=-I(1)/(32*(last+1)**2)
    tail=iv.mpf([lower.a,upper.b])
    L=iv.log(I(Q(3,4)))+2*iv.euler
    analytic=(-I(Q(3,160))-L/64)/(9*iv.pi**2)
    rho=(residual+tail)/(36*iv.pi**2)+analytic
    pressure=rho/3+1/(108*iv.pi**2)+1/(864*iv.pi**2)
    assert hi(rho)<0 and lo(pressure)>0
    return rho,pressure,{
        "N":last,"rho":pair(rho),"pressure":pair(pressure),
        "tail_in_residual_sum":pair(tail),"rho_local_addition":pair(analytic),
        "zero_mode_pvar":"3/2",
        "zero_mode_qvar_and_cross":"old Cauchy values; irrelevant to minimal homogeneous stress",
    }


def transplantation_divergence():
    L=iv.log(I(Q(3,4)))+2*iv.euler
    an_old=(58+45*L)/(8640*iv.pi**2)
    an_static=(-I(Q(3,160))-L/64)/(9*iv.pi**2)
    offset=an_static-an_old
    rows=[]
    harmonic=I(0)
    for n in range(1,1025):
        harmonic+=I(1)/n
        if n in (16,64,256,1024):
            mismatch=harmonic/(72*iv.pi**2)
            rows.append({"cutoff":n,"harmonic_term":pair(mismatch),
                         "complete_cutoff_difference":pair(mismatch+offset)})
    return {
        "metrics":"old smooth a^2=3*cos(2eta), and independent smooth static a^2=3",
        "same_induced_metric_and_extrinsic_curvature":True,
        "old_q_at_eta0":"1","new_q_at_eta0":"-1",
        "same_bare_energy_on_initial_surface":True,
        "exact_cutoff_identity":"rho_static,N = rho_old,N + H_N/(72*pi^2) + an_static-an_old",
        "local_finite_offset":pair(offset),
        "divergence_lower_formula":"H_N >= log(N+1); hence +infinity",
        "finite_counterterm_cannot_cancel_log_cutoff":True,
        "not_a_bare_particle_number_argument":True,
        "examples":rows,
    }


def repaired_states(rho_seed,p_seed):
    first=json.loads(INPUTS[0].read_text())
    extra=json.loads(INPUTS[1].read_text())
    assert first["last_nonzero_mode"]==64
    assert extra["first_nonzero_mode"]==65 and extra["last_nonzero_mode"]==256
    for name,digest in first["source_sha256"].items():
        assert hashlib.sha256((TIMELIKE/"evolution/propagation"/name).read_bytes()).hexdigest()==digest
    for name,digest in extra["source_sha256"].items():
        assert hashlib.sha256((TIMELIKE/"evolution/propagation"/name).read_bytes()).hexdigest()==digest
    modes=list(first["targets"]["0"]["modes"])
    all_rows=[]
    pref=1/(36*iv.pi**2)
    for K in (64,256):
        if K==256:modes+=extra["targets"]["0"]["modes"]
        assert [x["k"] for x in modes]==list(range(2,K+1))
        shift=I(0);p_shift=I(0);amplitude_upper=I(0);mode2=None
        for data in modes:
            k=data["k"];omega=iv.sqrt(k*k-1)
            energy=read_pair(data["e"]);pressure=read_pair(data["s"])
            shift+=k*k*pref*(energy-omega)
            p_shift+=k*k*pref*(pressure-omega/3)
            amp=I(Q(2,3))*iv.sqrt(nonnegative(energy*energy-omega*omega))
            amplitude_upper+=k*k*pref*upper_point(amp)
            if k==2: mode2=k*k*pref*amp
        density=rho_seed+shift
        pressure0=p_seed+p_shift
        pressure_center=p_seed+shift/3
        pressure_all=pressure_center+box(-rational(hi(amplitude_upper)),
                                         rational(hi(amplitude_upper)))
        assert lo(pressure_all)<=lo(pressure0)<=hi(pressure0)<=hi(pressure_all)
        assert mode2 is not None and lo(mode2)>0
        assert lo(density)>mp.mpf(".5")
        all_rows.append({
            "preserved_nonzero_modes":[2,K],
            "new_high_frequency_state":"static vacuum for every k>K",
            "zero_mode":"exact old regular Cauchy Gaussian block",
            "Hadamard_reason":"finite rank smooth difference from a new-background Hadamard reference",
            "density_at_all_times":pair(density),
            "pressure_at_eta0":pair(pressure0),
            "pressure_center":pair(pressure_center),
            "pressure_all_times_enclosure":pair(pressure_all),
            "nonzero_frequency_2sqrt3_pressure_amplitude":pair(mode2),
            "static_exact_SCE_with_constant_classical_source_rejected":True,
            "why_rejected":"nonzero unique k=2 pressure frequency; static geometry and local counterterms are constant",
            "initial_quantum_density_exceeds_geometry_required_half":True,
        })
    return all_rows


def compute():
    frozen=source_hashes()
    sy=symbolic()
    rho,p,seed=static_seed()
    result={
        "schema":1,
        "status":"EXACT_STATE_MAP_AND_TRANSPLANT_COUNTEREXAMPLE_WITH_FINITE_RANK_REPAIR",
        "frozen_base":"1a90c68b6178968e6b8239fc97a8b26200f8d59d",
        "source_sha256":frozen,
        "metric_and_field":"4D closed FLRW auxiliary patch; massless minimally coupled real scalar",
        "renormalization":"AE mu1; no extra finite curvature terms for the numeric repair example",
        "symbolic":sy,
        "naive_same_h_K_transplant":transplantation_divergence(),
        "new_static_reference":seed,
        "constructive_Hadamard_repairs":repaired_states(rho,p),
        "logical_boundaries":{
            "full_constant_scaling_Hadamard_transport":True,
            "same_h_K_sufficient_for_arbitrary_future":False,
            "finite_rank_repair_preserves_old_full_kernel":False,
            "fixed_background_state_evolution_constructed":True,
            "small_equation_residual_proves_nearby_exact_metric":False,
            "closed_massless_SCE_local_existence_proved_here":False,
        },
    }
    assert frozen==source_hashes(),"frozen source changed during proof"
    return result


def main():
    if not __debug__:raise RuntimeError("Certificate assertions required; do not use -O")
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument("--write",action="store_true")
    mode.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=compute();path=HERE/"receipt.json"
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    if args.check:assert result==json.loads(path.read_text()),"receipt mismatch"
    print("PASS: exact homothety, same-h/K logarithmic obstruction, legal finite-rank repairs")
    for x in result["constructive_Hadamard_repairs"]:
        print("K",x["preserved_nonzero_modes"][1],
              "rho",[float(Q(y)) for y in x["density_at_all_times"]],
              "p0",[float(Q(y)) for y in x["pressure_at_eta0"]],
              "k2 oscillation lower",float(Q(x["nonzero_frequency_2sqrt3_pressure_amplitude"][0])))


if __name__=="__main__":main()
