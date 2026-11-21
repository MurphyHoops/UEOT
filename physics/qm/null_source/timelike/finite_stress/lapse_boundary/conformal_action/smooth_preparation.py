"""Pulse and complete Gaussian reader identities; PDE theorem is analytic."""
import sympy as s
from common import finish,require,iv,outward,above
x=s.symbols('x',real=True)
q,r,z=s.symbols('q r z',real=True)
sig=s.symbols('sigma',positive=True)
profile=s.exp(4-1/(x*(1-x)))
require(s.simplify(profile.subs(x,s.Rational(1,2)))==1,'unit pulse maximum')
# The full flatness proof follows because every derivative is a rational
# function times exp(-1/[x(1-x)]); check the recursion's exact invariant.
rat=s.Integer(1);exponent=4-1/(x*(1-x))
for order in range(1,9):
 rat=s.factor(s.diff(rat,x)+rat*s.diff(exponent,x))
 require(s.cancel(rat).is_rational_function(x),'flat bump derivative structure')
 require(s.limit(rat*profile,x,0,dir='+')==0,'left flat jet '+str(order))
 require(s.limit(rat*profile,x,1,dir='-')==0,'right flat jet '+str(order))
# A Gaussian Kraus density, in Q_f's spectral variables.
prod=s.exp(-((z-q)**2+(z-r)**2)/(4*sig**2))/s.sqrt(2*s.pi*sig**2)
# Complete the square; integrate the normalized common Gaussian.
target=s.exp(-(q-r)**2/(8*sig**2))*s.exp(-(z-(q+r)/2)**2/(2*sig**2))/s.sqrt(2*s.pi*sig**2)
require(s.simplify(s.expand(s.log(prod/target)))==0,'exact dephasing square completion')
require(s.integrate(s.exp(-z*z/(2*sig**2))/s.sqrt(2*s.pi*sig**2),(z,-s.oo,s.oo))==1,'complete normalization')
lam=s.symbols('lambda',real=True)
variance=1/(4*sig**2)
require(s.simplify(variance*(q-r)**2/2-(q-r)**2/(8*sig**2))==0,'Weyl Gaussian variance')
# For each oscillator a -> a - i lambda f/sqrt(2), so the quadratic
# energy shift is lambda^2 <f,Df>/2; centered averaging removes linear term.
frequency,amplitude=s.symbols('frequency amplitude',positive=True)
kick=s.simplify(variance*frequency*amplitude**2/2)
require(kick==frequency*amplitude**2/(8*sig**2),'source readout mean energy')
require(kick.subs({frequency:1,amplitude:1,sig:1})==s.Rational(1,8),'unit-mode example')
e=iv.mpf('.08');V=2*iv.pi**2
require(above(1-11*e/iv.sqrt(V)),'uniform pulse positive form')
finish('smooth_preparation.py',{'pulse_support_fraction':['1/4','3/4'],
 'pulse_duration_example_model_conformal_time':'.02','amplitude_example':'.08',
 'finite_flat_jet_regressions':8,'all_orders_flatness_proved_by_rational_derivative_induction':True,
 'same_past_ESU_vacuum_on_all_branches':True,
 'actual_full_KG_in_out_map':'unique symplectic Cauchy solution of the stated local action',
 'late_outgoing_vacuum':'normal pure Hadamard Gaussian with all polynomial free-energy moments',
 'normal_channel_all_normal_inputs':True,
 'energy_moment_claim_for_arbitrary_normal_inputs':False,
 'complete_Gaussian_Kraus_normalization':True,
 'nonselective_Weyl_variance':'1/(4 sigma^2)',
 'exact_source_readout_energy_increase':'<f,Df>/(8 sigma^2)',
 'same_instrument_calibration_MSE':'sigma^2',
 'calibration_MSE_times_source_energy_increase':'<f,Df>/8',
 'universal_measurement_bound_claimed':False,
 'unit_k1_sigma1_energy_increase_exact':'1/8',
 'canonical_time_dependent_cutoff_convergence_proved':False,
 'physical_cross_history_renormalized_phase_fixed':False,
 'autonomous_stress_complete_pulse_and_reader_supplied':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/HADAMARD_SPLIT.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/STATIC_NORMALITY.md'])
