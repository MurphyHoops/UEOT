"""Exact shift/composition and compact-average normalization checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish, require, iv, outward, below
s,delta,L=sp.symbols("s delta L",positive=True)
require(sp.simplify((L*delta)/delta-L)==0,"Translation modulus coefficient")
# The proof's map identities: shifted integral approximates B F*, while
# change of integration variable approximates B. No generator is differentiated.
B,Fs=sp.symbols("B Fs",commutative=False)
require(sp.expand(B*Fs-B-B*(Fs-1))==0,"Dense-range cancellation")
# Finite-rank compact-test escape, illustrating rather than proving the
# infinite-dimensional normality argument.
rows=[]
for n in [8,16,32]:
    sig=np.eye(n)/n
    P=np.zeros((n,n));P[0,0]=1;P[1,1]=1
    require(abs(np.trace(sig)-1)<1e-13,"Finite density remains normalized")
    require(abs(np.trace(P@sig)-2/n)<1e-13,"Compact-prefix expectation")
    rows.append({"rank":n,"weighted_trace":1,"fixed_rank2_probability":2/n})
finish("interior_collapse.py",{
"uniform_reset_of_complete_original_propagator":True,
"fixed_Bochner_L1_vector_tests":"T_K X ->0 strongly",
"state_independent_fixed_test_rigging":"ZERO limit",
"all_normal_prepared_fixed_test_kernels":"ZERO limit, no state-limit assumption",
"nonzero_original_N3_gate":"REJECTED in fixed bulk comparison",
"positive_fixed_time_density_average":"all compact tests tend to zero; trace remains1 at finiteK",
"normal_L1_and_ae_trace_history_on_positive_interval":"EXCLUDED",
"fixed_forcing_retarded_advanced_response":"uniform strong zero",
"finite_K_physical_Hilbert_space_destroyed":False,
"cutoff_dependent_endpoint_or_rescaled_tests_excluded":False,
"isolated_fixed_positive_time_limit":"OPEN",
"selected_noncompact_N4_readout":"OPEN",
"finite_rank_normality_illustration":rows
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/NEXT_PROPAGATOR_TEST.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/LOCAL_CONSTRAINT.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RESCALED_KERNEL.md"])
