"""Same operational source, actual residual bound, and normal incoming-energy comparator."""
import sympy as s
from common import iv,load,box,above,below,outward,require,finish
A,h,hp,I,Q,D,P,t=s.symbols("A h hp I Q D P t",real=True,nonzero=True)
aQ=-A*A*hp/2;aD=h-A*A*hp*I;aP=s.Rational(1,2)/A**2+h*I-A*A*hp*I**2/2
base=aQ*Q+aD*D+aP*P
flow=aQ*(Q+2*t*D/A**2+t*t*P/A**4)+aD*(D+t*P/A**2)+aP*P
linear=-hp*D+(h/A**2-hp*I)*P
quad=-hp*P/(2*A*A)
require(s.simplify(flow-base-t*linear-t*t*quad)==0,"Exact current zero source flow")
Ez,delta=s.symbols("Ez delta",positive=True)
meanR=-A*hp*Ez/(4*delta**2)
mu=A*hp*Ez/(4*h*delta**2)
require(s.simplify(h*mu+meanR)==0,"Pointer mean shift retained")
vB=s.symbols("vB",positive=True)
varP=(delta*delta+vB)/(h*h);cov=-vB/h
require(s.simplify(h*h*varP+2*h*cov+vB-delta*delta)==0,"B-record full covariance")
z,b,c=s.symbols("z b c",real=True)
require(s.expand((z-b)**2+(z-c)**2-2*(z-(b+c)/2)**2-(b-c)**2/2)==0,"CP Gaussian nonselective kernel")
inputs=["joint_history/history.json","finite_stress/boundary_state.json",
 "finite_stress/lapse_boundary/OPERATIONAL_STATE.md",
 "finite_stress/lapse_boundary/READOUT_WITNESS.md",
 "finite_stress/lapse_boundary/CANONICAL_PREPARATION.md",
 "finite_stress/lapse_boundary/ACTION_LIFT.md",
 "finite_stress/lapse_boundary/PREPARED_MEAN.md","constraint_states/RELATIONAL.md"]
AA=box(load(inputs[0])["cases"]["unfiltered"]["A"])
source=load(inputs[1]);sig=box(source["example_sigma"]);ee=box(source["mean_unfiltered_zero_energy"])
dd=iv.mpf("1e-6");eps=iv.exp(-1158)
budget=iv.exp(60)+iv.exp(36)/(2*dd)+iv.sqrt(3)*iv.exp(28)/(4*dd*dd)
require(below(iv.ln(budget),61),"Actual residual norm exponent")
require(below(eps*eps*budget*budget,dd*dd*((iv.mpf("1.000001"))**2-1)),"Strict tolerance upper including residual")
R1=iv.mpf("1e15")+iv.mpf("1e22")/(iv.mpf("8e4")**2)+iv.mpf("1e-14")*iv.mpf("1e22")
R2=iv.mpf("1e22")/(2*iv.mpf("8e4")**2)
require(below(iv.ln(R1),36) and below(iv.ln(R2),28),"Same radial source norms")
extraQ=ee/(4*AA*dd*dd)
require(above(extraQ,"2e12"),"Finite large zero-coordinate cost")
Fupper=2*iv.sqrt(8*iv.pi)*dd/(AA*sig)
require(below(Fupper,".001"),"Complete bare support leakage")
require(above(AA*sig/iv.sqrt(128),".001"),"Geometry momentum resource lower")
finish("incoming_preparation.py",dict(
 controlled_generator="B=A*delta(H_in), not H_i",
 normal_positive_joint_toy_state_constructed=True,
 complete_declared_source_AP_restriction_preserved_nonselectively=True,
 operational_quotient_principle_reused=True,
 normal_Gaussian_encoding_principle_reused=True,
 same_source_mean_RSET_functional_and_stress_moments_preserved=True,
 source_Hadamard_preserved=True,
 source_B_spectral_law_preserved=True,
 source_H_i_spectral_law_preserved=False,
 target_constraint_H_i_not_redefined=True,
 exact_pointer_initial_mean="A*h_i_prime*E_z/(4*h_i*delta0^2)",
 centered_pointer_residual_symmetric_cross_zero=True,
 delta0="1e-6", actual_constraint_RMS_bounds=["1e-6","1.000001e-6"],
 residual_norm_log_upper=outward(iv.ln(budget)-1158),
 added_zero_Q_variance_per_species=outward(extraQ),
 complete_bare_trace_distance_strict_lower=.999,
 support_overlap_upper=outward(Fupper),
 geometry_momentum_RMS_floor="1e-3/h_i",
 exact_normal_zero_constraint_limit_claimed=False,
 free_pointer_P_identified_with_original_P_u=False,
 geometry_joint_mean_follows_quiet_history_proved=False,
 original_action_autonomous_constraint_conserving_gate_proved=False,
 calibrated_gravity_instrument_constructed=False),
 inputs,proof="INCOMING_PREPARATION.md")
