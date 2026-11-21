"""Same-H full-field autonomous source-sign record: exact and interval checks."""
import sympy as s
from common import finish,require,iv,outward,above,below,load,box
zdata=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/quantum_controller.json')
xx=s.symbols('xx',real=True)
env=s.sqrt(630)*xx**2*(1-xx)**2
require(s.integrate(env**2,(xx,0,1))==1,'normal input')
require(s.integrate(s.diff(env,xx)**2,(xx,0,1))==12,'exact controller kinetic integral')
for end in (0,1):
 require(env.subs(xx,end)==s.diff(env,xx).subs(xx,end)==0,'H2 zero boundary traces')
central=s.integrate(env**2,(xx,s.Rational(1,4),s.Rational(3,4)))
require(central==s.Rational(59123,65536),'exact central preparation mass')
yy=s.symbols('yy',positive=True)
require(s.simplify(s.diff(yy**2*s.exp(-yy),yy)-yy*(2-yy)*s.exp(-yy))==0,'bump derivative monotonic factor')
# Independent spectral translation gives the double anticommutator:
# [Z,[Z,sin(sP)]]=-d_P^2 sin(sP)=s^2 sin(sP).
ss,pp=s.symbols('ss pp',real=True)
require(s.simplify(-s.diff(s.sin(ss*pp),pp,2)-ss**2*s.sin(ss*pp))==0,'nested commutator sign')
qs,qp,ps,ppr,rr,ll=s.symbols('qs qp ps ppr rr ll',real=True)
hlow=(ps**2+ppr**2+qs**2+qp**2+2*rr*qs*qp)/2
require(s.expand(hlow-(ps**2+ppr**2+(qp+rr*qs)**2+(1-rr**2)*qs**2)/2)==0,'low-mode positive form')
require(s.expand(hlow.subs(qp,qp+ll)-hlow-ll*(qp+rr*qs)-ll**2/2)==0,'actual momentum-reader interaction backaction')
rs=iv.mpf('.2');R1=16*rs;sig=iv.mpf('.1');tt=iv.mpf('.0004')
eabs=box(zdata['vacuum_potential_absolute_bound'])
mass=iv.mpf(59123)/65536
rlo=rs*iv.exp(-iv.mpf(4)/3)*mass
connection=R1**2*iv.pi**2/(192*(1-rs)**2)
require(below(abs(connection-iv.pi**2/12),'1e-95'),'independent connection coefficient')
Ebar=6+iv.mpf('.5')+rs**2/8+connection
Eplus=Ebar+eabs+1
Cs=iv.sqrt(2*(1+rs**2)*Eplus)+(2*R1/iv.sqrt(1-rs**2)+2)*Eplus+iv.mpf('.25')
gain=iv.exp(-sig**2/2)*(iv.exp(-iv.mpf('.25'))*rlo*tt-Cs*tt**2/2)
require(above(gain,'8e-6'),'strict actual bounded record contrast')
finish('autonomous_record.py',{
 'same_autonomous_H_as_Z':True,'preparation_changed_to_active_region':True,
 'high_tail_controller_correlations_retained':True,
 'input_source_variable':'k=1 source quadrature sign; coherent means +/-1',
 'total_H_spectral_laws_of_two_inputs':'identical by joint low-mode parity',
 'geometric_or_total_energy_charge_discrimination':False,
 'central_preparation_mass_exact':'59123/65536',
 'rprime_uniform_bound':outward(R1),
 'r_eff_lower_bound':outward(rlo)[0],
 'controller_vacuum_connection_energy_upper_bound':outward(connection)[1],
 'actual_input_total_mean_energy_upper_bound':outward(Ebar)[1],
 'actual_second_weak_derivative_absolute_bound':outward(Cs)[1],
 'initial_binary_probabilities':[.5,.5],
 'actual_readout_ESU_model_time':'.0004',
 'terminal_momentum_reader_sigma':'.1',
 'actual_binary_probability_contrast_lower_bound':outward(gain)[0],
 'strict_record_bound_interval':outward(gain),
 'reader_total_mean_energy_increment_exact':'12.5',
 'reader_output_total_mean_energy_upper_bound':outward(Ebar+iv.mpf('12.5'))[1],
 'outside_packet_pulse_tracking_proved':False,
 'finite_cutoff_uniform_form_Taylor_and_actual_limit_proved_analytically':True,
 'autonomous_preparation_or_terminal_reader_constructed':False,
 'source_code_states_orthogonal':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/QUANTUM_CONTROLLER.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/quantum_controller.json'])
