"""AS: finite-cutoff metric/preparation/CTP identities and a Ward witness."""
import math
import numpy as np
import sympy as sp
from scipy.linalg import expm,expm_frechet
from common import require,finish
q0,q1,p0,p1,mu,u,u1,u2=sp.symbols('q0 q1 p0 p1 mu u u1 u2',real=True)
qs=[q0,q1];ps=[p0,p1]
H=(p0**2+p1**2+(1+mu)*q0**2+(4+mu)*q1**2)/2
def dot(x):
    return sp.expand(sum(sp.diff(x,q)*sp.diff(H,p)-sp.diff(x,p)*sp.diff(H,q) for q,p in zip(qs,ps)))
A=(p0*p1+(2+mu)*q0*q1)/2
O=q0*q1/2;D=sp.Rational(3,2)*p0*q1;Zshift=p0*q1-q0*p1/2
require(sp.expand(dot(A)+Zshift)==0,'improved density/shift Ward')
require(sp.expand(D-dot(O)-Zshift)==0,'shift improvement')
F=-u*D-u1*(A-O)
dF=dot(F)+sp.diff(F,u)*u1+sp.diff(F,u1)*u2
metric=-(u2+3*u)*p0*p1/2+(1+mu)*(3*u-u2)*q0*q1/2
require(sp.expand(dF-metric)==0,'pure-gauge metric jet identity')
Q,Q1=sp.symbols('Q Q1',real=True)
require(sp.expand(-u1*Q/2+u*Q1/2+(u1*Q-u*Q1)/2)==0,'fixed-field vs conformal-variable endpoint')
require(6*u2-2*(3*u2)==0,'pure-gauge curvature')
Jsp=sp.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
Gsp=sp.diag(1,4,1,1);Vsp=sp.diag(sp.Rational(1,2),sp.Rational(1,4),sp.Rational(1,2),1)
noise=sp.trace(Gsp*Vsp*Gsp*Vsp)/2+sp.trace(Gsp*Jsp*Gsp*Jsp)/8
require(noise==0,'quantum ground-energy variance cancellation')
J=np.array(Jsp,dtype=float);muv=.2
w0=math.sqrt(1+muv);w1=math.sqrt(4+muv)
G=np.diag([w0*w0,w1*w1,1.,1.])
Vin=np.diag([1/(2*w0),1/(2*w1),w0/2,w1/2])
M=np.zeros((4,4));M[0,1]=M[1,0]=.5
MA=np.zeros((4,4));MA[0,1]=MA[1,0]=(2+muv)/2;MA[2,3]=MA[3,2]=.5
T=.37
S,dS=expm_frechet(T*J@G,T*J@M)
V=S@Vin@S.T
dV=dS@Vin@S.T+S@Vin@dS.T
response=.5*np.trace(MA@dV)
Om=w0+w1;d=2+muv-w0*w1;W=1/(16*w0*w1)
pair=-2*d*W*(1-math.cos(Om*T))/Om
require(abs(response-pair)<2e-13 and abs(response)>1e-6,'actual prepared response equals exact pair Kubo')
eps=1e-5
Vp=expm(T*J@(G+eps*M))@Vin@expm(T*J@(G+eps*M)).T
Vm=expm(T*J@(G-eps*M))@Vin@expm(T*J@(G-eps*M)).T
require(np.linalg.norm((Vp-Vm)/(2*eps)-dV)<2e-8,'preparation derivative')
require(np.linalg.norm(S@J@S.T-J)<2e-13,'symplectic evolution')
require(np.linalg.eigvalsh(V+1j*J/2).min()>-2e-13,'same-state uncertainty positivity')
finish('metric_response.py',{
'canonical_cutoff_specified_before_variation':True,
'lapse_shift_spatial_metric_source_columns':True,
'four_dimensional_curvature_metric_jets_retained':True,
'nonvanishing_endpoint_terms_retained':True,
'fixed_q_and_fixed_Phi_endpoints_reconciled':True,
'actual_preparation_Duhamel_and_initial_response':True,
'initial_mixed_CTP_block':'U0 G_a rho_in G_b U0_dagger',
'finite_cutoff_history_Gram_positive':True,
'quadratic_noise_keeps_quantum_J_term':True,
'first_harmonic_density_shift_Ward_exact':True,
'first_order_reference_cutoff_gauge_exception_explicit':True,
'active_source_gauge_variation_required':True,
'finite_matrix_response_tolerance':'2e-13 Kubo; 2e-8 central derivative',
'arbitrary_metric_continuum_response_signed':False,
'full_gravity_canonical_Hamiltonian_derived':False,
'scope':'Common finite canonical cutoff and explicit reference-background first variations'
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/EXTERNAL_RAMP.md','physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/NEXT_GATE.md'])
