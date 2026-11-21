"""Uniform all-energy clock admission and exact scaling/canonical checks."""
import sympy as s
from common import finish,require,iv,outward,above,below
from model import HISTORY,parameters
A,U=parameters();V=2*iv.pi**2;ac=iv.mpf(1)/240;m=3*V/2
astar=A*iv.exp(iv.mpf('.55'));d=iv.mpf('.01');N0=iv.mpf(1)
rmax=N0*iv.exp(4*d)/astar**4
dis=m*m-4*ac*(V*U+iv.mpf([0,rmax.b]))
require(above(dis),'all-energy clock discriminant')
y=2*(V*U+iv.mpf([0,rmax.b]))/(m+iv.sqrt(dis))
ay=astar**2*iv.exp(iv.mpf([(-2*d).a,(2*d).b]))*y
require(above(ay,iv.mpf('1.81')),'all-energy expanding margin')
# Bounds after factoring w=(1+N)^1/4; 1/w² lies in [0,1].
kfactor=iv.sqrt(ay-iv.mpf([0,1]))
afactor=astar**2*iv.exp(iv.mpf([(-2*d).a,(2*d).b]))
hfactor=kfactor*(afactor*(2*m-4*ac*y/3)-iv.mpf([0,(8*ac/3).b]))
require(above(hfactor),'positive all-energy generator')
# Symbolic screened branch: derivative y_r and clock r_tau.
r,mm,aa,VV,UU=s.symbols('r m ac V U',positive=True)
yy=2*(VV*UU+r)/(mm+s.sqrt(mm*mm-4*aa*(VV*UU+r)))
require(s.simplify(aa*yy*yy-mm*yy+VV*UU+r)==0,'screened lower root')
require(s.simplify(s.diff(yy,r)-1/s.sqrt(mm*mm-4*aa*(VV*UU+r)))==0,'screened root derivative')
# Canonical generating-function algebra for general f(N).
N,P=s.symbols('N P');ff=s.Function('f')(N)
# d(P N f') coefficients match the flow correction plus clock shift.
F=P*N*s.diff(ff,N)
require(s.diff(F,P)==N*s.diff(ff,N),'endpoint dP')
require(s.simplify(s.diff(F,N)-P*(s.diff(ff,N)+N*s.diff(ff,N,2)))==0,'endpoint dN')
finish('energy_clock.py',{'clock':'tau=u-.55-(1/4)log(1+N_q)',
 'tau_window':[-.01,.01],'N0':1,'full_source_Fock_energy_range':'[0,infinity)',
 'r_max_bounds':outward(rmax),'discriminant_bounds':outward(dis),
 'kappa_divided_by_1plusN_quarter_bounds':outward(kfactor),
 'h_divided_by_1plusN_three_quarters_bounds':outward(hfactor),
 'common_generator_domain':'D((1+N_q)^(3/4))',
 'raw_R_domain':'D((1+N_q)^(1/8))','raw_R_inverse_bounded':True,
 'all_normal_physical_Fock_states':True,
 'controlled_translation_L2_unitary':True,'controlled_translation_general_L1_bounded':False,
 'naive_equal_tau_local_KG_identification':'EXCLUDED by high-frequency scaling',
 'clock_autonomously_realized':False,
 'old_minimal_operator_kernel_repaired':False},
 inputs=[HISTORY])
