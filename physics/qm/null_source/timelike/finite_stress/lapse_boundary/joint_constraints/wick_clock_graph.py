"""A specified body-Wick-only clock interaction fails its initial graph test."""
import sympy as sp
from common import iv,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
V=2*iv.pi**2;mu=iv.mpf(1)/5;m=iv.mpf(1)/4;L=iv.mpf(1)/20
bmin=iv.mpf(5)/4*iv.exp(-iv.mpf(2)/3)
require(above(bmin,iv.mpf('.5')),'actual compact profile positive interval')
c=7*m*m*L*L*iv.sin(1)**4/(512*iv.pi**2*iv.exp(1)*V**2*(1+mu)**2)
require(above(c,iv.mpf('6e-11')),'positive four-body norm constant')
r=sp.symbols('r',positive=True)
require(sp.expand((1-r*r/12+r**4/360)-(1-sp.Rational(29,360)*r*r)-r*r*(r*r-1)/360)==0,'rho cosine upper bound on r<=1')
require(sp.Rational(1,1)-sp.Rational(29,360)/4==sp.Rational(1411,1440),'rho gap')
pref=sp.Rational(3,2)*sp.Rational(1,2)*sp.Rational(14,3)/4**4
require(pref==sp.Rational(7,512),'annulus Wick norm prefactor')
finish('wick_clock_graph.py',{
 'fixed_nonzero_coupling':True,'initial_clock_body_product_Gaussian':True,
 'body_mass_square':'1/5','positive_switch_interval':['-1/40','1/40'],
 'switch_square_lower':'1/4','profile_b_lower':outward(bmin),
 'limiting_clock_annulus_correlation_range':['11/12','1411/1440'],
 'eventual_clock_correlation_gap':'29/2880',
 'four_body_initial_image_norm_squared_lower':'c_star g^2 K^3',
 'c_star_lower':outward(c),
 'finite_K_onset_quantified':False,'uniform_small_g_onset_claimed':False,
 'low_body_degree_subtractions_cancel_four_sector':False,
 'specified_initial_Hamiltonian_graph_sequence':'REJECTED',
 'all_correlated_recovery_sequences_excluded':False,
 'strong_resolvent_limit_excluded':False,
 'all_renormalized_clock_composites_excluded':False,
 'SI_calibration':False
},inputs=[p+'CLOCK_UV.md',p+'clock_uv.json',p+'CLOCK_ACTUATOR.md',
p+'LOCAL_PREPARATION.md'])
