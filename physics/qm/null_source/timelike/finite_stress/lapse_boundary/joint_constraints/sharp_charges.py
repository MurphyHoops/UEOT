"""Actual constituent dipole sums, ultraviolet counterexample and energy resource."""
import sympy as sp
from common import iv,require,above,below,outward,finish
r=iv.mpf(1)/5;kappa=1-r;V=2*iv.pi**2;K=256
var=iv.mpf(0);sa=iv.mpf(0);first=iv.mpf(0)
for sig in [-1,1]:
    mu=sig*r
    for k in range(1,K):
        w=iv.sqrt(k*k+mu);v=iv.sqrt((k+1)**2+mu)
        d=-mu/(k*(k+1)+mu+w*v)
        W=iv.mpf(k*(k+1))/(32*w*v)
        term=d*d*W
        var+=term;sa+=term/(w+v)
        if k==1:first+=term
tail=r*r/(192*kappa**3*K**3)
sat=tail/(2*iv.sqrt(kappa)*K)
var_full=iv.mpf([var.a,(var+tail).b]);sa_full=iv.mpf([sa.a,(sa+sat).b])
upper=r*r*(iv.pi**2/3-3)/(64*kappa**3)
require(above(first) and below(var_full,upper.a),'nonzero finite sharp dipole')
require(above(sa_full),'positive inverse-energy resource')
kk,mu=sp.symbols('k mu',positive=True)
dnum=kk*(kk+1)+mu
require(sp.expand(dnum*dnum-(kk*kk+mu)*((kk+1)**2+mu))==-mu,'dipole rationalization')
tel=sp.simplify((kk**-3-(kk+1)**-3)/3-1/(kk**2*(kk+1)**2))
require(sp.simplify(tel-1/(3*kk**3*(kk+1)**3))==0,'sharp cutoff telescoping tail')
rr=sp.symbols('r',positive=True)
pair=sp.simplify(kk**2/(kk**2+rr)+kk**2/(kk**2-rr)-2)
require(sp.simplify(pair-2*rr**2/(kk**4-rr**2))==0,'doublet quadrupole lower')
quad_coeff=4/(27*V)
finish('sharp_charges.py',{
 'r':'1/5','common_constituent_K':K,'included_adjacent_pairs':'k <= K-1',
 'sharp_dipole_variance':outward(var_full),'sharp_dipole_first_shell_lower':outward(first),
 'sharp_dipole_missing_tail_upper':outward(tail),'sharp_dipole_global_upper':outward(upper),
 'inverse_energy_resource_S_A':outward(sa_full),
 'resource_energy_coefficient_1_over_4S':outward(1/(4*sa_full)),
 'quadrupole_variance_lower_per_K_minus_1':outward(quad_coeff),
 'massless_singlefield_quadrupole_exact':'(3K-4)/(27 V0), K>=2',
 'dipole_vacuum_energy_graph_exponents':'0 <= p < 3/2, and not p >= 3/2',
 'generic_spatial_smearing_sharp_stress_variance_finite':False,
 'fixed_classical_geometry_cancels_dipole_quantum_variance':False,
 'new_quantum_geometry_no_go_claimed':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/GROUND_DATUM.md'])
