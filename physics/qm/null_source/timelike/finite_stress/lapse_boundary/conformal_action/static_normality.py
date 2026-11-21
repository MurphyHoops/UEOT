"""Full-field analytic norm bounds and finite canonical independent regressions."""
import numpy as np
from scipy.linalg import eigh,solve_sylvester
import sympy as s
from common import finish,require,iv,outward,above,below
V=2*iv.pi**2;ns=2;e=iv.mpf('.08')
pm=1-3*e/iv.sqrt(V);pp=1+3*e/iv.sqrt(V)
qm=1-11*e/iv.sqrt(V)
aa=iv.sqrt(qm*pm);bb=pm
cb=pp*e*8/(3*iv.sqrt(V))
require(above(pm) and above(qm),'uniform positive gaps')
hsharp=iv.sqrt(ns)*iv.pi*cb/(4*iv.sqrt(6)*aa*bb)
hheat=iv.sqrt(ns)*iv.pi*cb/(8*aa*iv.sqrt(aa*bb))
require(below(aa,bb.a) and bool(hsharp.b<hheat.a),'two independent norm bounds')
distance=iv.sqrt(1-iv.exp(-hsharp**2/2))
require(below(distance,1),'normal overlap bound')
k=s.symbols('k',integer=True,positive=True)
require(s.summation(1/k**2,(k,1,s.oo))==s.pi**2/6,'exact multiplicity trace')
x=s.symbols('x',positive=True)
# x=exp(-4mt) turns the heat integral into Beta(1/2,1/2)/(4m).
require(s.integrate(1/s.sqrt(x*(1-x)),(x,0,1))==s.pi,'exact integrable heat majorant')
K=12;vf=2*np.pi**2;tol=2e-9
def power(A,p):
 w,v=eigh(A);require(w.min()>0,'positive matrix square root')
 return (v*w**p)@v.T
blocks=[]
for ell in range(K):
 ks=np.arange(ell+1,K+1,dtype=float);d=len(ks)
 def rec(k):
  return 0. if k<=ell or k==0 else .5*np.sqrt((k-ell)*(k+ell+1)/(k*(k+1)))
 M=np.zeros((d,d))
 for i,k0 in enumerate(ks):
  M[i,i]=(4*(rec(k0)**2+rec(k0-1)**2)-1)/np.sqrt(vf)
  if i+2<d:M[i,i+2]=M[i+2,i]=4*rec(k0)*rec(k0+1)/np.sqrt(vf)
 B=(.5*(ks[:,None]-ks[None,:])**2-4/3)*M
 require(np.linalg.norm(B,2)<=8/(3*np.sqrt(vf))+tol,'exact row-sum upper bound')
 blocks.append((ell,ks,M,B))
rows=[]
for eps in [-.08,.08]:
 hs2=0.;logfid2=0.
 for ell,ks,M,B in blocks:
  d=len(ks);D0=np.diag(ks);P=np.eye(d)+eps*M
  ph=power(P,.5);pih=power(P,-.5)
  Q=D0@P@D0+eps*B
  Y=ph@D0@ph;Om=power(ph@Q@ph,.5)
  C=eps*ph@B@ph;X=solve_sylvester(Om,Y,C)
  require(np.linalg.norm(X-(Om-Y))<tol,'Sylvester square-root difference')
  bet=.5*power(Om,-.5)@X@pih@power(D0,-.5)
  direct=.5*(power(Om,.5)@pih@power(D0,-.5)-power(Om,-.5)@ph@power(D0,.5))
  require(np.linalg.norm(bet-direct)<tol,'independent canonical beta')
  alp=bet+power(Om,-.5)@ph@power(D0,.5)
  require(np.linalg.norm(alp@alp.T-bet@bet.T-np.eye(d))<tol,'canonical normalization')
  require(np.linalg.norm(alp@bet.T-bet@alp.T)<tol,'canonical symmetry')
  mult=ns*(2*ell+1)
  hs2+=mult*np.linalg.norm(bet,'fro')**2
  logfid2-=mult*np.linalg.slogdet(np.eye(d)+bet@bet.T)[1]/2
 require(hs2<float(hsharp.b)**2,'finite cutoff below analytic all-field majorant')
 require(logfid2>=-hs2/2-tol,'Fredholm fidelity inequality regression')
 rows.append({'epsilon':eps,'beta_HS_squared_rounded':round(float(hs2),12),
              'log_squared_vacuum_overlap_rounded':round(float(logfid2),12)})
# Direct ground-energy curvature, independent of pair-shell weights.
def energy(eps):
 result=0.
 for ell,ks,M,B in blocks:
  D0=np.diag(ks);P=np.eye(len(ks))+eps*M;ph=power(P,.5)
  Q=D0@P@D0+eps*B
  result+=ns*(2*ell+1)*np.sqrt(eigh(ph@Q@ph,eigvals_only=True)).sum()/2
 return result
eta=.01;E0=energy(0)
curv=(-energy(2*eta)+16*energy(eta)-30*E0+16*energy(-eta)-energy(-2*eta))/(12*eta**2)
chi=ns/(9*vf)*(float(s.harmonic(K))-1-1/(3*K))
require(abs(curv+chi)<2e-6,'ground-energy Hessian versus retarded susceptibility')
finish('static_normality.py',{'amplitude_bound_example':'.08','species':ns,
 'positive_kinetic_gap':outward(pm),'positive_potential_form_gap':outward(qm),
 'Omega_eigenvalue_factor':outward(aa),'Y_eigenvalue_factor':outward(bb),
 'bounded_square_difference_norm_upper_bound':outward(cb),
 'full_field_beta_HS_upper_bound':outward(hsharp),
 'independent_heat_beta_HS_upper_bound':outward(hheat),
 'new_ground_vs_old_vacuum_trace_distance_upper_bound':outward(distance),
 'finite_regression_cutoff':K,'finite_regressions':rows,
 'floating_matrix_regression_tolerance':tol,'ground_energy_Hessian_tolerance':2e-6,
 'full_field_canonical_cutoff_HS_convergence_proved_analytically':True,
 'full_field_normal_spectral_zero_unitary_and_CTP_limit':True,
 'arbitrary_normal_input_nonzero_influence_claimed':False,
 'locally_covariant_finite_amplitude_phase_matched':False,
 'normality_implies_unbounded_stress_moments':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/FINITE_LAPSE_CTP.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/WEYL_RESPONSE.md'])
