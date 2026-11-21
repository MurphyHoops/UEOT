"""Finite canonical lapse Gaussian influence and controlled second cumulants."""
import numpy as np
from scipy.linalg import expm
import sympy as s
from common import finish,require,iv,outward,above,below
K=8;ns=2;T=.02;V=2*np.pi**2
blocks=[]
for ell in range(K):
 ks=np.arange(ell+1,K+1,dtype=float);d=len(ks)
 def a(k):
  if k<=ell or k==0:return 0.
  return .5*np.sqrt((k-ell)*(k+ell+1)/(k*(k+1)))
 M=np.zeros((d,d))
 for i,k in enumerate(ks):
  M[i,i]=(4*(a(k)**2+a(k-1)**2)-1)/np.sqrt(V)
  if i+2<d:M[i,i+2]=M[i+2,i]=4*a(k)*a(k+1)/np.sqrt(V)
 A=((ks[:,None]**2+ks[None,:]**2)/2-4/3)*M
 D=np.diag(ks);I=np.eye(d);O=np.zeros((d,d));J=np.block([[O,I],[-I,O]])
 scale=np.diag(np.r_[np.sqrt(ks),1/np.sqrt(ks)])
 blocks.append((ell,ks,M,A,D,J,scale))
# Exact full-shell trace identity, including all multiplicities.
kk,ll=s.symbols('k l',integer=True,positive=True)
summed=s.summation((2*ll+1)*(1-2*ll*(ll+1)/(kk*kk-1)),(ll,0,kk-1))
require(s.simplify(summed)==0,'full harmonic-shell zero mean')
mean=0.;weights={}
for ell,ks,M,A,D,J,scale in blocks:
 mult=ns*(2*ell+1)
 mean+=mult*np.sum(ks*np.diag(M)+np.diag(A)/ks)/4
 B=((ks[:,None]-ks[None,:])**2-8/3)*M/(8*np.sqrt(ks[:,None]*ks[None,:]))
 for i,k in enumerate(ks):
  for j,l in enumerate(ks):
   n=int(k+l);weights[n]=weights.get(n,0.)+2*mult*B[i,j]**2
require(abs(mean)<1e-12,'fixed initial vacuum mean')
C=ns/(9*V)
for n,w in weights.items():
 target=C*(2/3 if n==2*K else 1) if n>=4 and n%2==0 else 0
 require(abs(w-target)<1e-12,'actual action shell weight '+str(n))
tol=2e-11
def branch(eps,b):
 ell,ks,M,A,D,J,scale=b;d=len(ks)
 P=np.eye(d)+eps*M;Q=D@D+eps*A
 require(np.linalg.eigvalsh(P).min()>0 and np.linalg.eigvalsh(Q).min()>0,'positive quadratic Hamiltonian')
 G=np.block([[Q,np.zeros((d,d))],[np.zeros((d,d)),P]])
 S=expm(T*J@G)
 require(np.linalg.norm(S.T@J@S-J)<tol,'symplectic regression')
 AA=S[:d,:d];BB=S[:d,d:];CC=S[d:,:d];DD=S[d:,d:]
 Je=AA+1j*BB@D
 Z=(DD@D-1j*CC)@np.linalg.inv(Je)
 require(np.linalg.norm(Z-Z.T)<tol and np.linalg.eigvalsh(Z.real).min()>0,'normal Gaussian state')
 return S,Je,Z
def logdet(X):return np.log(np.linalg.det(X))
def influence(ep,em,gaussian=False):
 value=0j
 for b in blocks:
  ell,ks,M,A,D,J,scale=b;d=len(ks)
  Sp,Jp,Zp=branch(ep,b);Sm,Jm,Zm=branch(em,b)
  if gaussian:
   term=d*np.log(2)/2+np.log(np.linalg.det(D))/2-(logdet(Jp)+np.conjugate(logdet(Jm))+logdet(Zp+np.conjugate(Zm)))/2
  else:
   S=scale@np.linalg.solve(Sm,Sp)@np.linalg.inv(scale)
   aa=S[:d,:d];bb=S[:d,d:];cc=S[d:,:d];dd=S[d:,d:]
   alpha=(aa+dd+1j*cc-1j*bb)/2
   beta=(aa-dd+1j*cc+1j*bb)/2
   require(np.linalg.norm(alpha@alpha.conj().T-beta@beta.conj().T-np.eye(d))<tol,'Bogoliubov normalization')
   term=-logdet(np.conjugate(alpha))/2
  value+=ns*(2*ell+1)*term
 return value
# Analytic no-winding estimate for every pair in the history grid.
tt=iv.mpf('.02');emax=iv.mpf('.08');VV=2*iv.pi**2
Cg=3*(iv.mpf(K)**iv.mpf('1.5')+iv.mpf(4)/3)/iv.sqrt(VV)
r=tt*(2*emax)*Cg*iv.exp(2*tt*(K+emax*Cg))
angle=K*(-iv.log(1-r))
require(below(r,1) and below(angle,iv.pi),'continuous determinant phase branch')
grid=[-.08,-.04,0.,.04,.08]
F=np.array([[np.exp(influence(ep,em)) for em in grid] for ep in grid])
require(np.linalg.norm(F-F.conj().T)<tol,'CTP conjugation')
require(np.max(abs(np.diag(F)-1))<tol,'CTP normalization')
mineig=float(np.linalg.eigvalsh((F+F.conj().T)/2).min())
require(mineig>-tol,'analytic Gram positivity regression')
phase_error=abs(influence(.08,-.04)-influence(.08,-.04,True))
require(phase_error<tol,'independent Gaussian overlap including phase')
N=sum(2*w*(1-np.cos(n*T))/n**2 for n,w in weights.items())
R=sum(2*w*(n*T-np.sin(n*T))/n**2 for n,w in weights.items())
eta=.01
lp=influence(eta,0);lm=influence(-eta,0)
same=(lp+lm)/eta**2
minus=(influence(0,eta)+influence(0,-eta))/eta**2
cross=(influence(eta,eta)-influence(eta,-eta)-influence(-eta,eta)+influence(-eta,-eta))/(4*eta**2)
hessian_error=max(abs(same-(-N+1j*R)),abs(minus-(-N-1j*R)),abs(cross-N))
require(hessian_error<2e-8,'three finite-initial complex Hessian entries')
# Full-field SECOND cumulants only, with rigorous absolute tails.
kf=10000;civ=iv.mpf(2)/(9*VV)
Ninf=civ*((iv.pi*tt-tt*tt)/2-iv.sin(tt)**2)
Nk=civ*(sum(((iv.sin(j*tt)/j)**2 for j in range(2,kf)),iv.mpf(0))
          +iv.mpf(2)/3*(iv.sin(kf*tt)/kf)**2)
Ntail=civ*(iv.mpf(1)/(3*kf*kf)+iv.mpf(1)/kf)
require(above(Ninf-Nk) and bool((Ninf-Nk).b<=Ntail.b),'full noise second-cumulant tail')
# gamma_R=0; use the same harmonic-number counterterm exactly.
Rk=-civ*tt*(1+iv.mpf(1)/(3*kf))-civ/2*(
 sum((iv.sin(2*j*tt)/j**2 for j in range(2,kf)),iv.mpf(0))
 +iv.mpf(2)/3*iv.sin(2*kf*tt)/kf**2)
Rtail=civ*(tt/(3*kf)+iv.mpf(1)/(6*kf*kf)+iv.mpf(1)/(2*kf))
finish('finite_lapse_ctp.py',{'finite_amplitude_mode_cutoff':K,
 'full_oscillators_including_species':ns*sum(k*k for k in range(1,K+1)),
 'pulse_duration_model_conformal_time':T,'history_grid':grid,
 'normal_initial_state':'one common full finite-mode Einstein vacuum',
 'canonical_cutoff_after_full_Legendre_transform':True,
 'relative_symplectic_distance_upper_bound':outward(r),
 'determinant_phase_no_winding_bound':outward(angle),
 'finite_Gram_min_eigenvalue_above_negative_tolerance':True,
 'Gaussian_metaplectic_complex_log_difference_upper_bound':tol,
 'complex_Hessian_regression_error_upper_bound':2e-8,
 'floating_regression_tolerance':tol,'Hessian_regression_tolerance':2e-8,
 'finite_K_noise_cumulant':round(float(N),12),'finite_K_response_cumulant':round(float(R),12),
 'sample_complex_influence_rounded_10_decimals':[round(float(F[-1,1].real),10),round(float(F[-1,1].imag),10)],
 'second_cumulant_tail_cutoff':kf,
 'full_field_noise_cumulant_bounds':outward(Ninf),
 'full_field_renormalized_response_cumulant_enclosure':[outward(Rk-Rtail)[0],outward(Rk+Rtail)[1]],
 'noise_tail_upper_bound':outward(Ntail),'response_tail_upper_bound':outward(Rtail),
 'renormalized_gamma_R_example':0,
 'trace_influence_is_not_vacuum_postselection':True,
 'finite_amplitude_locally_covariant_physical_phase_limit_proved':False,
 'separate_spectral_zero_normal_limit':'STATIC_NORMALITY.md',
 'joint_quantum_geometric_CTP_solution_proved':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SPATIAL_NOISE.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/WEYL_RESPONSE.md'])
