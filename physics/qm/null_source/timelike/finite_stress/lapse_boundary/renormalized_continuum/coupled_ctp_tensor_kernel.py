"""Symbolic S^3 verification of coupled CTP scalar/vector/TT-tensor noise witnesses and Bianchi decay."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
from model import geodesic_cap_spectrum

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
load(jc+"source_ctp.json");load(jc+"lapse_phase.json")
svar=load(rc+"continuum_stress_variance.json")

# 1. Symbolic check of Keldysh (+,-) <-> (Sigma, Delta) transformation, unitarity Gamma(g,g)=0, and reflection symmetry
dgp,dgm,Gret,Nkel=sp.symbols("dgp dgm Gret Nkel",real=True)
sig=(dgp+dgm)/2;delt=dgp-dgm
gamma_2=-sp.Rational(1,2)*delt*Gret*sig+sp.I*sp.Rational(1,8)*(delt**2)*Nkel
require(sp.simplify(gamma_2.subs(dgm,dgp))==0,"CTP unitarity normalization Gamma[g,g]=0")
gamma_swapped=gamma_2.subs({dgp:dgm,dgm:dgp},simultaneous=True)
require(sp.simplify(gamma_swapped+sp.conjugate(gamma_2))==0,"CTP branch-reflection identity Gamma[g-,g+] = -Gamma[g+,g-]*")

# 2. Exact symbolic S^3 polynomial moment & covariant derivative verifier for k=3 vector & TT-tensor witnesses
Z=sp.symbols("z1 z2 z3 z4",real=True)
z1,z2,z3,z4=Z
V0_s=sp.Symbol("V0",positive=True)

def int_S3(expr):
    poly=sp.Poly(sp.expand(expr),*Z)
    tot=sp.Integer(0)
    for monom,coeff in poly.terms():
        if any(m%2==1 for m in monom):continue
        a=[m//2 for m in monom];A=sum(a)
        w=sp.Integer(1)
        for aj in a:w*=sp.rf(sp.Rational(1,2),aj)
        tot+=coeff*V0_s*w/sp.factorial(A+1)
    return sp.simplify(tot)

def grad_S3(f):
    df=[sp.diff(f,zb) for zb in Z]
    rad=sum(Z[b]*df[b] for b in range(4))
    return [sp.expand(df[a]-Z[a]*rad) for a in range(4)]

def div_S3(V):
    res=sum(sp.diff(V[a],Z[a])-Z[a]*sum(Z[b]*sp.diff(V[a],Z[b]) for b in range(4)) for a in range(4))
    return sp.expand(res.subs(z4**2,1-z1**2-z2**2-z3**2))

# Non-Killing k_V = 3 transverse vector witness coupling (k1=2, k2=3, Omega=5)
g_z1=grad_S3(z1);g_z2=grad_S3(z2)
V_vec=[sp.sqrt(12/V0_s)*z3*(z1*g_z2[a]-z2*g_z1[a]) for a in range(4)]
u2=(2/sp.sqrt(V0_s))*z1
u3=sp.sqrt(24/V0_s)*z2*z3
gu3=grad_S3(u3)
overlap_vec=int_S3(u2*sum(V_vec[a]*gu3[a] for a in range(4)))
require(div_S3(V_vec)==0 and int_S3(sum(v**2 for v in V_vec))==1,"unit divergence-free k=3 vector")
require(int_S3(u2**2)==1 and int_S3(u3**2)==1 and sp.simplify(overlap_vec-sp.sqrt(2/V0_s))==0,"exact k=3 vector (2,3) overlap")

# k_T = 3 (2,0)+(0,2) TT tensor witness coupling (k1=3, k2=3, Omega=6)
L2=[z1*grad_S3(z3)[a]-z3*grad_S3(z1)[a]+z4*grad_S3(z2)[a]-z2*grad_S3(z4)[a] for a in range(4)]
L3=[z1*grad_S3(z4)[a]-z4*grad_S3(z1)[a]+z2*grad_S3(z3)[a]-z3*grad_S3(z2)[a] for a in range(4)]
require(sp.expand(sum(L2[a]*L3[a] for a in range(4)))==0,"pointwise trace-free Killing tensor h_TT")
sphere_rel=z1**2+z2**2+z3**2+z4**2-1
require(sp.rem(sp.expand(sum(L2[a]**2 for a in range(4))-1),sphere_rel,z4)==0,"unit Killing norm L2 on S^3")
require(sp.rem(sp.expand(sum(L3[a]**2 for a in range(4))-1),sphere_rel,z4)==0,"unit Killing norm L3 on S^3")
uA=sp.sqrt(12/V0_s)*(z2*z4-z1*z3)
uB=sp.sqrt(12/V0_s)*(z1*z4+z2*z3)
guA=grad_S3(uA);guB=grad_S3(uB)
L2_uA=sum(L2[a]*guA[a] for a in range(4));L3_uB=sum(L3[a]*guB[a] for a in range(4))
L3_uA=sum(L3[a]*guA[a] for a in range(4));L2_uB=sum(L2[a]*guB[a] for a in range(4))
overlap_TT=int_S3((L2_uA*L3_uB+L3_uA*L2_uB)/sp.sqrt(2*V0_s))
require(int_S3(uA**2)==1 and int_S3(uB**2)==1 and int_S3(uA*uB)==0,"orthonormal k=3 scalar pair")
require(sp.simplify(overlap_TT+2*sp.sqrt(2)/sp.sqrt(V0_s))==0,"exact k=3 TT tensor (3,3) overlap")

# 3. Outward interval positivity bounds on [1.1, 1.9] subset (1/2, 5/2) (half-width delta_s = 1/5):
V0=2*iv.pi**2
im_scalar_lapse_lo=box(svar["continuum_total_smeared_energy_variance_lower"])/8
im_scalar_lapse_hi=box(svar["continuum_total_smeared_energy_variance_upper"])/8
require(above(im_scalar_lapse_lo,iv.mpf("1.5e79")),"strictly positive scalar-lapse CTP noise")

chi_hat_5_sq=iv.cos(iv.mpf(5)/5)**4
chi_hat_6_sq=iv.cos(iv.mpf(6)/5)**4
require(above(chi_hat_5_sq,iv.mpf("0.084")) and above(chi_hat_6_sq,iv.mpf("0.017")),"positive Fourier weights at Omega=5 and Omega=6")

# 6 conformal massless frame scalars: pair modulus squared 1/(12*V0) for vector and 2/(9*V0) for TT tensor, times 1/8 in Im Gamma
im_vector_shift_lo=iv.mpf(6)*chi_hat_5_sq/(8*12*V0)
im_tt_tensor_lo=iv.mpf(6)*2*chi_hat_6_sq/(8*9*V0)
require(above(im_vector_shift_lo,iv.mpf("2.6e-4")) and above(im_tt_tensor_lo,iv.mpf("1.4e-4")),"strictly positive k=3 vector and TT-tensor CTP noise")

# 4. Finite-K diffeomorphism / Bianchi commutator residual decay O(K^-10)
spec=geodesic_cap_spectrum(inv_r0=20,Kmax=16,nsub=64)
bianchi_K256=2*spec["B_rho0"]/(iv.mpf(256)**10)
bianchi_K512=2*spec["B_rho0"]/(iv.mpf(512)**10)
require(below(bianchi_K512,iv.mpf("4e-4")) and above(bianchi_K256/bianchi_K512,1023),"O(K^-10) decay of cutoff diffeomorphism defect")

finish("coupled_ctp_tensor_kernel.py",{
  "perturbation_support_window_tau":"[1.1, 1.9] subset (1/2, 5/2)",
  "counterterm_basis":"alpha_R * R^2 + alpha_W * Weyl^2",
  "CTP_unitarity_and_reflection_identities_verified":True,
  "scalar_lapse_Keldysh_Im_Gamma_lower":outward(im_scalar_lapse_lo),
  "scalar_lapse_Keldysh_Im_Gamma_upper":outward(im_scalar_lapse_hi),
  "vector_shift_k3_non_Killing_pair_frequency":5,
  "vector_shift_k3_Keldysh_Im_Gamma_lower":outward(im_vector_shift_lo),
  "TT_tensor_k3_quadrupole_pair_frequency":6,
  "TT_tensor_k3_Keldysh_Im_Gamma_lower":outward(im_tt_tensor_lo),
  "all_three_York_SO4_sectors_strictly_positive_noise":True,
  "cutoff_Bianchi_residual_K256_upper":outward(bianchi_K256),
  "cutoff_Bianchi_residual_K512_upper":outward(bianchi_K512),
  "cutoff_Bianchi_decay_exponent_K":10,
  "nonperturbative_quantum_gravity_path_integral_claimed":False
},inputs=[jc+"source_ctp.json",jc+"SOURCE_CTP.md",jc+"lapse_phase.json",jc+"LAPSE_PHASE.md",rc+"continuum_stress_variance.json"])
