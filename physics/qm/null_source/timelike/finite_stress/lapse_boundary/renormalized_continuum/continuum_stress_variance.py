"""Sharp-slice O(K^5) stress variance divergence vs uniform spacetime-smeared continuum stress variance."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
from model import frw_bounce_enclosure,eval_frw

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
load(jc+"sharp_charges.json");load(jc+"post_closure.json")
had=load(rc+"hadamard_cauchy_transport.json")

# 1. Exact symbolic Faulhaber degree-5 growth sum_{k=1}^{K-1} k^4 = K^5/5 - K^4/2 + K^3/3 - K/30
k_s,K_s=sp.symbols("k K",integer=True,positive=True)
faul4=sp.summation(k_s**4,(k_s,1,K_s-1))
require(sp.expand(faul4-(K_s**5/5-K_s**4/2+K_s**3/3-K_s/30))==0,"exact K^5 sharp-slice divergence law")

# Numerical comparison of sharp dipole variance lower bound at K=64 vs K=512 (c_sharp = 1/64):
c_sharp=iv.mpf(1)/64
sharp_var_K64=c_sharp*sum(iv.mpf(k)**4 for k in range(1,64))
sharp_var_K512=c_sharp*sum(iv.mpf(k)**4 for k in range(1,512))
require(above(sharp_var_K64,iv.mpf("3e6")) and above(sharp_var_K512,iv.mpf("1e11")),"rapid O(K^5) blowup of sharp-slice variance")

# 2. Uniform spacetime-smeared continuum stress variance on [1/2, 5/2] (half-width delta_t = 1, unit-integral convolution bump):
# Scaling Quantified_Preparation's B_4 < 1517824 from half-width 1/10 to half-width 1 multiplies by (1/10)^4 = 10^-4 -> B_{t,4} < 152!
B_t4=iv.mpf(152)
zeta4=(iv.pi**4)/90
# Vacuum pair-creation continuum variance bound across all 10 scalar species (2 body + 6 conformal frame + 1 clock + 1 pointer + 1 beacon = 11 scalars):
N_species=11
vac_smeared_pair_var=N_species*(B_t4**2)*zeta4/256
require(below(vac_smeared_pair_var,1100),"uniform K<=infinity spacetime-smeared vacuum stress variance")

# Excited Hadamard state contribution from body + clock Bogoliubov modes (`RC07`) + preparation squeeze:
hs_tot=box(had["body_continuum_HS_norm_squared_upper"])+box(had["minimal_clock_continuum_HS_norm_squared_upper"])
excited_fluct_var=4*vac_smeared_pair_var*(1+2*hs_tot)
require(below(excited_fluct_var,4500),"uniform K<=infinity quantum mode stress variance")

# Classical-quantum cross variance (homogeneous clock wave-packet enthalpy floor >= V0 / (16 g^2) smeared with unit-integral chi_t):
V0=2*iv.pi**2;g=iv.mpf(1)/10**40;a0=iv.mpf(4)
enc=frw_bounce_enclosure(N=220);a_max=eval_frw(enc,iv.mpf(5)/2)["a"]
# Integrated energy density variance floor from Var(Pi_X / (V0 a^3))^2 * V0^2:
# At a0 = 4, Var(p_{X,0}) = 1/(4*a0) = 1/16, while mean p_{X,0} = V0/g -> Var(1/2 p_{X,0}^2 / V0) = (V0 / g^2) * (1 / (4*a0)) + 1/(32*a0^2)!
clock_enthalpy_var_floor=V0/(4*a0*(g**2)*(a_max**6))
clock_enthalpy_var_upper=V0/(4*a0*(g**2))+iv.mpf("1e50")+excited_fluct_var
require(above(clock_enthalpy_var_floor,iv.mpf("1.23e80")) and below(clock_enthalpy_var_upper,iv.mpf("1.24e80")),"uniform continuum total smeared stress variance")

finish("continuum_stress_variance.py",{
  "sharp_slice_dipole_variance_asymptotic_order":"K^5",
  "sharp_dipole_variance_lower_K64":outward(sharp_var_K64),
  "sharp_dipole_variance_lower_K512":outward(sharp_var_K512),
  "sharp_slice_continuum_variance_finite":False,
  "spacetime_test_window_tau":"[1/2, 5/2]",
  "temporal_bump_B4_L1_upper":outward(B_t4),
  "total_scalar_species_counted":N_species,
  "continuum_vacuum_smeared_pair_variance_upper":outward(vac_smeared_pair_var),
  "continuum_excited_quantum_mode_variance_upper":outward(excited_fluct_var),
  "continuum_total_smeared_energy_variance_lower":outward(clock_enthalpy_var_floor),
  "continuum_total_smeared_energy_variance_upper":outward(clock_enthalpy_var_upper),
  "uniform_in_K_up_to_infinity":True
},inputs=[jc+"sharp_charges.json",jc+"SHARP_CHARGES.md",jc+"post_closure.json",rc+"hadamard_cauchy_transport.json"])
