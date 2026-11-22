"""Uniform spectral mass, smooth packet constants and normal embedding."""
import sympy as s
from common import *
z=s.symbols("z",positive=True)
# Each z^k exp(4-z) decreases for z>=4 and k<=4.
for k in (2,3,4):
    assert s.simplify(s.diff(z**k*s.exp(4-z),z)-z**(k-1)*s.exp(4-z)*(k-z))==0
hpp=416*iv.sqrt(2)+16+iv.mpf(1)/4
ct=4*605/(iv.sqrt(iv.mpf(3)/8)*iv.exp(-iv.mpf(4)/3))
assert below(hpp,605) and below(ct,16000)
assert below(4*ALPHA*16000/D,exact(8)**(iv.mpf(4)/3))
eta=(4/(DELTA*D))**(iv.mpf(3)/4)
m=D/2;m0=D*(2**(iv.mpf(1)/3)+iv.mpf(1)/2)
r=m/2;R=4*m0**2/m;qb=1/(64*(2**(iv.mpf(1)/3)+iv.mpf(1)/2)**2)
m_s,M_s=s.symbols("m M",positive=True)
assert s.simplify(m_s/(4*(4*M_s**2/m_s))-m_s**2/(16*M_s**2))==0
assert above(qb,0.005) and below(qb,0.006)
finish("critical_state.py",{
 "bump_h_second_derivative_upper":outward(hpp),
 "packet_T_constant_derived_upper":outward(ct),"packet_T_constant_used":16000,
 "packet_center_floor":8,"packet_eta":outward(eta),
 "uniform_negative_band_mass_lower":outward(qb),
 "scaled_band_r":outward(r),"scaled_band_R":outward(R),
 "normal_embedding":"Omega=V rho_old V*, (V psi)(P)=phi_P psi(P)",
 "strict_negative_sector":True,"complete_original_P_law_preserved":True,
 "bare_source_state_preserved":False,"bare_QQ_added_PSD_metric":True,
 "P_section_all_derivatives_polynomially_bounded":True,
 "one_fixed_unitary_history":True,"local_preparation_device_constructed":False})
