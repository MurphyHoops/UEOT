"""Same-source residual charge and sharp-combination/independent-carrier identities."""
import sympy as s
from common import require,finish
a,h,hp,U,V0,Q,D,H0=s.symbols("a h hp U V0 Q D H0",real=True,nonzero=True)
V=hp+h*h
qi=-2*a*a*h*s.exp(U)
qpi=-2*a*a*s.exp(U)*(hp+3*h*h)
Bi=(-qi*D+(qpi-h*qi)*Q)/(3*V0*a**4)
di=s.Rational(2,3)*(H0-h*D+h*h*Q)/(V0*a*a)
kap=2*s.exp(U)/(3*V0*a*a)
require(s.simplify(-s.exp(U)*di-Bi+kap*(H0-V*Q))==0,"Exact residual cancellation")
# Same finite-cutoff source Ward.
t=s.symbols("t",real=True)
aa=s.Function("a")(t);hh=s.Function("h")(t)
QQ=s.Function("Q")(t);DD=s.Function("D")(t);HH=s.Function("H")(t)
vv=s.diff(hh,t)+hh*hh
rho=(HH-hh*DD+hh*hh*QQ)/(V0*aa**4)
pres=(s.diff(QQ,t,2)-3*hh*DD+(hh*hh-2*s.diff(hh,t))*QQ+HH)/(3*V0*aa**4)
ward=s.diff(rho,t)+3*hh*(rho+pres)
ward=ward.subs({s.diff(QQ,t,2):s.diff(DD,t),s.diff(QQ,t):DD,s.diff(HH,t):vv*DD,s.diff(aa,t):hh*aa})
require(s.simplify(ward)==0,"Same-source density pressure Ward")
I,ZQ,ZD,ZP=s.symbols("I ZQ ZD ZP",real=True)
Qzero=a*a*(ZQ+2*I*ZD+I*I*ZP)/2
Dzero=a*a*h*(ZQ+2*I*ZD+I*I*ZP)+ZD+I*ZP
H0zero=(a*h)**2*ZQ/2+a*h*(a*h*I+1/a)*ZD+(a*h*I+1/a)**2*ZP/2
HV=H0zero-V*Qzero
expected=-a*a*hp*ZQ/2+(h-a*a*hp*I)*ZD+(1/(2*a*a)+h*I-a*a*hp*I*I/2)*ZP
require(s.simplify(HV-expected)==0,"Actual zero-mode bulk Hamiltonian")
om,F,Fp,Vv=s.symbols("omega F Fp V")
raw=(-s.I*om*F+Fp)**2+(om*om-Vv)*F*F
require(s.expand(raw-(-2*s.I*om*F*Fp+Fp*Fp-Vv*F*F))==0,"Sharp H_V leading cancellation")
# Full arbitrary Hermitian support-leakage columns and the saturating normal record.
p,m0,m2=s.symbols("p m0 m2",real=True)
l00,l01,l10,l11=s.symbols("l00 l01 l10 l11",complex=True)
leak0=l00*s.conjugate(l00)+l10*s.conjugate(l10)
leak2=l01*s.conjugate(l01)+l11*s.conjugate(l11)
leak=(1-p)*leak0+p*leak2
variance=(1-p)*(m0*m0+leak0)+p*(m2*m2+leak2)-((1-p)*m0+p*m2)**2
require(s.expand(variance-leak-p*(1-p)*(m2-m0)**2)==0,"Exact support-leakage decomposition")
saturating=(1-p)*((m0-m0)**2+leak0)+p*((m2-m2)**2+leak2)
require(s.expand(saturating-leak)==0,"Two-record normal extension attains bound")
finish("constraint_residual.py",dict(
 explicit_source_density_Ward=True,
 density_transpose_defined_via_actual_Ward_intertwiner=True,
 residual_charge="-2*exp(U_i)*delta(H0-V_i*Q)_i/(3*V0*a_i^2)",
 residual_independent_of_unit_integral_smooth_test=True,
 particular_sharp_H0_minus_VQ_has_GNS_L2_limit=True,
 separate_sharp_density_H0_Q_assumed_L2=False,
 original_compact_radial_source_residual_variance_strictly_positive=True,
 fullmode_pressure_candidate_satisfies_density_constraint=False,
 fixed_bare_source_independent_carrier_optimum="Tr rho H(1-P)H > 0",
 abstract_two_record_extension_attains_mathematical_optimum=True,
 independent_carrier_realized_as_gravity=False,
 finite_low_initial_completion_uniquely_forced_by_UV=False,
 result_excludes_all_true_mixed_preparations=False),
 ["finite_stress/lapse_boundary/ACTUAL_INVERSE.md",
  "finite_stress/lapse_boundary/PREPARED_READOUT.md",
  "finite_stress/lapse_boundary/FINITE_SOURCE_DOMAIN.md",
  "finite_stress/BOUNDARY_STATE.md","finite_stress/BOUNDARY_EXTENSION.md"],
 proof="CONSTRAINT_RESIDUAL.md")
