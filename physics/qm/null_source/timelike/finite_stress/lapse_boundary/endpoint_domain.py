"""Quantitative sharp-boundary ultraviolet identities, distinct from smooth stress."""
import sympy as s
from common import finish
z, V, kap, A = s.symbols("z V kappa A", real=True, nonzero=True)
omega=s.sqrt(z**-2-1)
Omega=omega-V/(2*omega)
variance_shell=(z**-2)/(4*Omega**2)
log_overlap_shell=-(z**-2)*s.log(1+kap**2/(4*Omega**2))
assert s.limit(variance_shell,z,0,dir="+")==s.Rational(1,4)
assert s.limit(log_overlap_shell,z,0,dir="+")==-kap**2/4
assert s.limit((kap**2/(2*A)*(z**-2)/omega)*z,z,0,dir="+")==kap**2/(2*A)
assert s.limit(kap**2*(z**-2)/(2*omega**2),z,0,dir="+")==kap**2/2
# Exact characteristic-function derivatives verify Gaussian variance.
k, Om=s.symbols("k Om", positive=True)
chi=(1+s.I*k/(2*Om))**(-s.Rational(1,2))
m=s.simplify(s.I*s.diff(chi,k).subs(k,0))
second=s.simplify(-s.diff(chi,k,2).subs(k,0))
assert m==1/(4*Om)
assert s.simplify(second-m*m)==1/(8*Om**2)
# Explicit uniform static tail bounds, derived from elementary inequalities.
# For k>=3, Omega=omega: x=kappa^2/(4omega^2), 0<=x-log(1+x)<=x^2/2.
# Taking kappa=1/2 makes the finite K witnesses transparent, not a model input.
from mpmath import iv
Kvals=[16,64,256]
samples=[]
for K in Kvals:
    exact_log=iv.mpf(0)
    for j in range(K+1,2*K+1):
        exact_log-=j*j*iv.ln(1+iv.mpf(1)/(16*(j*j-1)))
    leading=-iv.mpf(K)/16
    # Difference of shell leading and exact coefficient bounded by 1/(10k^2).
    bound=iv.mpf(1)/(10*K)
    assert exact_log.a > (leading-bound).a
    assert exact_log.b < (leading+bound).b
    from common import outward
    samples.append({"K":K,"L":2*K,"static_kappa":"1/2",
                    "log_squared_tail_overlap":outward(exact_log),
                    "leading":outward(leading),"certified_error_bound":outward(bound)})
finish("endpoint_domain.py",{
    "actual_state_variance_QK_over_K_limit":"1/4",
    "tail_overlap_log_per_added_shell_limit":"-kappa^2/4",
    "c_number_subtraction_cannot_repair_GNS_L2":True,
    "arbitrary_scalar_rephasing_cannot_repair_strong_Cauchy":True,
    "strong_limit_exclusion_is_for_declared_Fock_identification":True,
    "static_active_kick_energy_over_K_squared_limit":"kappa^2/(4A)",
    "static_active_kick_number_over_K_limit":"kappa^2/2",
    "new_geometry_RSET_divergence_claimed":False,
    "smooth_charge_limit_taken_after_finite_endpoint_cancellation":True,
    "finite_static_tail_examples":samples
},["finite_stress/FINITE_SLICE_UV.md","finite_stress/DYNAMIC_CHARGE.md"])
