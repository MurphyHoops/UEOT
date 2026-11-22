"""A fixed supercritical alternative and nonuniform approximation costs."""
import sympy as s
from common import *
rcrit=1/(M2*U0**2)
assert above(rcrit,1)
q=V0*U0;mu=q/2;gamma=q/8;delta=iv.sqrt(2)*DELTA
vstar=(V0/mu)**(iv.mpf(3)/2);Estar=mu*vstar
cstar=iv.mpf(3)/2*2**(-iv.mpf(1)/3)-1
gap=cstar-iv.sin(iv.pi/8)**2
assert below(delta/vstar,iv.mpf(1)/8) and above(gap)
tail_exp=NU0*(iv.sqrt(iv.mpf("1.99"))-iv.sqrt(RHI))**2
assert above(tail_exp,100000000)
x=s.symbols("x",positive=True)
w,chi=s.symbols("w chi",positive=True)
F=w-s.Rational(3,2)*w**s.Rational(1,3)+chi/(2*w)
assert s.simplify(s.diff(F,w,2)-(s.Rational(1,3)*w**s.Rational(-5,3)+chi*w**-3))==0
# Exact Rayleigh/Gamma tail identity behind each unbounded P-moment budget.
for k in range(1,5):
    expr=s.factorial(k)*s.exp(-x)*sum(x**j/s.factorial(j) for j in range(k+1))
    assert s.simplify(s.diff(expr,x)+x**k*s.exp(-x))==0
assert below(2**(iv.mpf(1)/3)/8,iv.mpf(1)/4)
finish("robustness.py",{
 "fixed_supercritical_mu_over_q":"1/2","fixed_supercritical_ell_over_ellcritical":"sqrt(2)",
 "fixed_example_delta_over_volume_center":outward(delta/vstar),
 "fixed_example_negative_Rayleigh_margin_fraction":outward(gap),
 "fixed_example_ground_band_energy_scale":outward(Estar),
 "smooth_cutoff_r0":"1.99","smooth_cutoff_r1":"2",
 "discarded_probability_log_upper":outward(-tail_exp),
 "discarded_probability_is_exactly_zero":False,
 "source_unbounded_P_moment_tail_budgets_included":True,
 "full_bare_initial_error":"sqrt(epsilon_tail)+2 eta_N, eta_N=O(N^(-1/3))",
 "model_sequence_mu_scaling":"N^(-2/3); each sequence member has fixed parameters in time",
 "constructed_volume_cost":"Theta(N)","constructed_dust_mean_cost":"Theta(N^(1/3))",
 "model_sequence_is_fixed_mu_limit":False,
 "graph_domain_equality":"D(H_P^k)=D(N^k) for fixed mu>0, compact P",
 "finite_clock_extra_bare_error_budget_included":True,
 "cost_is_universal_optimal_lower_bound":False,
 "old_A_free_history_matched":False,
 "finite_error_critical_uniqueness":False})
