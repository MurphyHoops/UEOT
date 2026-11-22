"""All integer harmonics: nonresonance and analytic-coefficient inverse bounds."""
import sympy as sp
from common import *
def result():
    fast=json.loads((HERE/"fast_root.json").read_text())
    qL,qU=map(exact,fast["fast_to_slow_rate_ratio"])
    N=math.floor(float(qL.a))
    assert above(qL,N) and below(qU,N+1)
    m0=exact((-characteristic_zero()).a)
    assert above(m0,3)
    terms=[
       3*(1-4/qL**2),
       (N*N-1)*(1-N*N/qL**2),
       ((N+1)**2-1)*((N+1)**2/qU**2-1)]
    lower=interval(min(v.a for v in terms),min(v.b for v in terms))*m0
    assert above(lower,"11.99")
    fourth_terms=[
       N**4*qL**2/((N*N-1)*(qL*qL-N*N)),
       (N+1)**4*qU**2/(((N+1)**2-1)*((N+1)**2-qU*qU))]
    r1_upper=exact((SLOW*SLOW).b)
    M4=r1_upper**2/m0*interval(max(v.a for v in fourth_terms),max(v.b for v in fourth_terms))
    assert below(M4,"2e18")
    # Mixed slow/fast combinations retain both free linear amplitudes.
    mixed_lower=m0*(2*qL+5+2/qL)
    mixed_M4=r1_upper**2/m0*qU*(qU+1)**4/((qU+2)*(2*qU+1))
    assert above(mixed_lower,lower.b) and below(mixed_M4,M4.a)

    t,Q=sp.symbols("t Q",positive=True)
    assert sp.diff((t-1)*(Q-t),t,2)==-2
    assert sp.simplify(sp.diff((t-1)*(t-Q),t)-(2*t-Q-1))==0
    numerator=t*((Q+1)*t-2*Q)
    assert sp.simplify(sp.diff(t*t/((t-1)*(Q-t)),t)-numerator/((t-1)**2*(Q-t)**2))==0
    assert sp.simplify(sp.diff(t*t/((t-1)*(t-Q)),t)+numerator/((t-1)**2*(t-Q)**2))==0
    q=sp.symbols("q",positive=True)
    assert sp.factor(((q+1)**2-1)*(((q+1)**2/q**2)-1)-(2*q+5+2/q))==0
    g=q*(q+1)**4/((q+2)*(2*q+1))
    assert sp.factor(sp.diff(g,q)/g-
        (1/(q*(2*q+1))+(3*q+7)/((q+1)*(q+2))))==0
    # Independent formula for positive-y F: -F(y)>=c gives the common bound.
    m,r=sp.symbols("m r",positive=True)
    n=sp.symbols("n",integer=True,positive=True)
    assert sp.simplify((m/(r*r*Q))*r*r*(n*n-1)*(Q-n*n)
                       -m*(n*n-1)*(1-n*n/Q))==0
    return {
      "fast_to_slow_rate_ratio":[float(qL.a),float(qU.b)],
      "strict_enclosing_integers":[N,N+1],
      "all_integer_harmonics_n_at_least_2_nonresonant":True,
      "minus_D_zero_lower":outward(m0),
      "three_endpoint_divisor_bounds":[outward(m0*t) for t in terms],
      "uniform_absolute_characteristic_lower":outward(lower),
      "coefficient_inverse_unweighted_norm_upper":outward(1/lower)[1],
      "four_derivative_inverse_norm_upper":outward(M4)[1],
      "fourth_bound_endpoint_terms":[outward(t) for t in fourth_terms],
      "all_slow_fast_combinations_nonresonant":True,
      "mixed_frequency_domain":"lambda=n*s_*+m*sigma_F, n,m>=0, n+m>=2",
      "mixed_absolute_characteristic_lower":outward(mixed_lower),
      "mixed_four_derivative_inverse_norm_upper":outward(mixed_M4)[1],
      "same_global_divisor_and_M4_cover_all_combinations":True,
      "two_variable_coefficient_inverse_retains_both_linear_amplitudes":True,
      "two_variable_graph_domain":"X={u:sum abs(P(n*s_*+m*sigma_F)*u_nm)*Rz^n*Rw^m<infinity}, n+m>=2",
      "four_derivative_space_is_full_operator_domain":False,
      "nonlinear_two_parameter_history_exists":False,
      "finite_harmonic_scan_executed":False,
      "method":"Exact DD lower bound, one concave interval and one monotone interval; only nearest integer endpoints",
      "conditional_space":"f(z)=sum_{n>=2} f_n*z^n with sum abs(f_n)*R^n finite; u_n=f_n/P(n*s_*)",
      "four_derivatives":"sum (n*s_*)^4*abs(u_n)*R^n <= M4*sum abs(f_n)*R^n",
      "analytic_z_selection_is_extra_assumption":True,
      "analytic_selection_adopted_as_physical_law":False,
      "noninteger_fast_mode_excluded_by_Hadamard":False,
      "full_nonlinear_map_or_convergent_series_proved":False,
      "proof":"INVERSE.md"
    }
if __name__=="__main__":finish("harmonics.py",result(),["fast_root.py","fast_root.json"])
