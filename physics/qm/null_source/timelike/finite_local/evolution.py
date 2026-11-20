"""Leading conditional-mean histories and complete-record source error bounds."""
import sympy as sp
from common import *
def result():
    a,H,M,m,ell=sp.symbols("a H M mu lambda2",positive=True)
    constraint=H**2+a**(-2)-ell-M*m/(3*a**6)
    flow={a:a*H,H:a**(-2)-M*m/a**6}
    derivative=sp.diff(constraint,a)*flow[a]+sp.diff(constraint,H)*flow[H]
    assert sp.factor(derivative)==0
    assert sp.simplify(flow[H]+H**2-constraint-(ell-2*M*m/(3*a**6)))==0
    q,xc,beta=sp.symbols("q xc beta",positive=True)
    aa=xc*(1+q)**sp.Rational(1,3)
    H2=(1-(1+q)**(-sp.Rational(1,3))+beta*q/(1+q))/xc
    assert sp.simplify(H2+1/aa-1/xc-beta*xc**2*q/aa**3)==0
    assert above(BETA) and below(BETA,exact(3)/20)
    assert above(1-2*BETA,"0.7")
    source_rms=BETA/MU*iv.sqrt(LOCAL_MSE_UPPER)
    prep_log_upper=iv.log(XC/X)/2+iv.log(2)/6
    proper_window=exact("0.1")/iv.sqrt(LAMBDA2)
    return {
      "model":"leading Einstein: two zero modes + fixed U0; high RSET and apparatus omitted here",
      "fixed_original_M2":outward(M2),"fixed_original_U0":outward(U0),
      "lambda_squared":outward(LAMBDA2),"xc":outward(XC),"beta":outward(BETA),
      "initial_radius_squared":"xc*(1+mu_record/mu_reference)^(1/3)",
      "initial_H_squared":"lambda^2*(1-(1+q)^(-1/3)+beta*q/(1+q))",
      "flow":"a_dot=a H, H_dot=a^-2-M2*mu_record/a^6",
      "constraint_derivative":"identically zero",
      "q_fixed_along_history":True,
      "all_records_future_expanding":True,
      "dimensionless_acceleration_lower":outward(1-2*BETA),
      "dimensionless_H_squared_upper":outward(1+BETA),
      "common_proper_window_for_tau_0_to_0_1":outward(proper_window),
      "uniform_positive_conformal_window_over_all_records":False,
      "normal_zero_evolution":"Q(t)=Q+P*integral a^-3 dt, P(t)=P",
      "source_only_relative_constraint_RMS_upper":outward(source_rms),
      "source_only_relative_constraint_MSE_upper":outward(source_rms**2),
      "uniform_finite_preparation_time_with_bounded_H_from_fixed_A":False,
      "expected_minimum_log_expansion_upper":outward(prep_log_upper),
      "minimum_duration_formula":"Hmax*tau_req=0.5*log(xc/A^2)+(1/6)*log(1+q)",
      "actual_local_measurement_joint_state_transported_to_this_geometry":False,
      "full_semiclassical_Einstein_solution":False,
      "proof":"EVOLUTION.md"}
if __name__=="__main__":finish("evolution.py",result(),["EVOLUTION.md"])
