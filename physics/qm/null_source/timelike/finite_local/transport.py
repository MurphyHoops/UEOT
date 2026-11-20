"""Smooth same-CCR transport of the actual state; uniform Bogoliubov bounds."""
from common import *
def result():
    eps=exact("0.01");m=exact(31)/32;M=exact(33)/32
    caps=[5,22,212,2220,29000]
    assert below(caps[0]*eps**2/3,1-m*m)
    assert above(iv.sqrt(1-5*eps**2/3)-212*eps**4/72,m)
    assert below(iv.sqrt(1+5*eps**2/3)+212*eps**4/72,M)
    cq=(1+M+M*M)/(m*m*(1+m))
    terms=[
      cq*5*212/4,
      5*exact(22)**2/(16*m**4),
      exact(212)**2*eps**2/(64*3),
      exact(212)**2*eps**2/(32*m**3*3)+exact(22)**2*212*eps**4/(64*m**5*9),
      exact(29000)/(16*m),
      3*exact(22)*2220*eps**2/(32*m**3*3),
      3*exact(2220)**2*eps**4/(256*m*m*9),
      9*exact(22)**2*212*eps**4/(128*m**6*9)]
    assert all(below(x,y) for x,y in zip(terms,[445,172,1,1,1871,1,1,1]))
    defect=sum(terms,exact(0));assert below(defect,2493)
    exponent=22*eps**2/(m*m*3)
    assert below(exponent,"0.001") and below(iv.exp(exponent),exact(501)/500)
    beta_coefficient=7000*eps**5
    beta_max=beta_coefficient/(iv.sqrt(3)**5)
    assert below(beta_max,"1e-7")
    raw_IR=(exact(63)/32)**6*(exact(13)/12)**2*(1+2*beta_max**2)
    assert below(raw_IR,69)
    CIR=(exact(13)/12)**2*(exact(7)/4)**6
    assert below(CIR*(1+3*exact("1e-7")),34)
    # Generous all-mode mean estimate, both scalar fields and thermal excess.
    mean_difference=34*exact(26)/25/iv.pi**2*2*beta_coefficient*(iv.sqrt(1+beta_max**2)+beta_max)*exact(16)/9
    assert below(mean_difference,"1e-5")
    amin=exact(4)/7*iv.sqrt(XC)
    # The actual fixed A is separately smaller or larger than amin; use safe min.
    astar2=iv.mpf([min(X.a,amin.a**2),min(X.b,amin.b**2)])
    shear=5/(2*eps*astar2)
    return {
      "geometry_contract":"explicit smooth off-shell preparation, static at both ends",
      "same_initial_CCR_state_propagated":True,"high_modes_reset":False,
      "epsilon":outward(eps),"conformal_h_derivative_potential_caps":caps,
      "defect_R_over_eps6_omega4_upper":outward(defect),
      "ramp_energy_exponent_upper":outward(exponent),
      "Bogoliubov_beta_bound":"7000*epsilon^5/omega^5",
      "Bogoliubov_beta_coefficient":outward(beta_coefficient),
      "uniform_all_shells_Bogoliubov_beta_upper":outward(beta_max),
      "transported_raw_IR_energy_coefficient_upper":outward(raw_IR),
      "all_modes_mean_stress_difference_over_lambda4_upper":outward(mean_difference),
      "same_future_pair_caps_retained":[25000,600000],
      "same_future_high_RMS_coefficients_retained":[1600,8000],
      "uniform_zero_Q_shear_during_ramps_and_plateau_upper":outward(shear),
      "record_dependent_static_waiting_shear_included_separately":True,
      "Hadamard_basis":"smooth exact Klein-Gordon evolution, not finite WKB order",
      "preparation_total_Einstein_equation_solved":False,
      "proof":"TRANSPORT.md"}
if __name__=="__main__":finish("transport.py",result(),["TRANSPORT.md","profile.json","ultraviolet.json","fluctuations.json"])
