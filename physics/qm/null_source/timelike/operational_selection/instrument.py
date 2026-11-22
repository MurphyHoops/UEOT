"""Complete Gaussian source instrument, backaction, and source-clock information tradeoff."""
from common import *
import sympy as sp
def result():
    vm=exact("1e-12")
    d=1/SIGMA
    postD=SOURCE_C*d*iv.sqrt(vm)/(2*X)
    postD45=postD*iv.sqrt(45)
    assert below(postD,".0492") and below(postD45,".330")
    error45=(1-postD45)/2
    assert above(error45,".335")
    necessary_vm=(exact(".9")*2*X/(SOURCE_C*d*iv.sqrt(45)))**2
    assert above(necessary_vm,"7.4e-12") and below(necessary_vm,"7.6e-12")
    vs=box(CASE["variance_S0"])
    pointer_energy_ratio=iv.sqrt(1+vs/vm)
    assert above(pointer_energy_ratio,"4.33e5")
    q_backaction=MU/(SOURCE_C*vm)
    D_backaction=(vs+MU**2)/vm
    # Symbolic calibration and minimum-energy oscillator pointer, all outcomes retained.
    v,g,C,mu,var,noise,omega=sp.symbols("v g C mu var v_m Omega",positive=True)
    assert sp.simplify((g*g/(C*C*v)*(C*mu)).subs(g*g,v/noise)-mu/(C*noise))==0
    ptr=omega*(v+1/(4*v)+v*var/noise)/2
    vopt=1/(2*sp.sqrt(1+var/noise))
    assert sp.simplify(ptr.subs(v,vopt)-omega*sp.sqrt(1+var/noise)/2)==0
    assert sp.simplify(sp.diff(ptr,v).subs(v,vopt))==0
    s,y=sp.symbols("s y",real=True)
    density=sp.exp(-(y-s)**2/(2*noise))/sp.sqrt(2*sp.pi*noise)
    assert sp.integrate(density,(y,-sp.oo,sp.oo))==1
    assert sp.simplify(sp.integrate((y-s)**2*density,(y,-sp.oo,sp.oo))-noise)==0
    return {
      "instrument":"K_y=(2*pi*v_m)^(-1/4)*exp[-(y-S0)^2/(4*v_m)]",
      "pointer_unitary":"exp[-i*g*(S0-mu)*Pi], Y=mu+Xout/g, v_m=VarX/g^2",
      "complete_record_domain":"all y in R, no failure or tail discarded",
      "readout_law":"Y=S0+independent N(0,v_m)",
      "nonselective_full_P_spectrum_and_free_matter_T_algebra_preserved":True,
      "pointer_and_interaction_stress_included_in_invariance_claim":False,
      "Q_backaction":"v_m * sum_i DeltaVar(Q_i) = mu/(2*pi^2*M2), minimum Gaussian pointer",
      "D_backaction":"DeltaVar(D)=E(S0^2)/v_m",
      "clock_QFI_after":"(2*pi^2*M2)^2/A^4 * E_p MMSE(S0|Y,p)",
      "clock_QFI_loss":"same factor * E_p Var_Y(E[S0|Y,p])",
      "clock_QFI_after_upper":"(2*pi^2*M2)^2*v_m/A^4",
      "all_Y_probabilities_independent_of_theta":True,
      "finite_test_D_after_upper":"abs(dtheta)*pi^2*M2/A^2 * sqrt(N*v_m)",
      "example_measurement_variance":outward(vm),
      "example_single_D_after_upper":outward(postD)[1],
      "example_45_copy_D_after_upper":outward(postD45)[1],
      "example_45_copy_error_lower":outward(error45)[0],
      "necessary_measurement_variance_for_45_copy_error_0_05":outward(necessary_vm),
      "minimum_pointer_energy_over_Omega_half":outward(pointer_energy_ratio),
      "example_sum_Q_backaction":outward(q_backaction),
      "example_D_backaction":outward(D_backaction),
      "pointer_energy_scope":"only Hptr=Omega*(X^2+Pi^2)/2 with fixed Omega, centered calibration and optimized v",
      "universal_measurement_energy_bound_claimed":False,
      "coherent_pointer_purification_available_in_clock_bound":False,
      "local_gravitational_device_constructed":False,"proof":"INSTRUMENT.md"}
if __name__=="__main__":finish("instrument.py",result(),["INSTRUMENT.md"])
