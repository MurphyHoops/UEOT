"""Global two-observable identifiability and actual zero-mode phase differences."""
from common import *
import sympy as sp
def result():
    assert exact(NONLINEAR["normalized_solution_correction_E4_upper"]).b<CORRECTION.a
    assert above(SLOW,"1.99") and below(SLOW,2) and above(SIGMA,936000)
    wz=weight(2*SLOW);ww=weight(SIGMA+SLOW)
    assert above(wz,1100) and above(ww,"1e25")
    vz=CORRECTION/(RZ*wz)
    hz=CORRECTION*2*SLOW/(RZ*wz)
    vw=CORRECTION/(RW*ww)
    hw=CORRECTION*(SIGMA+SLOW)/(RW*SIGMA*ww)
    assert below(vz,".004") and below(hz,".016")
    assert below(vw,".04") and below(hw,".041")
    assert below((SLOW+hz)/SIGMA,"2.2e-6")
    det=exact(".996")*exact(".959")-exact("1.04")*exact("2.2e-6")
    assert above(det,".955")
    gain=(exact("1.041")+exact("1.04"))/exact(".955")
    assert below(gain,"2.18")
    assert below(exact("1.041")/exact(".955"),"1.091")
    assert below(exact("1.004")/exact(".955"),"1.052")
    assert below(exact("2.2e-6")/exact(".955"),"2.31e-6")
    ubound=RZ/2+RW/2+CORRECTION/(4*wz)
    assert below(ubound,"5.01e-29")
    assert above(iv.exp(-3*ubound),".999") and below(iv.exp(3*ubound),"1.001")
    bw=2*exact("1.001")*exact("1.04")
    kw=exact("1.001")*exact("1.04")
    bz=2*exact("1.001")*exact("1.004")
    kz=exact("1.001")*exact("1.004")
    assert below(bw,"2.1") and above(2*exact(".999")*exact(".96"),"1.9")
    denominator=1-kz*RZ/2
    deta=kw/denominator
    proper=bw+(1+bz*RZ/2)*deta
    assert below(deta,"1.043") and below(proper,"3.13")
    phase_eta=exact("2.1")*RW/SIGMA
    phase_proper=exact("3.13")*RW/SIGMA
    assert below(phase_eta,"2.244e-57") and below(phase_proper,"3.345e-57")
    # Correct order of the derivative in the Jacobian.
    z,w,ss,ff=sp.symbols("z w s sigma")
    n,m=sp.symbols("n m",integer=True,positive=True)
    mon=z**n*w**m
    theta=lambda g:ss*z*sp.diff(g,z)+ff*w*sp.diff(g,w)
    assert sp.simplify(sp.diff(theta(mon),z)-theta(sp.diff(mon,z))-ss*sp.diff(mon,z))==0
    assert sp.simplify(sp.diff(theta(mon),w)-theta(sp.diff(mon,w))-ff*sp.diff(mon,w))==0
    return {
      "domain":"real |z|<=Rz/2, |w|<=Rw/2, frozen exact U=z+w+v",
      "weight_2s":outward(wz),"weight_sigma_plus_s":outward(ww),
      "coefficient_derivative_bounds":{"v_z":outward(vz)[1],"d_z_Theta_v":outward(hz)[1],
          "v_w":outward(vw)[1],"d_w_Theta_v_over_sigma":outward(hw)[1]},
      "Jacobian_box":[[".996","1.004"],[".96","1.04"],["-2.2e-6","2.2e-6"],[".959","1.041"]],
      "all_convex_average_Jacobians_determinant_lower":outward(det)[0],
      "inverse_Linf_gain_upper":outward(gain)[1],
      "z_error":"<1.091*(abs(du)+abs(dh)/sigma)",
      "w_error":"<2.31e-6*abs(du)+1.052*abs(dh)/sigma",
      "global_injectivity_on_real_half_rectangle":True,
      "requires_image_convex":False,"arbitrary_noisy_data_in_image_claimed":False,
      "U_uniform_upper":outward(ubound)[1],
      "actual_zero_phase":"theta=eta-eta_ref+Theta^-1(exp(-2U)-1)",
      "same_eta_phase_difference_upper":outward(phase_eta)[1],
      "same_proper_time_phase_difference_upper":outward(phase_proper)[1],
      "same_proper_time_domain":"same epsilon, both endpoints in half rectangle, common incoming proper origin",
      "ideal_observables":["u=log(a/A) from 3-curvature","h/sigma=a*H_proper/sigma"],
      "CP_geometry_instrument_constructed":False,"proof":"GEOMETRY.md"}
if __name__=="__main__":finish("geometry.py",result(),["GEOMETRY.md"])
