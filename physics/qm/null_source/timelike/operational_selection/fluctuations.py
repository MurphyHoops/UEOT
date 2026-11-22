"""Dynamic arbitrary-state QEI and complete-record constraint obstruction."""
from common import *
import sympy as sp
def result():
    assert above(SLOW,"1.99")
    # Reuse the complete fixed-prescription vacuum bound; no old checker runs.
    assert NORMS["geometry_ball_radius"]=="0.1"
    assert NORMS["all_fixed_contacts_zero_thermal_retained"]
    assert exact(NORMS["full_vacuum_density_bracket_upper"]).b<7
    assert exact(NORMS["sum_k_squared_over_omega_fifth_upper"]).b<exact("1.027").a
    assert above(X,"6e9") and below(X,"7e9")
    assert above(1/SIGMA,"1e-6")
    Cg=96*SIGMA**2+15*SIGMA+1
    assert below(Cg,"1e14")
    Cbar=exact("1e14");cut=5_000_000
    C5=(exact(4)/3)**2*iv.sqrt(exact(4)/3)
    low=2/iv.sqrt(3)*(exact(cut)*(cut+1)/2-1)
    tail=Cbar**2*C5/(32*cut**2)
    split=low+tail
    assert below(split,"4.1e13")
    r=exact(1)/5000
    Q= X*r*r*iv.exp(10*r)*exact("4.1e13")/(2*iv.pi**2)
    assert below(Q,"7e14")
    Gmax=exact(3)*X**2*iv.exp(4*r)*(1+r*r)/2
    # A uniform bound valid for every allowed branch; use safe Q rather than equality.
    cap=2/M2*(Gmax-U0*X**3*iv.exp(-6*r)+7*X*iv.exp(2*r)/(2*iv.pi**2)+exact("7e14"))
    pref=M2/(2*Gmax)
    assert below(cap,exact(36)/25) and above(pref,exact(581)/2500)
    high=1+iv.sqrt(3)/2
    assert above(high,exact(933)/500)
    lower=exact(123753)/(1250000*iv.sqrt(2))
    assert above(lower,".07")
    # Whole certified bound as a function of the E4 radius, not a metric-amplitude claim.
    table=[]
    for rtext in ["1e-25","0.0001","0.0002","0.001","0.005"]:
        rr=exact(rtext)
        qq=X*rr**2*iv.exp(10*rr)*exact("4.1e13")/(2*iv.pi**2)
        gg=exact(3)*X**2*iv.exp(4*rr)*(1+rr**2)/2
        cc=2/M2*(gg-U0*X**3*iv.exp(-6*rr)+7*X*iv.exp(2*rr)/(2*iv.pi**2)+qq)
        assert above(high-cc)
        ll=M2/(2*gg)*(high-cc)/iv.sqrt(2)
        table.append({"E4_radius":rtext,"Q_upper":outward(qq)[1],
            "capacity_upper":outward(cc)[1],"relative_RMS_lower":outward(ll)[0]})
    # KG identities for d=Y^2+omega^2*v^2, Y=v'-h*v.
    a,v,Y,h,w=sp.symbols("a v Y h omega")
    d=Y**2+w**2*v**2
    derivative=2*h*a*a*d+a*a*(2*Y*(-h*Y-w*w*v)+2*w*w*v*(Y+h*v))
    assert sp.expand(derivative-4*a*a*h*w*w*v*v)==0
    # Exact beta(3,3) sampler on [T/4,3T/4], then mollify inside (0,T).
    u=sp.symbols("u",real=True)
    beta=30*u**2*(1-u)**2
    assert sp.integrate(beta,(u,0,1))==1
    assert beta.subs(u,0)==beta.subs(u,1)==0
    assert sp.diff(beta,u).subs(u,0)==sp.diff(beta,u).subs(u,1)==0
    assert beta.subs(u,sp.Rational(1,2))==sp.Rational(15,8)
    crit=(3-sp.sqrt(3))/6
    assert sp.simplify(4*sp.diff(beta,u).subs(u,crit)-40*sp.sqrt(3)/3)==0
    assert below(160*iv.sqrt(3)/3,96)
    # Stable single-mode shift and the joint-spectral positive-part inequality.
    aa,bb,rr,yy,hh=sp.symbols("A B root y h",nonnegative=True)
    assert sp.expand((aa-rr)*(aa+rr)-(aa*aa-rr*rr))==0
    assert sp.expand((yy+hh)**2-yy**2)==2*yy*hh+hh**2
    # Neumann norm: (r+r^2)/s^2 <= r/3 throughout the old radius .1.
    assert below(exact("1.1")/exact("1.99")**2,exact(1)/3)
    return {
      "geometry_class":"positive-frequency analytic E4 histories with common incoming A; sample window in strict interior",
      "E4_radius": "1/5000",
      "reference":"same incoming Jost modes, full fixed two-field AE vacuum; arbitrary high state in normal-ordered form",
      "arbitrary_nonstationary_squeezed_entangled_high_states_allowed":True,
      "zero_high_state_product_required":False,
      "high_state_stationarity_required":False,
      "complete_input_S0_spectrum_preserved":True,"all_records_retained":True,
      "fixed_M2_U0_AE_required":True,"CQ_geometry_state_correlations_allowed":True,
      "sampler_support":"[T/8,7T/8], T=1/sigma, normalized smooth mollified beta(3,3)",
      "sampler_derivative_constant_upper":outward(Cg)[1],
      "two_frequency_B_bound":"abs(Bk)<=x*r*exp(4r)*min(1,Cg/(4*omega_k^2))",
      "split_cutoff":cut,"low_frequency_sum_upper":outward(low)[1],
      "high_frequency_sum_upper":outward(tail)[1],"split_sum_upper":outward(split)[1],
      "uniform_sum_chosen_upper":"4.1e13","Q_computed_upper":outward(Q)[1],"Q_chosen_upper":"7e14",
      "full_fixed_AE_vacuum_bracket_bound":7,
      "capacity_enclosure":outward(cap),"capacity_chosen_upper":"36/25",
      "source_over_constraint_scale":outward(pref),"chosen_prefactor_lower":"581/2500",
      "strict_complete_record_relative_RMS_lower":outward(lower),
      "RMS_definition":"sqrt(E_records omega[(integral g*a^6*(rho_bar-3*(1+h^2)/(2*a^2))/G_g)^2]), G_g=integral g*3*a^4*(1+h^2)/2",
      "ordinary_RMS_domain":"smeared residual second moment finite; otherwise extended nonnegative RMS",
      "strong_constraint_or_arbitrarily_small_RMS_in_this_domain_excluded":True,
      "mean_SCE_disproved":False,"all_possible_quantum_geometries_excluded":False,
      "metric_amplitude_or_geometric_RMS_claimed":False,"sharp_optimal_bound_claimed":False,
      "radius_dependence":table,"proof":"FLUCTUATIONS.md"}
if __name__=="__main__":finish("fluctuations.py",result(),["FLUCTUATIONS.md"])
