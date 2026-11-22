"""Independent rational safety margins and scope checks for all new certificates."""
from common import *
from fractions import Fraction as F
def result():
    cut=5_000_000;Cg=10**14
    split=F(20,17)*(F(cut*(cut+1),2)-1)+F(10*Cg**2,153*cut**2)
    assert split<F(41*10**12)
    r=F(1,5000)
    q=F(7*10**9)*r*r*F(101,100)*F(41*10**12)/18
    assert q<7*10**14
    xlo,xhi=map(F,CASE["x"])
    mlo=F(STATIC["fixed_original_M2"][0])
    ulo=F(HISTORY["fixed_U0"][0])
    G=F(3,2)*xhi*xhi*F(1250,1249)*(1+r*r)
    U=ulo*xlo**3*F(2497,2500)
    vacuum=F(7,18)*xhi*F(2500,2499)
    cap=2*(G-U+vacuum+7*10**14)/mlo
    pref=mlo/(2*G)
    assert cap<F(36,25) and pref>F(581,2500)
    margin=123753**2*10000-98*1250000**2
    assert margin==23050090000 and margin>0
    # Strict R+ > 933/500 follows by squaring sqrt(3)>433/250.
    assert F(433,250)**2<3
    det=F(996,1000)*F(959,1000)-F(104,100)*F(22,10**7)
    assert det>F(955,1000)
    # The raw square inequality fails if its positive part is dropped.
    y,h=F(-1),F(1)
    assert (y+h)**2<y*y
    docs=[json.loads((HERE/(name+".json")).read_text())
          for name in ["selector","geometry","clock","instrument","fluctuations"]]
    assert all(d["status"]=="PASS" for d in docs)
    sel,geom,clk,ins,fluc=docs
    assert not sel["full_covariance_and_analyticity_select_fast_amplitude"]
    assert geom["global_injectivity_on_real_half_rectangle"]
    assert not geom["CP_geometry_instrument_constructed"]
    assert clk["independent_repetitions_necessary_for_error_0_05"]==45
    assert not clk["repetitions_sufficient_claimed"]
    assert not clk["extra_copies_free_in_fixed_two_field_geometry"]
    assert not ins["local_gravitational_device_constructed"]
    assert not ins["pointer_and_interaction_stress_included_in_invariance_claim"]
    assert not fluc["high_state_stationarity_required"]
    assert not fluc["zero_high_state_product_required"]
    assert not fluc["mean_SCE_disproved"]
    assert fluc["E4_radius"]=="1/5000"
    def ratio(value):return {"numerator":str(value.numerator),"denominator":str(value.denominator)}
    return {
      "independent_arithmetic":"exact Fraction from frozen input endpoints; sqrt3>17/10, pi^2>9, elementary exp envelopes",
      "split_sum_rational_upper":ratio(split),"Q_rational_upper":ratio(q),
      "capacity_rational_upper":ratio(cap),"prefactor_rational_lower":ratio(pref),
      "RMS_squared_strict_margin_integer":margin,"Jacobian_determinant_rational_lower":ratio(det),
      "uncut_square_negative_control":True,"scope_flags_consistent":True,
      "native_research_review_agents":3,"external_human_peer_review":False,
      "analytic_proofs_fully_machine_formalized":False,
      "whole_unified_physics_goal":"OPEN","proof":"REVIEW.md"}
if __name__=="__main__":finish("review.py",result(),["REVIEW.md","selector.json","geometry.json","clock.json","instrument.json","fluctuations.json"])
