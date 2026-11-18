"""Executed structural negative controls, independent of sampled estimation."""
from __future__ import annotations
import math
from fractions import Fraction
from mpmath import mp
from common_c import BASE,dump_json,digest

mp.dps=70

def a(t):
    t=mp.mpf(t)
    return 4*(1-mp.cos(t)+mp.mpf(4)/25*(1-mp.cos(mp.mpf(3)/2*t)))

def main():
    t=mp.mpf(3)/2;lam=mp.mpf('0.3');eta=mp.mpf('.96');other=mp.mpf('.29')
    eta_other=eta*mp.exp(a(t)*(other**2-lam**2))
    residual=abs(eta*mp.exp(-a(t)*lam**2)-eta_other*mp.exp(-a(t)*other**2))
    assert mp.mpf('.9')<eta_other<1 and residual<mp.mpf('1e-60')
    wider_lam=mp.mpf('.25');occupation=mp.mpf('.22')
    assert (2*Fraction('.22')+1)*Fraction('.25')**2==Fraction('.3')**2
    thermal_residual=max(abs(mp.exp(-a(s)*lam**2)-mp.exp(-a(s)*(2*occupation+1)*wider_lam**2)) for s in ['.5','1','1.5','2'])
    tau=mp.mpf(2)/3;duration=mp.mpf(3)/4
    phase_coeff=4*sum((c/w)**2*(mp.sin(w*tau)+mp.sin(w*duration)-mp.sin(w*(tau+duration)))
                      for w,c in [(mp.mpf(1),mp.mpf(1)),(mp.mpf(3)/2,mp.mpf(3)/5)])
    shared_visibility=mp.exp(-a(duration)*lam**2)
    p_vac=(1-shared_visibility*mp.sin(phase_coeff*lam**2))/2
    p_thermal=(1-shared_visibility*mp.sin(phase_coeff*wider_lam**2))/2
    assert abs(p_vac-p_thermal)>mp.mpf('.02')
    out={'schema':'identifiability-negative-controls/1','source_sha256':digest(__file__),
         'single_nonzero_time':{'time':'3/2','lambda':'0.3','eta':'0.96','lambda_alternative':'0.29',
          'eta_alternative':mp.nstr(eta_other,30),'both_in_frozen_parameter_domain':True,'same_mean_residual':mp.nstr(residual,6),
          'conclusion':'NONIDENTIFIABLE_WITH_ONE_SETTING; exact equality follows algebraically, numerical residual is an execution check'},
         'unknown_thermal_extension':{'inside_frozen_vacuum_contract':False,'vacuum_lambda':'0.3','thermal_lambda':'0.25',
          'thermal_occupation_per_mode':'0.22','common_effective_lambda_squared':'0.09',
          'single_slot_max_residual':mp.nstr(thermal_residual,6),'causal_break_Yplus_probability_vacuum':mp.nstr(p_vac,30),
          'causal_break_Yplus_probability_thermal':mp.nstr(p_thermal,30),'gap':mp.nstr(abs(p_vac-p_thermal),30),
          'conclusion':'additional causal-break tester separates this declared extension; no silent extension of the executed source'},
         'status':'PASS_DECLARED_STRUCTURAL_NEGATIVE_CONTROLS'}
    dump_json(BASE/'IDENTIFIABILITY_NEGATIVE_CONTROLS.json',out)
    print(out['status'],mp.nstr(eta_other,16),mp.nstr(abs(p_vac-p_thermal),16))

if __name__=='__main__':main()
