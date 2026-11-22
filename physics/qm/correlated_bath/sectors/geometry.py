"""Conditional weak-field comparison and a matched-background perturbation holdout."""
import json
import math
import numpy as np
from scipy.integrate import solve_ivp


def transfer(k, cs2, rtol):
    def rhs(loga, y):
        a=math.exp(loga)
        e2=.3/a**3+.7
        h=1-1.5*.3/a**3/e2
        return (y[1],-(3+h)*y[1]-(2*h+1+cs2*k*k/(a*a*e2))*y[0])
    s=solve_ivp(rhs,(math.log(1e-5),0),(1,0),rtol=rtol,atol=rtol*1e-3,method="DOP853")
    assert s.success
    return float(s.y[0,-1])


def main():
    for a in (.01,.1,.3,.7,1):
        u=math.asinh(math.sqrt(.7/.3)*a**1.5)
        kinetic=.7/(2*math.sinh(u)**2)
        phi=2/math.sqrt(3)*math.log(math.tanh(u/2))
        potential=.7*(1+.5*math.sinh(math.sqrt(3)*phi/2)**2)
        assert abs((kinetic+potential)/(.3/a**3+.7)-1)<2e-12
        assert abs(kinetic-potential+.7)<2e-9
    results={}
    for k in (0,5,20):
        result=[]
        for cs2 in (0,1):
            coarse=transfer(k,cs2,1e-8)
            fine=transfer(k,cs2,1e-11)
            assert abs(coarse-fine)<1e-7
            result.append(fine)
        results[k]=result
    assert abs(results[0][0]-results[0][1])<1e-10 and abs(results[20][1])<.01*results[20][0]
    lim=(1-1/3)/(1+1/3)
    obs=[1+2.1e-5-3*2.3e-5,1+2.1e-5+3*2.3e-5]
    assert obs[0]<1<obs[1] and lim<obs[0]
    print(json.dumps(dict(frozen_Omega_dust=.3,initial_a=1e-5,Phi_initial=1,dPhi_dloga_initial=0,
        k_over_H0_to_today_Phi_dust_scalar=results,Cassini_central_plusminus_3_reported_errors=obs,
        unscreened_constant_slip_long_range_limit=lim),indent=2))


if __name__=="__main__":
    main()
