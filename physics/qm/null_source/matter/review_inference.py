"""Independent audit of the four-frame and Ramsey menu, using only reported summaries."""
from math import cos, log, sin, sqrt

import numpy as np
from scipy.integrate import quad, solve_ivp


def check(pulse, slope, receipt):
    b,d,gain=1.001,-.002,1.013
    mean=quad(lambda t:pulse(b*t+d),-.1,.1,epsabs=1e-14)[0]/.2
    commands=[.25,-.25,-.375]
    trials=[131072,131072,65536]
    successes=receipt["calibration"]["matter_plus_counts"]+[receipt["held"]["matter_plus"]]
    frac=.005  # Maxwell share in Tuu; one common source splitting for every command
    control=.64
    def probability(c,s):
        return (1+sin(c*sqrt(1-s)*mean))/2
    shifts=[probability(c,frac)-probability(c,0) for c in commands]
    assert max(map(abs,shifts)) < .001
    # Wide physical gate: both quadratures have slope at most 1/2 in phase.
    # The covariance and visibility are shared on the same geometry.
    wide_bound=.5*1.002*1.002*max(map(abs,commands))*(1-sqrt(1-frac))*32/35
    assert b<1.002 and wide_bound<.001
    for c,n,k in zip(commands,trials,successes):
        r=sqrt(log(2*12/.05)/(2*n))+.001
        assert abs(k/n-probability(c,frac))<r
        assert abs(k/n-probability(c,control))>r

    times=np.array([-.30,-.25,.25,.30])
    def observed_frames(s):
        def rhs(t,y):
            u=b*t+d
            flux=(commands[2]*slope(u))**2
            tide=(flux*(1-s)+flux*s)*np.eye(2)
            tide+=np.array([[.055*cos(3*u),.040*sin(4*u)],[.040*sin(4*u),-.055*cos(3*u)]])
            j,v=y.reshape(2,2,2)
            return np.stack([v,-b*b*tide@j]).ravel()
        y0=np.r_[np.eye(2).ravel(),np.zeros(4)]
        sol=solve_ivp(rhs,times[[0,-1]],y0,t_eval=times,method="RK45",rtol=1e-12,atol=1e-14)
        assert sol.success
        return gain*sol.y[:4].T.reshape(4,2,2)

    frames=observed_frames(frac)
    np.testing.assert_allclose(frames,observed_frames(0),rtol=0,atol=2e-13)
    y=-np.trace(frames[3]-frames[2]-frames[1]+frames[0])/.1
    low,high=receipt["verdict"]["held_geo_interval"]
    assert low<y<high and receipt["verdict"]["geometry_outcome"]=={"minimal":"compatible","improved":"rejected"}
    return dict(scalar_Ramsey_mean_profile=mean, Maxwell_flux_share=frac,
                signed_probability_shifts=shifts, held_geometry=float(y),
                wide_either_axis_absolute_shift_bound=wide_bound,
                counterexample_Maxwell_share_rejected_by_known_Ramsey=control)

# Inputs to this audit only: archived counts and verdict, not a snapshot of peer files.
SUMMARY = {"calibration":{"matter_plus_counts":[81836,49598]},
           "held":{"matter_plus":20773},
           "verdict":{"held_geo_interval":[.008152050394387794,.009250147657119265],
                      "geometry_outcome":{"minimal":"compatible","improved":"rejected"}}}


if __name__=="__main__":
    import json
    from pathlib import Path
    from replay import pulse,slope
    record=json.loads((Path(__file__).resolve().parents[1]/"inference/result.json").read_text())
    assert check(pulse,slope,record)==check(pulse,slope,SUMMARY)
    pair=json.loads((Path(__file__).resolve().parents[1]/"probe/pair_observed.json").read_text())
    theta=.25*quad(lambda t:(1-t*t)**3*pulse(t),-1,1,epsabs=1e-14)[0]
    visibility=pair["noise_visibility"]
    plus_minus=[(1+visibility*np.array([cos(t),sin(t)]))/2 for t in [theta,-theta]]
    centered=np.mean(plus_minus,axis=0)
    np.testing.assert_allclose(centered,[pair["centered_same_stress_mixture_X_plus"],
                               pair["centered_same_stress_mixture_Y_plus"]],rtol=0,atol=1e-13)
    assert abs(centered[0]-pair["reference_gaussian_X_plus"])>.009
    print("PASS: four frames, signed counts, wide-window bound and centered X/Y mixture",centered)
