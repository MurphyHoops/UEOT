"""Distributed readout contract for a shell, with all-start parity and explicit transfer bounds."""
from itertools import product
import json
from pathlib import Path

import numpy as np
from mpmath import iv
from anomaly import interval,q

HERE=Path(__file__).resolve().parent


def logical_parity():
    # Independent local binary flips or unbiased replacements for missing outputs act on parity.
    means=[.98,.99,.97,.995]
    for coherence in (.3,-.4):
        joint=wrong=0.
        for original in product((1,-1),repeat=4):
            pr=(1+coherence*np.prod(original))/16
            for noise in product((1,-1),repeat=4):
                channel=np.prod([(1+m*n)/2 for m,n in zip(means,noise)])
                joint+=pr*channel*np.prod(original)*np.prod(noise)
            wrong+=pr*original[0]
        assert abs(joint-coherence*np.prod(means))<1e-14 and abs(wrong)<1e-14


def main():
    logical_parity()
    modes=json.loads((HERE/'instrument/result.json').read_text())
    shell=modes['offset']['aperture_cases']['complete_radial_shell']
    # Same smooth profile, isolated second gate; quadratic Gaussian log visibility vs dose.
    nominal=shell['v_strong']**.49
    assert .19 < nominal < .193
    t=iv.mpf([q('1.398').a,q('1.402').b])
    visibility=iv.mpf([q('.190').a,q('.193').b])
    transfer=iv.mpf([q('.79').a,q('.81').b])
    bias=iv.mpf([-1,1])*q('.001')
    chi=[iv.cos(t*iv.sqrt(3)/2),(2+iv.cos(3*t/2))/3]
    bands=[(1+visibility*transfer*c)/2+bias for c in chi]
    n=200000
    error=iv.sqrt(iv.ln(40)/(2*n))
    assert bands[0].b+error < bands[1].a-error
    rng=np.random.default_rng(74370119)
    counts=[]
    for i,c in enumerate([np.cos(1.4*np.sqrt(3)/2),(2+np.cos(2.1))/3]):
        plus=int(rng.binomial(n,(1+.8*nominal*c)/2))
        observed=q(plus)/n+iv.mpf([-1,1])*error
        assert not (observed>bands[i] or observed<bands[i])
        assert observed>bands[1-i] or observed<bands[1-i]
        counts.append(plus)
    # Six cube faces; a smooth cap partition, radius 2 sqrt(2)/m. Diameter is a sufficient design choice.
    m=160
    width=q('0.015625')+4*iv.sqrt(2)*iv.sin(q('0.3984375'))/m
    stations=6*m*m
    assert width<q('0.03125')
    return dict(dose=1.4,field_visibility_model=nominal,record_plus_bands=[interval(v) for v in bands],
                starts_per_candidate=n,synthetic_counts=counts,hoeffding_halfwidth=interval(error),
                example_station_count=stations,local_readouts_per_candidate=n*stations,
                equal_station_transfer_needed=interval(q('.79')**(q(1)/stations)),
                aperture_diameter_comoving_upper=interval(width)[1])


if __name__=="__main__":
    print(json.dumps(main(),indent=2))
