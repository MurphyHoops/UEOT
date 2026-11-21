"""Main review: same time weight, same quantum input, mode response and source fluctuations."""
from pathlib import Path
import json
from mpmath import mp

import anomaly
import noise
import parity
import plane_reference
import spectrum

HERE=Path(__file__).resolve().parent


def read(name):
    return json.loads((HERE/name).read_text())


def weights():
    # Independent weak volume measurement for the precise smooth QSEI sampler on the core clock.
    def calc(eta,which):
        x=8*eta-1
        d=1-x*x
        if d<=0:
            return mp.mpf(0)
        c=mp.cos(2*eta)
        a=mp.sqrt(3*c)
        w=mp.exp(2-2/d)
        log1=-4*x/d**2
        log2=-4/d**2-16*x**2/d**3
        if which=='volume':
            return -w*(64*(log2+log1**2)+8*mp.tan(2*eta)*log1)/a*(3*mp.log(c)/2)
        if which=='ricci':
            return a*w*2/c**3
        return 3*w*mp.tan(2*eta)**2/a
    out={k:mp.quad(lambda t:calc(t,k),[0,mp.mpf(1)/8,mp.mpf(1)/4]) for k in ('volume','ricci','expansion')}
    assert abs(out['volume']-out['ricci']-out['expansion'])<mp.mpf('1e-48')
    lo,hi=read('quantum/observed.json')['core']['unit_zero_mode_integral']
    assert 2*mp.mpf(lo)<out['ricci']<2*mp.mpf(hi)
    return {k:float(v) for k,v in out.items()}


def review():
    instrument=read('instrument/result.json')
    peer=read('identification/observed.json')['instrument']['bacon_comparison']
    assert all(v<1e-11 for rows in peer['max_cell_error_by_sign_axes'].values() for v in rows.values())
    assert abs(peer['weighted_commutator']-instrument['smooth']['retarded_pair'])<1e-11
    geom=read('geometry/result.json')
    h=sum(float(noise.Fraction(v)) for v in geom['vol_weak_H'])/2
    ratio=2*instrument['smooth']['central_weighted_SEC']/h
    assert ratio>28
    return dict(geometry_QSEI_common_sampler=weights(),central_induced_to_declared_volume=ratio,
                identical_input_probability_cells=2*4*4,
                absolute_plane=plane_reference.plane(),spacelike_monitor=plane_reference.monitor(),
                noise=noise.replay(),distributed=parity.main(),feedback=anomaly.main(),spectrum=spectrum.main())


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError("enable assertions")
    print(json.dumps(review(),indent=2))
