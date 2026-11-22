"""Same-metric source reversal and probe-input reversal, with an independent geodesic comparison."""
import cmath
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

HERE=Path(__file__).resolve().parent


def calibrated_phase(contrasts):
    corrected={}
    for sign,inputs in contrasts.items():
        # Each complex number contains separate ensemble X and Y contrasts.
        corrected[sign]=(inputs[1]-inputs[-1])/2
    a,b=corrected['+'],corrected['-']
    if min(abs(a),abs(b))<1e-12:
        raise ValueError("unresolved Ramsey visibility")
    return cmath.phase(a*b.conjugate())/2


def main():
    if not __debug__:
        raise RuntimeError("enable assertions")
    own=json.loads((HERE/'observed.json').read_bytes())
    geo=json.loads((HERE.parent/'geometry/result.json').read_bytes())['cases']
    bindings={}
    for name in ('baseline','minus','flat','improved','holdout_eighth'):
        g=geo[name]
        r=next(r for r in own['rows'] if r['A']==float(Fraction(g['physical_scalar_amplitude']))
               and r['xi']==float(Fraction(g['xi'])))
        endpoints=[g['full_transfer'][i] for i in (0,2)]
        for value,bounds in zip((r['p_exit'],r['p_prime_exit']),endpoints):
            assert Fraction(bounds[0]) <= Fraction(value) <= Fraction(bounds[1])
        bindings[name]=endpoints
    assert bindings['baseline']==bindings['minus']

    rows=own['rows'][:2]
    visibility=rows[0]['visibility']
    # An admissible binary readout for each axis: |bias_j| + gain <= 1.
    offset=.04-.03j
    gain, drift=.81,.37
    measured={}
    records=[]
    for sign,r in zip(('+','-'),rows):
        z=complex(*(2*r['probabilities'][basis][0]-1 for basis in ('X','Y')))
        measured[sign]={}
        for initial in (1,-1):
            m=offset+initial*gain*cmath.exp(1j*drift)*z
            measured[sign][initial]=m
            row=dict(source=sign,input_X=initial)
            for basis,c in zip(('X','Y'),(m.real,m.imag)):
                assert -1 <= c <= 1
                row[basis]=[(1+c)/2,(1-c)/2]
            records.append(row)
        assert abs((measured[sign][1]+measured[sign][-1])/2-offset)<1e-15
    theta=2*own['g']*rows[0]['mu']
    fixed=calibrated_phase(measured)
    naive=cmath.phase(measured['+'][1]*measured['-'][1].conjugate())/2
    assert abs(fixed-theta)<1e-14 and abs(naive-theta)>1e-3
    assert abs(math.sin(theta)*visibility-(rows[0]['probabilities']['Y'][0]-rows[1]['probabilities']['Y'][0]))<1e-14
    # Balanced +/- mixture is a centered same-stress state with non-Gaussian characteristic.
    mix_x=(rows[0]['probabilities']['X'][0]+rows[1]['probabilities']['X'][0])/2
    assert abs(mix_x-rows[0]['same_geometry_reference']['X'][0])>.005
    try:
        calibrated_phase({s:{1:offset,-1:offset} for s in ('+','-')})
    except ValueError:
        pass
    else:
        raise AssertionError("a phase was returned at zero contrast")
    print(json.dumps(dict(geometry_interval_matches=list(bindings),
                          geometry_scientific_intervals_sha256=hashlib.sha256(json.dumps(bindings,sort_keys=True).encode()).hexdigest(),
                          same_metric_source_signs=True,noise_visibility=visibility,injected_readout=dict(
                              gain=gain,common_phase=drift,bias_X=offset.real,bias_Y=offset.imag),
                          records=records,uncorrected_half_phase=naive,recovered_half_phase=fixed,
                          recovered_A=fixed/(2*own['g']*own['template_mean']),phase_modulus='pi',
                          centered_same_stress_mixture_X_plus=mix_x,centered_same_stress_mixture_Y_plus=.5,
                          reference_gaussian_X_plus=rows[0]['same_geometry_reference']['X'][0]),indent=2))


if __name__=='__main__':
    main()
