#!/usr/bin/env python3
"""Generate explicitly synthetic calibration/holdout records, never real data.

Truth is written only to synthetic_provenance.json. The separate analyzer does
not open this file and does not accept a truth parameter.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, random
from certified_intervals import normal_half_axis_probability


def binary_draw(rng, bounds):
    """Dyadic uniform refinement against certified probability brackets.

    The Python PRNG is a reproducible synthetic device, not empirical proof of
    iid randomness. An unresolved arithmetic comparison aborts; no shot is
    silently removed.
    """
    lo,hi=bounds;word=0;bits=0
    for _ in range(4):
        word=(word<<64)|rng.getrandbits(64);bits+=64;den=1<<bits
        if (word+1)*lo.denominator <= lo.numerator*den:return '1'
        if word*hi.denominator >= hi.numerator*den:return '0'
    raise ArithmeticError("uniform refinement could not resolve probability enclosure")


def flag(rng):
    # q=1/2 and s=3/4, exact rational flag probabilities 3/8,3/8,1/4.
    u=rng.randrange(8)
    return '0' if u<3 else '1' if u<6 else 'f'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--plan',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    a=p.parse_args();plan=json.loads(a.plan.read_text());out=a.output_dir
    out.mkdir(parents=True,exist_ok=True)
    q=F(1,2);x=F(3,50)
    p_bounds=normal_half_axis_probability(x)
    rng=random.Random(plan['q_calibration']['seed'])
    (out/'q_calibration_flags.txt').write_text(''.join(flag(rng) for _ in range(plan['q_calibration']['shots']))+'\n')
    rng=random.Random(plan['drive_calibration']['seed'])
    (out/'drive_calibration_bits.txt').write_text(''.join(binary_draw(rng,p_bounds) for _ in range(plan['drive_calibration']['shots']))+'\n')
    n=plan['holdout']['shots_per_stream']
    rng=random.Random(plan['holdout']['source_seed']);rows=[]
    for _ in range(n):
        first=flag(rng);rows.append(first if first=='f' else first+flag(rng))
    (out/'source_holdout_records.txt').write_text('\n'.join(rows)+'\n')
    rng=random.Random(plan['holdout']['compiled_seed']);rows=[]
    for _ in range(n):
        first=str(rng.randrange(2));w=F(plan['policy']['after_'+first])
        second='1' if rng.randrange(w.denominator)<w.numerator else '0'
        rows.append(first+second)
    (out/'compiled_holdout_records.txt').write_text('\n'.join(rows)+'\n')
    rng=random.Random(plan['holdout']['drive_seed'])
    holdout_bounds=normal_half_axis_probability(plan['holdout']['drive_gate_calls']*x)
    (out/'drive_holdout_bits.txt').write_text(''.join(binary_draw(rng,holdout_bounds) for _ in range(n))+'\n')
    ctrl=plan['synthetic_nonshared_pulse_control']
    rng=random.Random(ctrl['seed'])
    drift_bounds=normal_half_axis_probability(plan['holdout']['drive_gate_calls']*(x+F(ctrl['per_call_area_drift'])))
    (out/'drive_holdout_drift_bits.txt').write_text(''.join(binary_draw(rng,drift_bounds) for _ in range(ctrl['shots']))+'\n')
    raw={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.glob('*.txt')}
    provenance={
        'classification':'SYNTHETIC_ONLY','new_hardware_data':False,
        'generating_truth':{'q':str(q),'x':str(x),'s':str(1-q/2)},
        'certified_generator_probability_interval':[str(v) for v in p_bounds],
        'holdout_drive_probability_interval':[str(v) for v in holdout_bounds],
        'nonshared_control_probability_interval':[str(v) for v in drift_bounds],
        'nonshared_control_is_explicitly_synthetic':True,
        'randomness':'Python random.Random with frozen independent stream seeds; not a measured randomness claim',
        'raw_record_order':'Character or line order is logical trial order, not physical timestamps',
        'seeds':{k:plan[k]['seed'] for k in ['q_calibration','drive_calibration']},
        'holdout_seeds':{k:plan['holdout'][k] for k in ['source_seed','compiled_seed','drive_seed']},
        'nonshared_control_seed':ctrl['seed'],
        'plan_sha256':hashlib.sha256(a.plan.read_bytes()).hexdigest(),
        'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'raw_sha256':raw,
        'not_supplied_to_analysis':'generating_truth and this provenance file',
        'actual_device_preparation_readout_pulse_membership':'UNVERIFIED',
    }
    (out/'synthetic_provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print(json.dumps({'classification':'SYNTHETIC_ONLY','raw_files':len(raw),'calibration_trials':plan['q_calibration']['shots']+plan['drive_calibration']['shots'],'holdout_trials':3*n,'nonshared_control_trials':ctrl['shots']}))


if __name__=='__main__':main()
