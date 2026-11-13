#!/usr/bin/env python3
"""Independent integer/readback checks for the root's interval output artifact.

The outward-arithmetic and Taylor proof is reviewed separately. This verifier
checks exact encoded states, aggregation, consumed identities and declared
domain; it does not replace the interval propagation by a floating oracle.
"""
from datetime import datetime, timezone
from fractions import Fraction as F
import argparse
import hashlib
import json
import math
from pathlib import Path


def identity(path):
    raw=path.read_bytes()
    return {'path':str(path),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}


def verify(artifact, predictor):
    x=json.loads(artifact.read_text());checks=[]
    def check(name,ok,detail=None):
        checks.append({'name':name,'status':'PASS' if bool(ok) else 'FAIL','detail':detail})
    nominal=F(x['nominal_x']);k=x['Galerkin_K'];degree=x['Taylor_degree']
    check('frozen predictor domain',k==4175 and degree==100 and abs(nominal)<=F(1,10))
    check('source norm bound',4*nominal*nominal*(k+1)<=F(13)**2)
    rem=F(13)**101/F(math.factorial(101))/(1-F(13,102))
    check('Taylor tail exact rational identity',rem==F(x['one_gate_Taylor_remainder_upper']))
    expected_q={'00':F(313,1250),'01':F(312,1250),'10':F(312,1250),'11':F(313,1250)}
    rows=x['records'];check('all four accepted records',set(r['word'] for r in rows)==set(expected_q) and len(rows)==4)
    check('all required zero-mass records retained',set(x['zero_mass_records'])=={'f','0f','1f','prep_fail'})
    total=F(0)
    for r in rows:
        word=r['word'];amps=r['amplitudes'];keys=[tuple(a[:3]) for a in amps]
        norm=sum(int(a[3])**2+int(a[4])**2 for a in amps)
        check(word+' nonzero exact normalization',norm>0 and norm==int(r['sum_abs_integer_squared']))
        check(word+' unique amplitude coordinates',len(set(keys))==len(keys))
        check(word+' valid finite system/reference coordinates',all(a[0] in ['g','e'] and isinstance(a[1],int) and 0<=a[1]+(a[0]=='e')<=k and a[2] in [0,1] for a in amps))
        check(word+' exact rational policy weight',F(r['Q'])==expected_q[word])
        radius=F(r['interval_radius_upper']);err=F(r['normalized_state_trace_distance_upper'])
        check(word+' nonnegative interval radius',radius>=0)
        vector=(1+rem)**word.count('1')-1+radius
        check(word+' vector-error aggregation',vector==F(r['unit_vector_error_upper']))
        check(word+' normalized-state conversion',err==min(F(1),2*vector))
        total+=F(r['Q'])*err
    check('complete Q aggregation exact',total==F(x['complete_CQ_numerical_error_upper']))
    check('numerical reservation achieved',total<F(x['reserved_budget'])==F(1,10**8))
    check('predictor source matches executed source',identity(predictor)['sha256']==x['script_sha256'])
    binding=x.get('calibration_identity')
    if binding:
        cp=Path(binding['path']);current=identity(cp)
        check('consumed calibration identity retained',current['sha256']==binding['sha256'],
              {'bound':binding,'current':current})
        cal=json.loads(cp.read_text())
        check('nominal comes from calibration artifact',F(cal['nominal_x'])==nominal)
    return {'schema':'ueot-qm.a-interval-output-readback/1',
            'status':'PASS' if all(c['status']=='PASS' for c in checks) else 'IDENTITY_OR_OUTPUT_MISMATCH',
            'checked_at_utc':datetime.now(timezone.utc).isoformat(),
            'checker_author':'native research agent A',
            'artifact':identity(artifact),'predictor_source':identity(predictor),
            'checker_source':identity(Path(__file__)),
            'checks':checks,'check_count':len(checks),
            'complete_CQ_numerical_error_upper':str(total),
            'scope':'exact encoded-state, error-aggregation and source/consumed-input identity checks; outward interval proof is a separate source review',
            'new_hardware_data':False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--artifact',type=Path,required=True)
    p.add_argument('--predictor',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=verify(a.artifact,a.predictor)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({'status':r['status'],'checks':r['check_count'],
                      'failed':[x['name'] for x in r['checks'] if x['status']=='FAIL']}))
    if r['status']!='PASS':raise SystemExit(1)


if __name__=='__main__':main()
