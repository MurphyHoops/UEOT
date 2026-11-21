"""Reproduce the new dynamic certificates and record their exact scope.

Unchanged source inputs are compared with the reviewed predecessor. Each entry
runs in its own process so numerical contexts and proof state cannot leak.
Large finite-mode output goes to logs; the visible result is a compact ledger.
"""
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE='987dd4ccc58d0086cc1305e99b5cdb67f8127fde'
INPUTS=[
    'physics/qm/null_source/FINITE_WINDOW.md',
    'physics/qm/null_source/timelike/instrument/instrument.py',
    'physics/qm/null_source/timelike/identification/reference.py',
    'physics/qm/null_source/timelike/continuation/SOURCE.md',
    'physics/qm/null_source/timelike/continuation/quantum/minimal_response.py',
    'physics/qm/status/CURRENT.json',
    'formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean',
]
ENTRIES=[
    ('independent_local_algebra',['review_algebra.py','--check']),
    ('validated_modes_2_to_64',['propagation/finite_modes.py','--check']),
    ('validated_initial_modes_65_to_256',['propagation/extra_eta0.py','--check']),
    ('independent_physical_propagation_diagnostic',['propagation/crosscheck.py','--check']),
    ('ultraviolet_certificate_64',['stress/tail.py','--K','64','--mesh','1024','--check']),
    ('ultraviolet_certificate_256',['stress/tail.py','--K','256','--mesh','1024','--check']),
    ('full_dynamic_stress_and_initial_constraint',['stress/assemble.py','--check']),
    ('finite_window_coupling_identification',['inference/check.py','--check']),
    ('independent_propagation_and_infinite_field_review',['inference/review_bc.py','--check']),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest():
    return {str(p.relative_to(REPO)):sha(p) for p in sorted(HERE.rglob('*'))
            if p.is_file() and p.suffix in ('.py','.json','.md')
            and p.name!='verification.json' and '__pycache__' not in p.parts}


def decimal_lower(q,digits=10):
    scale=10**digits
    n=q.numerator*scale//q.denominator
    return f'{n//scale}.{n%scale:0{digits}d}'


def run(logs):
    if not __debug__:
        raise RuntimeError('Verification requires assertions; do not use -O')
    inherited={}
    for rel in INPUTS:
        old=subprocess.run(['git','show',f'{BASE}:{rel}'],cwd=REPO,
                           check=True,capture_output=True).stdout
        now=(REPO/rel).read_bytes()
        if now!=old:
            raise RuntimeError(f'Declared source changed since reviewed base: {rel}')
        inherited[rel]=hashlib.sha256(now).hexdigest()
    before=manifest()
    logs.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
    results=[]
    for name,args in ENTRIES:
        start=time.monotonic()
        proc=subprocess.run([sys.executable,'-B',str(HERE/args[0]),*args[1:]],
                            cwd=REPO,env=env,capture_output=True,text=True)
        out=logs/f'{name}.stdout.log';err=logs/f'{name}.stderr.log'
        out.write_text(proc.stdout);err.write_text(proc.stderr)
        row={'entry':name,'returncode':proc.returncode,
             'duration_seconds':round(time.monotonic()-start,3),
             'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
        results.append(row)
        if proc.returncode:
            print(proc.stdout[-5000:]);print(proc.stderr[-5000:],file=sys.stderr)
            raise RuntimeError(f'Failed {name}; complete logs: {logs}')
        print(f'PASS {name} ({row["duration_seconds"]} s)',flush=True)
    if manifest()!=before:
        raise RuntimeError('Research input changed during verification; freeze and rerun')
    for rel,digest in inherited.items():
        if sha(REPO/rel)!=digest:
            raise RuntimeError(f'Inherited input changed during verification: {rel}')
    stress=json.loads((HERE/'stress/result.json').read_text())
    strong=next(r for r in stress['initial_energy_certificates'] if r['finite_K']==256)
    lower=Fraction(strong['selected']['rho_full_lower_bound'][0])
    if not lower>Fraction(1,2):
        raise RuntimeError('The claimed initial-constraint rejection is not certified')
    return {
        'schema':'ueot-dynamic-source-verification/1',
        'timestamp_utc':datetime.now(timezone.utc).isoformat(),
        'reviewed_base':BASE,
        'git_head_at_execution':subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
        'python':sys.version,'entries':results,'logs_directory':str(logs),
        'inherited_inputs_unchanged':inherited,'current_source_manifest':before,
        'initial_constraint_consequence':{
            'background':'declared finite-source interior a0^2=3, Kij=0',
            'units':'4*pi*G=1; hbar=1; declared source length scale',
            'scheme':'Anderson_Eaker_mu1_no_extra_finite_curvature_terms',
            'quantum_density_lower_exact':str(lower),
            'quantum_density_lower_decimal_downward':decimal_lower(lower),
            'classical_density':'1/2','required_total_density':'1/2',
            'quantum_to_classical_ratio_lower_exact':str(2*lower),
            'Gnn_minus_2_total_density_upper_exact':str(-2*lower),
            'alpha_upper_if_added_alpha_H1_cancels_original_density_residual':str(-lower/6),
            'curvature_coupling_can_change_single_point_verdict':True,
            'is_a_new_self_consistent_solution':False,
        },
        'dynamic_point_RSET_enclosures':'CERTIFIED_BUT_WIDE',
        'useful_initial_density_lower_bound':'CERTIFIED',
        'finite_window_identification':'CONDITIONAL_ON_DECLARED_SOURCE_AND_GEOMETRY_DATA',
        'precise_pressure_and_window_reference_integrals':'OPEN',
        'full_self_consistent_backreaction':'OPEN',
        'geometry_apparatus_calibration':'OPEN',
        'Core_unique_physical_selection':'OPEN',
        'new_Lean_proofs':False,'new_matching_hardware_data':False,
        'whole_unified_physics_goal':'OPEN',
    }


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--logs',type=Path)
    args=parser.parse_args()
    logs=args.logs or Path(tempfile.mkdtemp(prefix='ueot-dynamic-verification-'))
    result=run(logs)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(f'Saved {args.output}')
    else:
        print(json.dumps(result,indent=2,ensure_ascii=False))
