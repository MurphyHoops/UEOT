"""Verify the finite-conditioning increment against actual Lean and source bytes.

This runs the complete public package and the complete named axiom audit once.
Unchanged historical runtime/certificate witnesses are not silently rerun here.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

MODULES = (
    'QuantumFiniteWindow', 'QuantumFiniteWindowSpectral',
    'QuantumActionRealizability', 'QuantumReachableActionRealizability',
    'QuantumActionCounterexamples', 'QuantumActionPauliWitness',
    'QuantumInitializationCost', 'QuantumPostselectionError',
)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1; i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1; i += 2
        elif not depth and s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i] if depth == 0 or s[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('unclosed Lean comment')
    return ''.join(out)


def declarations(p):
    stack, result = [], []
    for line in strip_comments(p.read_text()).splitlines():
        line = line.strip()
        m = re.match(r'namespace\s+(\S+)$', line)
        if m:
            stack.append(('namespace', m[1])); continue
        if re.match(r'(?:noncomputable\s+)?section(?:\s+\S+)?$', line):
            stack.append(('section', '')); continue
        if re.match(r'end(?:\s+\S+)?$', line):
            if not stack:
                raise ValueError(f'unmatched end in {p}')
            stack.pop(); continue
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?'
                     r'(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([\w.\']+)', line)
        if m:
            prefix = '.'.join(name for kind, name in stack if kind == 'namespace')
            result.append({'name': prefix + '.' + m[2], 'kind': m[1]})
    if stack:
        raise ValueError(f'unclosed namespace/section in {p}')
    return result


def source_closure(package):
    repo = package.parents[1]
    pending = [package/'UEOTQM.lean']; found = {}
    while pending:
        p = pending.pop()
        key = p.relative_to(repo).as_posix()
        if key in found:
            continue
        if not p.is_file():
            raise FileNotFoundError(p)
        found[key] = {'path': key, 'sha256': digest(p), 'bytes': p.stat().st_size}
        for imports in re.findall(r'^import\s+([^\n]+)', strip_comments(p.read_text()), re.M):
            for module in imports.split():
                if module.startswith('UEOTQM.'):
                    pending.append(package/(module.replace('.', '/')+'.lean'))
                elif module.startswith('UEOT.'):
                    pending.append(repo/'formalization/ueot-core'/(module.replace('.', '/')+'.lean'))
    for name in ('lakefile.lean','lake-manifest.json','lean-toolchain','scripts/AxiomAudit.lean',
                 'scripts/check_dependencies.py','scripts/check_axioms.py','scripts/record_source.py',
                 'scripts/verify_finite_conditioning.py'):
        p=package/name;key=p.relative_to(repo).as_posix()
        found[key]={'path':key,'sha256':digest(p),'bytes':p.stat().st_size}
    return [found[k] for k in sorted(found)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    package=Path(__file__).resolve().parents[1]
    out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    before=source_closure(package)
    requested=re.findall(r'^#print axioms (\S+)$',(package/'scripts/AxiomAudit.lean').read_text(),re.M)
    root_imports=(package/'UEOTQM.lean').read_text()
    inventory={m:declarations(package/'UEOTQM'/f'{m}.lean') for m in MODULES}
    newnames=[d['name'] for ds in inventory.values() for d in ds]
    if len(newnames)!=len(set(newnames)) or len(requested)!=len(set(requested)):
        raise ValueError('duplicate declaration inventory/audit target')
    if not set(newnames)<=set(requested):
        raise ValueError('new source declarations absent from public audit: '+repr(set(newnames)-set(requested)))
    if not all(f'import UEOTQM.{m}' in root_imports for m in MODULES):
        raise ValueError('new module absent from public import root')
    for p in (package/'UEOTQM').glob('*.lean'):
        if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b',strip_comments(p.read_text()),re.M):
            raise ValueError('forbidden proof escape: '+str(p))
    gates=[]
    commands=[('dependencies',[sys.executable,'scripts/check_dependencies.py']),
              ('public_build',['lake','build','UEOTQM']),
              ('public_axioms',['lake','env','lean','scripts/AxiomAudit.lean'])]
    for name,cmd in commands:
        started=datetime.now(timezone.utc).isoformat();tic=time.monotonic()
        log=out/(name+'.log')
        with log.open('w') as stream:
            r=subprocess.run(cmd,cwd=package,stdout=stream,stderr=subprocess.STDOUT)
        gates.append({'name':name,'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-tic,
                      'started_at_utc':started,'log':log.name,'log_sha256':digest(log)})
        print(json.dumps({'gate':name,'exit_code':r.returncode,'seconds':gates[-1]['seconds']}),flush=True)
        if r.returncode:
            break
    audit={};audit_ok=False
    if len(gates)==3 and all(g['exit_code']==0 for g in gates):
        text=(out/'public_axioms.log').read_text()
        rows=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
        audit={n:sorted(a.strip() for a in aa.split(',') if a.strip()) for n,aa in rows}
        audit_ok=(set(audit)==set(requested) and len(rows)==len(audit)
                  and all(set(aa)<=ALLOWED for aa in audit.values()))
    after=source_closure(package)
    passed=(len(gates)==3 and all(g['exit_code']==0 for g in gates) and audit_ok and before==after)
    audit_result={'schema':'ueot_qm.axiom_audit.v1','status':'PASS' if audit_ok else 'FAILED',
                  'declaration_count':len(audit),'allowed_foundation':sorted(ALLOWED),'declarations':audit}
    (out/'proof-axioms.json').write_text(json.dumps(audit_result,indent=2)+'\n')
    source={'schema':'ueot_qm.recursive_scientific_inputs.v1','sources':before,'source_count':len(before),
            'source_set_sha256':hashlib.sha256(json.dumps(before,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
            'identity_unchanged_during_execution':before==after}
    (out/'source-manifest.json').write_text(json.dumps(source,indent=2)+'\n')
    (out/'new-declarations.json').write_text(json.dumps(inventory,indent=2)+'\n')
    public_files=sorted((package/'UEOTQM').glob('*.lean'))
    theorem_count=sum(len(re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+',
                                      strip_comments(p.read_text()),re.M)) for p in public_files)
    receipt={'schema':'ueot_qm.finite_conditioning_integration.v1','status':'PASS' if passed else 'FAILED',
             'recorded_at_utc':datetime.now(timezone.utc).isoformat(),'gates':gates,
             'public_modules':len(public_files),'public_explicit_theorems':theorem_count,
             'public_named_axiom_reports':len(audit),'new_modules':len(MODULES),
             'new_explicit_theorems':sum(d['kind']=='theorem' for ds in inventory.values() for d in ds),
             'new_named_axiom_reports':len(newnames),'new_names_all_audited':set(newnames)<=set(audit),
             'source_set_sha256':source['source_set_sha256'],'source_count':source['source_count'],
             'identity_unchanged_during_execution':before==after,'allowed_axioms_only':audit_ok,
             'new_hardware_data':False,'scope':'actual complete public Lean build and named audit; not validation of every book statement or Python implementation'}
    (out/'lean-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
