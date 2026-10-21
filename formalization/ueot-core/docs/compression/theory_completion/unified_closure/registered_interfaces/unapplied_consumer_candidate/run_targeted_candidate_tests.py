#!/usr/bin/env python3
"""Run only the new synthetic regression class from a temporary code copy.

No production import, source mutation, Lean, full FKRG suite or canonical gate.
The copied consumer is imported under its normal repository-relative layout.
"""
import ast
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory
import unittest

HERE = Path(__file__).resolve().parent
PREFIX = Path('formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse')
def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    consumer = HERE/'fkrg_reuse.py'
    tests = HERE/'test_fkrg_reuse.py'
    ast.parse(consumer.read_text(),filename=str(consumer))
    tree = ast.parse(tests.read_text(),filename=str(tests))
    classes = [node for node in tree.body if isinstance(node,ast.ClassDef)
               and node.name=='AdditiveHistoricalRepairTests']
    assert len(classes)==1
    for attempt in range(1,1000):
        logfile = HERE/f'targeted-attempt-{attempt}.log'
        if not logfile.exists():
            break
    with TemporaryDirectory(prefix='candidate-import-',dir=HERE) as directory:
        location = Path(directory)/PREFIX
        location.mkdir(parents=True)
        shutil.copyfile(consumer,location/'fkrg_reuse.py')
        spec = importlib.util.spec_from_file_location('synthetic_candidate_fkrg_reuse',location/'fkrg_reuse.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name]=module
        spec.loader.exec_module(module)
        namespace = {'unittest':unittest,'json':json,'Path':Path,'HERE':HERE,'reuse':module,
                     '__name__':'synthetic_candidate_tests'}
        isolated = ast.fix_missing_locations(ast.Module(body=classes,type_ignores=[]))
        exec(compile(isolated,str(tests),'exec'),namespace)
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(namespace['AdditiveHistoricalRepairTests'])
        with logfile.open('x') as stream:
            result = unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    status = {
        'status':'PASS_LOCAL_SYNTHETIC_REGRESSIONS_ONLY' if result.wasSuccessful() else 'FAIL_LOCAL_SYNTHETIC_REGRESSIONS',
        'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
        'test_class':'AdditiveHistoricalRepairTests',
        'log':logfile.name,'log_sha256':sha(logfile),
        'consumer_sha256':sha(consumer),'test_source_sha256':sha(tests),
        'production_modified':False,'candidate_applied_to_repository':False,
        'native_export_or_Lean_executed':False,'full_FKRG_tests_executed':False,
        'canonical_gate_satisfied':False,
        'scope':'Only the new synthetic test class, extracted unchanged from the candidate test AST, against a temporary byte-identical consumer copy. The historical integration class was not run.',
    }
    output=HERE/f'targeted-attempt-{attempt}.json'
    output.write_text(json.dumps(status,indent=2)+'\n')
    print(json.dumps(status,indent=2))
    if not result.wasSuccessful():
        raise SystemExit(1)

if __name__=='__main__':
    main()
