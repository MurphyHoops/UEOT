#!/usr/bin/env python3
"""Exact check of the new standard-QM teaching example in section 0.11.

This checks ideal finite matrices, not hardware data or a UEOT-specific mechanism.
The external-reader case demonstrates why inverse control must include every copy.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform

import sympy as s


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cnot(n, control, target):
    out = s.zeros(2**n)
    for col in range(2**n):
        row = col ^ ((1 << (n-1-target)) if (col >> (n-1-control)) & 1 else 0)
        out[row, col] = 1
    return out


def reduced_first(psi, n):
    return s.Matrix(2, 2, lambda i, j: s.simplify(sum(
        psi[i*2**(n-1)+k] * s.conjugate(psi[j*2**(n-1)+k])
        for k in range(2**(n-1)))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    h = s.Matrix([[1,1],[1,-1]]) / s.sqrt(2)
    z2 = s.Matrix([1,0,0,0])
    u2 = cnot(2,0,1)*s.kronecker_product(h,s.eye(2))
    bell = u2*z2
    rho = bell*bell.adjoint()
    z3 = s.Matrix([1,0,0,0,0,0,0,0])
    write12 = cnot(3,0,1)*s.kronecker_product(h,s.eye(4))
    copy_reader = cnot(3,1,2)
    full_write = copy_reader*write12
    ghz = full_write*z3
    incomplete_reverse = write12.adjoint()*ghz
    checks = {
        'H_unitary': h.adjoint()*h == s.eye(2),
        'two_qubit_write_unitary': s.simplify(u2.adjoint()*u2) == s.eye(4),
        'Bell_state_exact': bell == s.Matrix([1,0,0,1])/s.sqrt(2),
        'global_density_pure': s.simplify(rho*rho-rho) == s.zeros(4),
        'local_density_I_over_2': reduced_first(bell,2) == s.eye(2)/2,
        'complete_two_qubit_inverse_returns_00': s.simplify(u2.adjoint()*bell) == z2,
        'reader_copies_GHZ_record': ghz == s.Matrix([1,0,0,0,0,0,0,1])/s.sqrt(2),
        'inverse_ignoring_reader_fails_to_restore_000': s.simplify(incomplete_reverse) != z3,
        'ignored_reader_leaves_system_I_over_2': reduced_first(incomplete_reverse,3) == s.eye(2)/2,
        'full_three_qubit_inverse_returns_000': s.simplify(full_write.adjoint()*ghz) == z3,
    }
    assert all(checks.values()), checks
    book = Path(__file__).resolve().parents[1]
    receipt = {'schema':'ueot_physics.record_example_check.v1', 'status':'PASS',
               'executed_at_utc':datetime.now(timezone.utc).isoformat(),
               'arithmetic':'exact SymPy algebra with sqrt(2)', 'python':platform.python_version(),
               'sympy':s.__version__, 'script_sha256':sha(Path(__file__)),
               'section':'0.11', 'source_sha256':{name:sha(book/name) for name in
                   ['UEOT_PHYSICS.md','UEOT_PHYSICS.en.md']},
               'checks':checks, 'new_hardware_data':False,
               'scope':'Ideal standard quantum circuits only; no experimental validation, general record-reversal theorem, or new actualization law is claimed.'}
    args.output.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'checks':len(checks),'output':str(args.output)}))


if __name__ == '__main__':
    main()
