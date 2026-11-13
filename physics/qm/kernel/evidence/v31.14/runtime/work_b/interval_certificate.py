"""Outward interval enclosure for the frozen infinite-bath Choi representation.

This uses mpmath's interval arithmetic, not a comparison of two floating solvers.
The exported exact dyadic endpoints and stored binary64 matrices identify the
represented linear map. The bound does not certify subsequent arbitrary-input
floating contractions, nor a physical device, nor physicality of rounded Choi.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from mpmath import iv, mp

import dynamics


def rational(value):
    f = Fraction(value)
    return iv.mpf(f.numerator) / f.denominator


def zero_matrix(n=2):
    return [[iv.mpc(0) for _ in range(n)] for _ in range(n)]


def eye(n=2):
    a = zero_matrix(n)
    for i in range(n):
        a[i][i] = iv.mpc(1)
    return a


def multiply(a, b):
    n = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(n)), iv.mpc(0))
             for j in range(n)] for i in range(n)]


def conjugate(z):
    return iv.mpc(z.real, -z.imag)


def interval_history(lam, times, signs):
    omega, c = (rational(1), rational('3/2')), (rational(1), rational('3/5'))
    beta = [iv.mpc(0), iv.mpc(0)]
    phase = iv.mpf(0)
    for t, sign in zip(times, signs):
        for k in range(2):
            angle = omega[k] * t
            rot = iv.mpc(iv.cos(angle), -iv.sin(angle))
            alpha = sign * lam * c[k] / omega[k] * (rot - 1)
            beta_rot = rot * beta[k]
            phase += (lam * c[k] / omega[k]) ** 2 * (angle - iv.sin(angle))
            phase += (alpha * conjugate(beta_rot)).imag
            beta[k] = beta_rot + alpha
    return beta, phase


def interval_choi(lam_fraction, decimal_precision=80, times_rational=('2/3','3/4','1/2')):
    iv.dps = decimal_precision
    mp.dps = decimal_precision + 30
    lam = rational(lam_fraction)
    if len(times_rational) != 3:
        raise ValueError('three slots are required for this interval contract')
    times = [rational(x) for x in times_rational]
    sq2, sq3 = iv.sqrt(2), iv.sqrt(3)
    ry = [[1 / sq2, -1 / sq2], [1 / sq2, 1 / sq2]]
    rx = [[sq3 / 2, iv.mpc(0, -rational('1/2'))],
          [iv.mpc(0, -rational('1/2')), sq3 / 2]]
    rotations = (ry, rx, eye())
    p, f = zero_matrix(), zero_matrix()
    p[0][0], p[1][1] = iv.sqrt(rational('7/8')), iv.sqrt(rational('3/4'))
    f[0][0], f[1][1] = iv.sqrt(rational('1/8')), rational('1/2')
    result = {}
    for stop in range(4):
        count = min(stop + 1, 3)
        label = 'p' * stop + 'f' if stop < 3 else 'ppp'
        kraus = [multiply(rotations[j], p) for j in range(stop)]
        if stop < 3:
            kraus.append(f)
        histories = []
        for indices in itertools.product((0, 1), repeat=count):
            op = eye()
            for k, idx in enumerate(indices):
                proj = zero_matrix()
                proj[idx][idx] = iv.mpc(1)
                op = multiply(multiply(kraus[k], proj), op)
            beta, phase = interval_history(lam, times[:count], [1 if i == 0 else -1 for i in indices])
            # (op tensor I)|Bell> = vec(op)/sqrt(2), with (S,R) row order.
            vector = [op[a][r] / sq2 for a in range(2) for r in range(2)]
            histories.append((vector, beta, phase))
        block = zero_matrix(4)
        for vec, beta, phase in histories:
            for vecp, betap, phasep in histories:
                realpart = iv.mpf(0)
                imagpart = phase - phasep
                for k in range(2):
                    realpart -= (beta[k].real ** 2 + beta[k].imag ** 2
                                 + betap[k].real ** 2 + betap[k].imag ** 2) / 2
                    dot = conjugate(betap[k]) * beta[k]
                    realpart += dot.real
                    imagpart += dot.imag
                influence = iv.exp(realpart) * iv.mpc(iv.cos(imagpart), iv.sin(imagpart))
                for a in range(4):
                    for b in range(4):
                        block[a][b] += influence * vec[a] * conjugate(vecp[b])
        result[label] = block
    return result


def raw_interval(value):
    # mpmath raw tuples denote exact dyadic endpoints: (-1)^sign * man * 2^exp.
    return [[int(part) for part in endpoint] for endpoint in value._mpi_]


def display_upper(value):
    return mp.nstr(mp.mpf(value._mpi_[1]), 30)


def _pair_add(z,w):
    return (z[0]+w[0],z[1]+w[1])


def _pair_scale(z,a):
    return (z[0]*a,z[1]*a)


def _pair_conj(z):
    return (z[0],-z[1])


def rational_physical_repair(floating):
    """Exact rational CP/TP completion, justified by the preceding 1e-12 bound.

    The raw map need not be positive. The proof in B_DYNAMICS_PROOF.md derives
    positivity and residual positivity using operator norm perturbation bounds.
    """
    delta, eps = Fraction(1,10**10), Fraction(1,10**12)
    scale = 1/(1+20*delta)
    zero = (Fraction(0),Fraction(0))
    raw={}
    for label,block in floating.items():
        q=[[(Fraction.from_float(float(block[i,j].real)),
             Fraction.from_float(float(block[i,j].imag))) for j in range(4)] for i in range(4)]
        raw[label]=[[_pair_scale(_pair_add(q[i][j],_pair_conj(q[j][i])),Fraction(1,2))
                     for j in range(4)] for i in range(4)]
    repaired={}
    for label,q in raw.items():
        repaired[label]=[[_pair_scale(_pair_add(q[i][j],(delta if i==j else Fraction(0),Fraction(0))),scale)
                           for j in range(4)] for i in range(4)]
    marginal=[[zero for _ in range(2)] for _ in range(2)]
    for block in repaired.values():
        for i in range(2):
            for j in range(2):
                marginal[i][j]=_pair_add(marginal[i][j],_pair_add(block[i][j],block[i+2][j+2]))
    residual=[[_pair_add((Fraction(1,2) if i==j else Fraction(0),Fraction(0)),
                        _pair_scale(marginal[i][j],-1)) for j in range(2)] for i in range(2)]
    for i in range(2):
        for j in range(2):
            repaired['f'][i][j]=_pair_add(repaired['f'][i][j],residual[i][j])
    # Exact Hermiticity and trace preservation, no floating eigenvalue assertion.
    for block in repaired.values():
        assert all(block[i][j]==_pair_conj(block[j][i]) for i in range(4) for j in range(4))
    for i in range(2):
        for j in range(2):
            actual=zero
            for block in repaired.values():
                actual=_pair_add(actual,_pair_add(block[i][j],block[i+2][j+2]))
            assert actual==(Fraction(1,2) if i==j else Fraction(0),Fraction(0))
    repair_bound=(40*delta+eps+20*delta*eps)/(1+20*delta)
    total_bound=(40*delta+2*eps)/(1+20*delta)
    assert total_bound < Fraction(1,10**8)
    encoded={label:[[[str(z[0]),str(z[1])] for z in row] for row in block]
             for label,block in repaired.items()}
    return {
        'status':'EXACT_RATIONAL_COMPLETELY_POSITIVE_TRACE_PRESERVING_INSTRUMENT',
        'delta':str(delta),'scale':str(scale),'added_residual_record':'f',
        'no_new_record':True,
        'basis_order':'(output S,input reference)=(0,0),(0,1),(1,0),(1,1)',
        'exact_trace_preservation_checked':True,'exact_Hermiticity_checked':True,
        'positivity_basis':'interval raw error <=1e-12 gives ||Jraw-Jexact||op<=5e-13<delta and marginal error<delta; analytic positivity proof',
        'raw_to_repaired_half_diamond_upper_exact':str(repair_bound),
        'exact_source_to_repaired_half_diamond_upper_exact':str(total_bound),
        'certified_half_diamond_rational_upper':'1/100000000',
        'raw_sum_choi_trace_norm_error_upper':'1/1000000000000',
        'residual_exact_fraction_pairs':[[[str(z[0]),str(z[1])] for z in row] for row in residual],
        'scope':'fixed-policy terminal CQ instrument; no claim to repair a complete multi-time process tensor for every intervention',
        'choi_blocks_exact_fraction_pairs':encoded,
    }


def certificate(lam_fraction='3/10', decimal_precision=80,
                times_rational=('2/3','3/4','1/2'), backend='weyl', cutoff=20):
    f = Fraction(lam_fraction)
    if not Fraction(1, 5) <= f <= Fraction(2, 5):
        raise ValueError('lambda outside frozen interval')
    intervals = interval_choi(f, decimal_precision, times_rational)
    ts=[float(Fraction(x)) for x in times_rational]
    if backend=='weyl':
        floating = dynamics.exact_output(float(f),times=ts)
    elif backend=='galerkin':
        floating = dynamics.galerkin_output(float(f),times=ts,cutoff=cutoff)
    else:
        raise ValueError('backend must be weyl or galerkin')
    error = iv.mpf(0)
    exported = {}
    for label, block in intervals.items():
        square = iv.mpf(0)
        entries = []
        for a in range(4):
            row = []
            for b in range(4):
                approx = complex(floating[label][a, b])
                delta = block[a][b] - iv.mpc(approx.real, approx.imag)
                # Interval absolute values include both endpoint directions.
                square += abs(delta.real) ** 2 + abs(delta.imag) ** 2
                row.append({'real': raw_interval(block[a][b].real),
                            'imag': raw_interval(block[a][b].imag),
                            'stored_binary64_real_hex': approx.real.hex(),
                            'stored_binary64_imag_hex': approx.imag.hex()})
            entries.append(row)
        # d_in/2 * sqrt(d_out*d_in) = 2 for normalized qubit Choi blocks.
        error += 2 * iv.sqrt(square)
        exported[label] = entries
    rational_upper = rational('1/1000000000000')
    if not mp.mpf(error._mpi_[1]) < mp.mpf(rational_upper._mpi_[0]):
        raise ArithmeticError('Numerical interval failed the frozen 1e-12 bound')
    cutoff_bounds = {}
    x = rational('2/5') * rational('23/12') * iv.sqrt(rational('34/25'))
    for cutoff_probe in (8, 12, 16, 20, 24):
        order = cutoff_probe + 1
        b = 2 * x ** order / math.factorial(order)
        for k in range(1, order + 1):
            b *= iv.sqrt(k - 1) + iv.sqrt(k)
        cutoff_bounds[str(cutoff_probe)] = {'interval_exact_dyadic': raw_interval(b),
                                      'upper_display': display_upper(b)}
    gamma = iv.sqrt(rational('34/25'))
    t = rational('23/12')
    lipschitz = gamma * t + rational('2/5') * gamma ** 2 * t ** 2
    assert mp.mpf(lipschitz._mpi_[1]) < mp.mpf(rational('51/10')._mpi_[0])
    return {
        'schema': 'ueot.persistent_bath.interval_choi.v1',
        'status': 'OUTWARD_INTERVAL_BOUND_FOR_STORED_LINEAR_MAP',
        'lambda_exact': f'{f.numerator}/{f.denominator}',
        'slot_durations_exact':list(times_rational),
        'represented_backend':backend,
        'galerkin_cutoff_if_applicable':cutoff if backend=='galerkin' else None,
        'arithmetic': {'engine': 'mpmath.iv', 'decimal_precision': decimal_precision,
                       'raw_endpoint_semantics': '(-1)^sign * mantissa * 2^exponent; last integer is bitcount'},
        'input_dimension': 2,
        'normalized_choi': True,
        'untouched_reference': 'arbitrary finite dimension in analytic diamond implication',
        'bound_formula': '(d_in/2)*sum_r ||J_exact,r-J_stored,r||_1 <= 2*sum_r ||Delta J_r||_F',
        'half_diamond_error_rational_upper': '1/1000000000000',
        'computed_half_diamond_error_interval': raw_interval(error),
        'computed_half_diamond_error_upper_display': display_upper(error),
        'cutoff_uniform_bounds': cutoff_bounds,
        'parameter_lipschitz_certified_rational_upper': '51/10',
        'parameter_lipschitz_sharper_upper_display': display_upper(lipschitz),
        'choi_blocks': exported,
        'physical_repair': rational_physical_repair(floating),
        'limitations': [
            'Certificate concerns exact arithmetic interpretation of the stored binary64 Choi entries.',
            'A subsequent floating arbitrary-input matrix contraction needs its own roundoff budget.',
            'Raw rounded Choi matrices are not asserted CP/TP; the separately exported exact rational repaired instrument is CP/TP.',
            'No real device, SPAM calibration, Hamiltonian derivation from Core or infinite-mode limit is certified.'
        ],
        'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [Path(__file__), Path(dynamics.__file__)]},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--lambda-rational', default='3/10')
    parser.add_argument('--precision', type=int, default=80)
    parser.add_argument('--times', nargs=3, default=['2/3','3/4','1/2'])
    parser.add_argument('--backend', choices=['weyl','galerkin'], default='weyl')
    parser.add_argument('--cutoff', type=int, default=20)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('interval_choi_certificate.json'))
    args = parser.parse_args()
    result = certificate(args.lambda_rational, args.precision,args.times,args.backend,args.cutoff)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'lambda_exact',
                    'computed_half_diamond_error_upper_display',
                    'half_diamond_error_rational_upper',
                    'parameter_lipschitz_sharper_upper_display')}, indent=2))
