"""Integer-grid Bell propagation with an explicit norm error and rational output.

A second finite solver, independent of SciPy exponentials and bath diagonalization.
Exact integer operations with checked int64 products. Rational inputs. See DYNAMICS.md.
"""
from fractions import Fraction as Q
from math import comb, factorial, isqrt

import numpy as np

from correlated_cq import RECORDS
from fock import _check_cutoff, _start, thermal_tail

SCALE = 2**27
DELTA = Q(1, SCALE)
TIMES_Q = {"deployment": (Q(2, 3), Q(3, 4), Q(1, 2)),
           "changed_intervals": (Q(3, 4), Q(2, 3), Q(1, 2))}
I64_MAX = 2**63-1


def _grid_sqrt(q, sign=1):
    q = Q(q)
    return sign * isqrt((SCALE*SCALE*q.numerator)//q.denominator)


def _upper(q):
    return Q(-(-q.numerator*10**13//q.denominator), 10**13)


def _maxabs(a):
    return max(abs(int(a.min())), abs(int(a.max())))


def _product(a, b, divisor=SCALE):
    """Complex matrix multiplication followed by floor of each component."""
    x, y = a
    z, w = b
    cap = 2*x.shape[1]*max(_maxabs(x), _maxabs(y))*max(_maxabs(z), _maxabs(w))
    if cap > I64_MAX:
        raise ArithmeticError("increase integer product width")
    return (x@z-y@w)//divisor, (x@w+y@z)//divisor


def _propagator(k, lam, t):
    d = _start(k+1)
    b = 0
    # ||H|| <= 3K/2 + 2 lambda ||g|| sqrt(K) <= 3K/2 + (K+1).
    while t*(Q(3*k, 2)+k+1) > 2**b*Q(1, 4):
        b += 1
    t = t/2**b
    h = np.zeros((d, d), dtype=np.int64)
    parity = []
    for s in range(k+1):
        for i in range(s+1):
            idx = _start(s)+i
            parity.append((-1)**s)
            h[idx, idx] = (SCALE*t*(i+Q(3*(s-i), 2))).__floor__()
            if s < k:
                for next_idx, q in ((_start(s+1)+i+1, (t*lam)**2*(i+1)),
                                    (_start(s+1)+i, (t*lam*Q(3, 5))**2*(s-i+1))):
                    h[idx, next_idx] = h[next_idx, idx] = _grid_sqrt(q)
    eye = np.eye(d, dtype=np.int64)*SCALE
    a = eye, np.zeros_like(h)
    order = 12
    for j in range(order, 0, -1):
        v, w = _product((np.zeros_like(h), -h), a, SCALE*j)
        if _maxabs(v)+SCALE > I64_MAX:
            raise ArithmeticError("Horner addition overflow")
        a = eye+v, w
    e = 5*DELTA + Q(1, 2**(order+1)*factorial(order+1)) + 4*d*DELTA
    for _ in range(b):
        a = _product(a, a)
        e = _upper(2*e+e*e+2*d*DELTA)
    # Parity conjugation sends the positive Z drive to the negative one.
    parity = np.outer(parity, parity)
    return (a, (a[0]*parity, a[1]*parity)), e


def _bell_factor(k, n, c):
    d = _start(k+1)
    z = np.zeros((d, d), dtype=np.int64)
    a, b = (p/(1+p) for p in (n+c, n-c))
    kept = 1-thermal_tail(n, c, k)
    for s in range(k+1):
        for h in range(s+1):
            w = (1-a)*(1-b)*a**h*b**(s-h)/kept
            for i in range(s+1):
                coeff = sum(comb(h, j)*comb(s-h, i-j)*(-1)**(s-h-i+j)
                            for j in range(max(0, i-s+h), min(i, h)+1))
                q = Q(factorial(i)*factorial(s-i), 2**(s+1)*factorial(h)*factorial(s-h))
                z[_start(s)+i, _start(s)+h] = _grid_sqrt(w*q*coeff**2, -1 if coeff < 0 else 1)
    # Matrix layout for each S value is E by (R, bath purification).
    zero = np.zeros_like(z)
    re = np.stack((np.hstack((z, zero)), np.hstack((zero, z))))
    return re, np.zeros_like(re)


def _gate(rows):
    """Each entry codes a signed square, separately for real and imaginary part."""
    def component(part):
        return np.array([[_grid_sqrt(abs(Q(str(x[part]))), -1 if Q(str(x[part])) < 0 else 1)
                          for x in row] for row in rows], dtype=np.int64)
    return component(0), component(1)


def _reduce_exact(v, d):
    re, im = (a.reshape(2, d, 2, d).transpose(0, 2, 1, 3).reshape(4, -1).astype(object)
              for a in v)
    return re@re.T+im@im.T, im@re.T-re@im.T


def bounded_bell(lam, n, c, cutoff, timing="deployment"):
    """Return exact rational normalized CQ blocks as (real,imag) arrays and error.

    The error bounds half trace distance to the exact finite Galerkin Bell output.
    Add uniform_bound(cutoff) for the infinite bath. Tested up through K=16.
    """
    lam, n, c = (Q(str(q)) for q in (lam, n, c))
    k = _check_cutoff(cutoff)
    if not (Q(1,5) <= lam <= Q(2,5) and abs(c) <= n <= Q(3,5) and timing in TIMES_Q):
        raise ValueError("outside frozen model")
    if k > 16:
        raise ValueError("integer backend supports total cutoff up to 16")
    d = _start(k+1)
    v = _bell_factor(k, n, c)
    error = 2*d*DELTA
    zero = (0, 0)
    fail = _gate([[("1/8", 0), zero], [zero, ("1/4", 0)]])
    passed = [_gate([[("7/16", 0), ("-3/8", 0)], [("7/16", 0), ("3/8", 0)]]),
              _gate([[("21/32", 0), (0, "-3/16")], [(0, "-7/32"), ("9/16", 0)]]),
              _gate([[("7/8", 0), zero], [zero, ("3/4", 0)]])]
    result = {}
    for j, t in enumerate(TIMES_Q[timing]):
        us, unit_error = _propagator(k, lam, t)
        pieces = [_product(us[i], (v[0][i], v[1][i])) for i in range(2)]
        evolved = tuple(np.stack(parts).reshape(2, -1) for parts in zip(*pieces))
        error = _upper(error+unit_error*(1+error)+3*d*DELTA)
        failed = _product(fail, evolved)
        result[RECORDS[j]] = _reduce_exact(failed, d)
        v = tuple(a.reshape(2, d, 2*d) for a in _product(passed[j], evolved))
        error = _upper(error+3*DELTA*(1+error)+4*d*DELTA)
    result["ppp"] = _reduce_exact(v, d)
    norm2 = sum(np.trace(re) for re, _ in result.values())
    if norm2 <= 0:
        raise ArithmeticError("cannot normalize zero output")
    blocks = {label: tuple(a*Q(1, norm2) for a in pair) for label, pair in result.items()}
    return blocks, min(Q(1), error)


def certified_choi(lam, n, c, cutoff, timing="deployment"):
    """Exactly CPTP rational Fock prediction; error is uniform over SR for these inputs.

    Return normalized Choi blocks (real, imaginary) and half-diamond error budget.
    All returned entries and budget values are fractions. Include the detector via
    the fixed Born rule separately. Unknown physical parameters require a further bound.
    """
    from fock import uniform_bound
    raw, e = bounded_bell(lam, n, c, cutoff, timing)
    half_eye = np.eye(2, dtype=int)*Q(1, 2)
    marginal = [sum(pair[j].reshape(2, 2, 2, 2).trace(axis1=0, axis2=2)
                    for pair in raw.values()) for j in (0, 1)]
    row_bound = max(np.sum(abs(marginal[0]-half_eye)+abs(marginal[1]), axis=1))
    tau = min(e, row_bound)
    scale = 1/(1+2*tau)
    blocks = {label: (scale*re, scale*im) for label, (re, im) in raw.items()}
    blocks["f"][0][:2, :2] += half_eye-scale*marginal[0]
    blocks["f"][1][:2, :2] -= scale*marginal[1]
    numeric = 2*(e+1-scale)
    truncation = uniform_bound(cutoff)
    return blocks, {"bell_arithmetic": e, "repair_bell": 1-scale,
                    "all_input_arithmetic": numeric, "truncation": truncation,
                    "total": min(Q(1), truncation+numeric)}


def rational_events(blocks, eta, name):
    """Exact Bell joint probabilities from certified_choi, same cell order as the float API."""
    from correlated_cq import PAULI
    eta = Q(str(eta))
    if not Q(".9") <= eta <= 1 or len(name)!=2 or any(x not in PAULI for x in name):
        raise ValueError("expected a frozen visibility and two Pauli axes")
    o = np.kron(PAULI[name[0]], PAULI[name[1]])
    ore, oim = o.real.astype(int), o.imag.astype(int)
    cells = []
    for label in RECORDS:
        re, im = blocks[label]
        weight = np.trace(re)
        moment = np.trace(ore@re-oim@im)
        cells.extend(((weight-eta*moment)/2, (weight+eta*moment)/2))
    return tuple(cells)
