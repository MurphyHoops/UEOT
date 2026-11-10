#!/usr/bin/env python3
"""Exact finite checks of two UEOT source boundaries; no Lean proof is added.

The Python transaction below follows the six locally supplied Lean files from
main de8efdd7d9009d48cd64c005e209b158f2c66d42. All numerical laws use Fraction;
SymPy is used only for the displayed symbolic identities and Jacobian.
"""

from collections import defaultdict
from dataclasses import dataclass, replace
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json

import sympy as sp


@dataclass(frozen=True)
class Body:
    row_h: tuple[bool, bool, bool]
    row_d: tuple[bool, bool, bool]
    gate: bool
    bootstrap: bool
    tag: bool


@dataclass(frozen=True)
class Result:
    retained: Body | None
    newborn: Body | None
    repair_paid: int
    operation_paid: int
    refund: int
    status: str


P = (F(3, 4), F(1, 8), F(3, 8), F(1, 4), F(1, 3))
NOISE = tuple(product(range(3), range(3), (False, True), (False, True)))


def majority(row):
    return sum(row) >= 2


def damage_body(x, damaged):
    if not damaged:
        return x
    return replace(x, row_h=(not x.row_h[0], *x.row_h[1:]),
                   row_d=(not x.row_d[0], *x.row_d[1:]), gate=False)


def program_body(theta, damaged):
    return damage_body(Body((theta,) * 3, (False,) * 3, True, True, False), damaged)


def diagnostic(x):
    return (not x.gate or len(set(x.row_h)) != 1 or len(set(x.row_d)) != 1)


def restore(x):
    return replace(x, row_h=(majority(x.row_h),) * 3,
                   row_d=(majority(x.row_d),) * 3, gate=True)


def repair_cost(x):
    return (sum(bit != majority(x.row_h) for bit in x.row_h)
            + sum(bit != majority(x.row_d) for bit in x.row_d) + int(not x.gate))


def operation_cost(action):
    return {"care": 1, "bloom": 2, "stop": 0}[action]


def request_cap(x, action):
    return 0 if action == "stop" else repair_cost(x) + operation_cost(action) + 2


def can_execute(x, action):
    return (x.bootstrap or repair_cost(x) == 0) and request_cap(x, action) <= 6


def request_of(x):
    row = x.row_d if diagnostic(x) else x.row_h
    return "bloom" if majority(row) else "care"


def executed_result(x, action, z):
    u, v, damage_r, damage_b = z
    retains = (u in (1, 2) if action == "care" else u == 2)
    births = (v == 2 if action == "care" else v in (1, 2))
    y = restore(x)
    r = damage_body(y, damage_r) if retains else None
    b = damage_body(y, damage_b) if births else None
    repair, operation = repair_cost(x), operation_cost(action)
    refund = 6 - repair - operation - int(r is not None) - int(b is not None)
    assert refund >= 0
    return Result(r, b, repair, operation, refund, "executed")


def step(x, action, z):
    if action == "stop":
        return Result(None, None, 0, 0, 6, "stopped")
    if can_execute(x, action):
        return executed_result(x, action, z)
    return Result(x, None, 0, 0, 5, "rejected")


def program_step(x, z):
    request = request_of(x)
    if not can_execute(x, request):
        return Result(x, None, 0, 0, 5, "rejected")
    y = restore(x)
    original_diagnostic = diagnostic(x)
    assert y.gate
    active = (y.row_d if original_diagnostic else y.row_h)[0]
    actual = "bloom" if active else "care"
    return executed_result(x, actual, z)


def weight(z, p=P):
    s, delta, b, gamma, q = p
    u, v, damage_r, damage_b = z
    return ((1 - s, delta, s - delta)[u]
            * (1 - b - gamma, gamma, b)[v]
            * (q if damage_r else 1 - q) * (q if damage_b else 1 - q))


@lru_cache(None)
def future_birth_law(x, horizon):
    """Law of (B_1,...,B_T), counting NEWBORN slots at each census.

    Both potential output slots have independent child noise trees. Absent
    slots contribute the zero vector, integrating their unused noise to one.
    This is not the law of total population or of births by the founder alone.
    """
    if horizon == 0:
        return {(): F(1)}
    if x is None:
        return {(0,) * horizon: F(1)}
    law = defaultdict(F)
    for z in NOISE:
        r = program_step(x, z)
        left = future_birth_law(r.retained, horizon - 1)
        right = future_birth_law(r.newborn, horizon - 1)
        for a, mass_a in left.items():
            for b, mass_b in right.items():
                counts = (int(r.newborn is not None),) + tuple(i + j for i, j in zip(a, b))
                law[counts] += weight(z) * mass_a * mass_b
    assert sum(law.values()) == 1
    return dict(law)


def partition(named_values):
    groups = []
    for name, value in named_values.items():
        for group in groups:
            if value == named_values[group[0]]:
                group.append(name)
                break
        else:
            groups.append([name])
    return groups


def main():
    s0, d0, b0, g0, q0 = P
    assert 0 < d0 < s0 < 1 and 0 < b0 and b0 + g0 < 1
    assert d0 < g0 and 0 < q0 < 1 and s0 + b0 > 1
    assert len(NOISE) == 36 and sum(map(weight, NOISE)) == 1
    assert all(weight(z) > 0 for z in NOISE)

    states = {
        "theta0H": program_body(False, False),
        "theta0D": program_body(False, True),
        "theta1H": program_body(True, False),
        "theta1D": program_body(True, True),
    }
    for x in states.values():
        for z in NOISE:
            r = program_step(x, z)
            assert r == step(x, request_of(x), z)
            assert r.status == "executed"
            assert r.repair_paid + r.operation_paid + int(r.retained is not None) + int(r.newborn is not None) + r.refund == 6
    # This identity is independent of p; it is the base of the written
    # all-horizon same-noise-tree induction, not a numerical approximation.
    for z in NOISE:
        a = program_step(states["theta0H"], z)
        b = program_step(states["theta0D"], z)
        assert (a.retained, a.newborn) == (b.retained, b.newborn)
        assert (a.repair_paid, b.repair_paid) == (0, 3)
        assert a.refund - b.refund == 3

    laws = {T: {name: future_birth_law(x, T) for name, x in states.items()}
            for T in (1, 2, 3)}
    means = {name: [sum(F(record[k]) * mass for record, mass in law.items()) for k in (0, 1)]
             for name, law in laws[2].items()}
    assert means["theta1D"][1] - means["theta0D"][1] == (s0 + b0) * (1 - q0) * g0 == F(3, 16)
    s, delta, b, gamma, q = sp.symbols("s delta b gamma q", real=True)
    nu = sp.Matrix([[1 - q, q]])
    beta0, beta1 = sp.Matrix([b, b]), sp.Matrix([b + gamma, b])
    e0 = ((s + b) * nu * beta0)[0]
    e1 = ((s + b) * nu * beta1)[0]
    gap = sp.factor(e1 - e0)
    assert sp.simplify(gap - (s + b) * (1 - q) * gamma) == 0
    responses = sp.Matrix([s, b, b * q])
    jac = responses.jacobian([s, delta, b, gamma, q])
    minor = jac[:, [0, 2, 4]]
    assert minor.det() == b
    response_numeric = [sum(weight(z) * int(program_step(states["theta0H"], z).retained is not None) for z in NOISE),
                        sum(weight(z) * int(program_step(states["theta0H"], z).newborn is not None) for z in NOISE),
                        sum(weight(z) * int((n := program_step(states["theta0H"], z).newborn) is not None and diagnostic(n)) for z in NOISE)]
    assert response_numeric == [s0, b0, b0 * q0]

    source_relative = Path("formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure")
    source_names = (
        "CoreRegenerativeControlPopulation.lean",
        "CoreRegenerativeFormation.lean",
        "CoreRegenerativeOneStep.lean",
        "CoreRegenerativePopulation.lean",
        "CoreRegenerativeQuotient.lean",
        "CoreRegenerativeSource.lean",
    )
    # Locate either an enclosing repository or the cloud's bound ueot-review copy.
    source_dir = next(
        (ancestor / prefix / source_relative
         for ancestor in Path(__file__).resolve().parents
         for prefix in (Path(), Path("ueot-review"))
         if all((ancestor / prefix / source_relative / name).is_file()
                for name in source_names)),
        None,
    )
    if source_dir is None:
        raise FileNotFoundError("Cannot locate the six bound UEOT source files from this script's ancestors")
    hashes = {name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
              for name in source_names}
    result = {
        "bound_commit_as_supplied": "de8efdd7d9009d48cd64c005e209b158f2c66d42",
        "source_sha256": hashes,
        "parameter_point": list(map(str, P)),
        "actual_program_requests": {name: request_of(x) for name, x in states.items()},
        "actual_request_caps": {name: request_cap(x, request_of(x)) for name, x in states.items()},
        "actual_initial_repair_paid": {name: repair_cost(x) for name, x in states.items()},
        "newborn_means_B1_B2": {name: list(map(str, values)) for name, values in means.items()},
        "second_tick_newborn_gap": str(gap),
        "second_tick_gap_at_point": "3/16",
        "finite_birth_record_partitions": {str(T): partition(law) for T, law in laws.items()},
        "birth_records_plus_initial_repair_partition": partition({name: (laws[3][name], repair_cost(x)) for name, x in states.items()}),
        "one_birth_plus_initial_repair_partition": partition({name: (laws[1][name], repair_cost(x)) for name, x in states.items()}),
        "public_response_map": [str(expr) for expr in responses],
        "jacobian_parameters_s_delta_b_gamma_q": str(jac),
        "s_b_q_minor_determinant": str(minor.det()),
        "public_response_at_point": list(map(str, response_numeric)),
        "two_tick_joint_laws": {name: {str(record): str(mass) for record, mass in sorted(law.items())} for name, law in laws[2].items()},
        "status": "All finite exact checks passed. All-horizon equality and C1-factor obstruction are written proofs; no new Lean theorem or compilation claimed.",
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
