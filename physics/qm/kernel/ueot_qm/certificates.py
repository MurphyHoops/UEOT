"""Exact, explicitly scoped record and error certificates.

Finite protocol comparisons cover only the supplied preparation pairs and
causal trees. They do not certify all states, all protocols, trace distance,
or diamond norm. Scalar transport requires its stated recurrence hypotheses;
the optional trace verifier checks those hypotheses on the supplied trace.
"""

from __future__ import annotations

from collections.abc import Hashable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json

from .algebra import Matrix, matrix_payload, rational
from .instrument import InstrumentLibrary, ProtocolNode


def _law(law: Mapping[Hashable, int | Fraction]) -> dict[Hashable, Fraction]:
    if not isinstance(law, Mapping) or not law:
        raise ValueError("a probability law must be a nonempty mapping")
    result = {key: rational(value) for key, value in law.items()}
    if any(value < 0 for value in result.values()) or sum(result.values()) != 1:
        raise ValueError("a probability law must be nonnegative and sum to one")
    return result


def tv_distance(left: Mapping[Hashable, int | Fraction],
                right: Mapping[Hashable, int | Fraction]) -> Fraction:
    """Total variation of two normalized finite laws on the union of supports."""
    left, right = _law(left), _law(right)
    return sum((abs(left.get(k, 0) - right.get(k, 0))
                for k in left.keys() | right.keys()), Fraction()) / 2


def _protocol_payload(tree: ProtocolNode | None):
    if tree is None:
        return None
    # A flat deterministic breadth-first table also handles long finite
    # controllers. Sharing a subtree does not change its unfolded meaning.
    pending = [tree]
    nodes = []
    for node in pending:
        branches = []
        for outcome, child in node.branches:
            child_index = None
            if child is not None:
                child_index = len(pending)
                pending.append(child)
            branches.append([outcome, child_index])
        nodes.append([node.action, branches])
    return {"root": 0, "nodes": nodes}


@dataclass(frozen=True, slots=True)
class ProtocolComparison:
    preparation: str
    protocol: str
    tv: Fraction


@dataclass(frozen=True, slots=True)
class FiniteProtocolCertificate:
    left_context: str
    right_context: str
    scope_fingerprint: str
    preparation_pair_count: int
    protocol_count: int
    comparisons: tuple[ProtocolComparison, ...]
    maximum_tv: Fraction
    scope: str = "declared-finite-preparation-pairs-and-causal-trees"


def compare_finite_protocols(
    left: InstrumentLibrary,
    right: InstrumentLibrary,
    preparation_pairs: Mapping[str, tuple[Matrix, Matrix]],
    protocols: Mapping[str, ProtocolNode | None],
) -> FiniteProtocolCertificate:
    """Evaluate every named preparation-pair/tree combination exactly.

    A pair is an explicitly chosen comparison, not a proved preparation
    embedding. Action and outcome labels mean the same records on each side;
    every tree must be valid in both libraries. Empty coverage is rejected.
    The fingerprint binds all matrices, operations and tree structures.
    """
    if not preparation_pairs or not protocols:
        raise ValueError("certificate coverage must include preparations and protocols")
    if any(not isinstance(name, str) or not name
           for name in (*preparation_pairs, *protocols)):
        raise ValueError("coverage entries need nonempty string names")
    rows = []
    for pname in sorted(preparation_pairs):
        pair = preparation_pairs[pname]
        if len(pair) != 2:
            raise ValueError("a preparation comparison needs two density operators")
        rho, sigma = pair
        for tname in sorted(protocols):
            tree = protocols[tname]
            rows.append(ProtocolComparison(
                pname, tname,
                tv_distance(left.protocol_law(rho, tree), right.protocol_law(sigma, tree)),
            ))
    payload = {
        "schema": "ueot_qm.finite_protocol_certificate.v1",
        "left": left.fingerprint,
        "right": right.fingerprint,
        "preparations": [[name, matrix_payload(preparation_pairs[name][0]),
                           matrix_payload(preparation_pairs[name][1])]
                          for name in sorted(preparation_pairs)],
        "protocols": [[name, _protocol_payload(protocols[name])] for name in sorted(protocols)],
    }
    digest = sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return FiniteProtocolCertificate(
        left.fingerprint, right.fingerprint, digest, len(preparation_pairs), len(protocols),
        tuple(rows), max(row.tv for row in rows),
    )


@dataclass(frozen=True, slots=True)
class TransportStep:
    """A stated local bound e_next <= lipschitz*e + local_bound.

    The justification is provenance text, not a machine proof of that bound.
    In a quantum application the metric and the protocol/state scope must be
    supplied by the caller. Both numerical coefficients must be nonnegative.
    """

    lipschitz: Fraction
    local_bound: Fraction
    justification: str

    def __post_init__(self):
        object.__setattr__(self, "lipschitz", rational(self.lipschitz))
        object.__setattr__(self, "local_bound", rational(self.local_bound))
        if self.lipschitz < 0 or self.local_bound < 0:
            raise ValueError("transport coefficients and local bounds must be nonnegative")
        if not isinstance(self.justification, str) or not self.justification.strip():
            raise ValueError("each transport premise needs explicit provenance")


def transport_budget(initial_bound: int | Fraction,
                     steps: Iterable[TransportStep]) -> tuple[Fraction, ...]:
    """Conditional scalar upper bounds, including the initial bound.

    This calculation does not establish any quantum metric recurrence. Use
    verify_transport_trace to check a specified finite numerical trace.
    """
    initial_bound = rational(initial_bound)
    if initial_bound < 0:
        raise ValueError("the initial bound must be nonnegative")
    bounds = [initial_bound]
    for step in steps:
        if not isinstance(step, TransportStep):
            raise TypeError("transport steps must be TransportStep objects")
        bounds.append(step.lipschitz * bounds[-1] + step.local_bound)
    return tuple(bounds)


@dataclass(frozen=True, slots=True)
class TransportTraceCertificate:
    errors: tuple[Fraction, ...]
    bounds: tuple[Fraction, ...]
    steps: tuple[TransportStep, ...]
    scope: str = "supplied-finite-scalar-trace"


def verify_transport_trace(errors: Sequence[int | Fraction],
                           initial_bound: int | Fraction,
                           steps: Iterable[TransportStep]) -> TransportTraceCertificate:
    """Check initial and local premises on every supplied step, then coverage."""
    steps = tuple(steps)
    bounds = transport_budget(initial_bound, steps)
    errors = tuple(rational(value) for value in errors)
    if len(errors) != len(bounds) or any(value < 0 for value in errors):
        raise ValueError("errors must be a nonnegative trace with one entry per boundary")
    if errors[0] > bounds[0]:
        raise ValueError("the initial error exceeds its bound")
    for index, step in enumerate(steps):
        if errors[index + 1] > step.lipschitz * errors[index] + step.local_bound:
            raise ValueError(f"the local transport premise fails at step {index}")
    if any(error > bound for error, bound in zip(errors, bounds)):
        raise ArithmeticError("verified transport premises failed to cover the trace")
    return TransportTraceCertificate(errors, bounds, steps)


@dataclass(frozen=True, slots=True)
class PostselectionCertificate:
    original_tv: Fraction
    left_event_mass: Fraction
    right_event_mass: Fraction
    minimum_event_mass: Fraction
    conditional_tv: Fraction
    conditional_upper_bound: Fraction


def certify_postselection(left: Mapping[Hashable, int | Fraction],
                          right: Mapping[Hashable, int | Fraction],
                          event: Iterable[Hashable]) -> PostselectionCertificate:
    """Compute finite conditional TV and min(1, 2*TV/min(P(E),Q(E))).

    Both event masses must be positive. No posterior on a zero-evidence
    branch and no event-independent contraction are asserted.
    """
    left, right = _law(left), _law(right)
    event = frozenset(event)
    p = sum((left.get(key, 0) for key in event), Fraction())
    q = sum((right.get(key, 0) for key in event), Fraction())
    if min(p, q) <= 0:
        raise ValueError("conditioning requires a positive event mass on both sides")
    delta = tv_distance(left, right)
    conditional = tv_distance({key: left.get(key, 0) / p for key in event},
                              {key: right.get(key, 0) / q for key in event})
    bound = min(Fraction(1), 2 * delta / min(p, q))
    if conditional > bound:
        raise ArithmeticError("finite conditional TV exceeds its stated upper bound")
    return PostselectionCertificate(delta, p, q, min(p, q), conditional, bound)
