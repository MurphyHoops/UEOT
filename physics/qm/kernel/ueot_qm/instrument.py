"""Exact CP instruments, complete action libraries, and finite record laws.

A term (K,w), w>=0 rational, represents X -> w K X K*.  This includes
Hadamard as the integer matrix [[1,1],[1,-1]] with weight 1/2, without
pretending that sqrt(2) is rational.  All actions are validated as complete.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json

from .algebra import (
    Matrix,
    identity,
    matrix_payload,
    rational,
    real_trace,
    require_small_dimension,
    validate_density,
    zeros,
)


def _label(label: str) -> str:
    if not isinstance(label, str) or not label:
        raise ValueError("action and outcome labels must be nonempty strings")
    return label


def _fingerprint(payload: object) -> str:
    encoded = json.dumps(payload, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
    return sha256(encoded.encode("utf-8")).hexdigest()


def _dimension(matrix: Matrix, dimension: int) -> None:
    if not isinstance(matrix, Matrix):
        raise TypeError("operator must be a Matrix")
    if matrix.shape != (dimension, dimension):
        raise ValueError("operator dimension does not match the instrument")


@dataclass(frozen=True, slots=True)
class KrausTerm:
    operator: Matrix
    weight: Fraction = Fraction(1)

    def __post_init__(self) -> None:
        if not isinstance(self.operator, Matrix) or not self.operator.is_square:
            raise ValueError("a Kraus operator must be a square Matrix")
        require_small_dimension(self.operator.nrows)
        object.__setattr__(self, "weight", rational(self.weight))
        if self.weight < 0:
            raise ValueError("Kraus weights must be nonnegative")


@dataclass(frozen=True, slots=True, init=False)
class Instrument:
    """An immutable, exactly complete instrument for a single action.

    Each outcome maps to a finite sequence of KrausTerm objects.  Empty
    sequences are allowed as explicit impossible outcomes.  At least one
    nonempty sequence is needed to infer the Hilbert dimension.
    """

    branches: tuple[tuple[str, tuple[KrausTerm, ...]], ...]
    dimension: int

    def __init__(self, outcomes: Mapping[str, Sequence[KrausTerm]]) -> None:
        if not isinstance(outcomes, Mapping) or not outcomes:
            raise ValueError("an instrument needs a nonempty outcome mapping")
        for label in outcomes:
            _label(label)
        branches = tuple((label, tuple(outcomes[label])) for label in sorted(outcomes))
        terms = tuple(term for _, branch_terms in branches for term in branch_terms)
        if not terms:
            raise ValueError("an instrument needs at least one Kraus term")
        if any(not isinstance(term, KrausTerm) for term in terms):
            raise TypeError("outcome entries must be KrausTerm objects")
        dimension = terms[0].operator.nrows
        if any(term.operator.shape != (dimension, dimension) for term in terms):
            raise ValueError("all Kraus operators must have the same dimension")
        total = zeros(dimension)
        for term in terms:
            total += (term.operator.adjoint() @ term.operator) * term.weight
        if total != identity(dimension):
            raise ValueError("instrument is incomplete: sum(w K* K) must equal I exactly")
        object.__setattr__(self, "branches", branches)
        object.__setattr__(self, "dimension", dimension)

    @property
    def outcomes(self) -> tuple[str, ...]:
        return tuple(label for label, _ in self.branches)

    def terms(self, outcome: str) -> tuple[KrausTerm, ...]:
        for label, terms in self.branches:
            if label == outcome:
                return terms
        raise KeyError(f"unknown outcome {outcome!r}")

    def branch(self, operator: Matrix, outcome: str) -> Matrix:
        """Apply the linear branch map, including to subnormalized inputs.

        Only shape is checked here: this linear operation also makes sense
        on general operators.  The probability/posterior/record-law entry
        points separately require a physical normalized input state.
        """
        _dimension(operator, self.dimension)
        result = zeros(self.dimension)
        for term in self.terms(outcome):
            result += (term.operator @ operator @ term.operator.adjoint()) * term.weight
        return result

    def adjoint(self, effect: Matrix, outcome: str) -> Matrix:
        """Heisenberg pullback, dual to branch under the trace pairing."""
        _dimension(effect, self.dimension)
        result = zeros(self.dimension)
        for term in self.terms(outcome):
            result += (term.operator.adjoint() @ effect @ term.operator) * term.weight
        return result

    def outcome_effect(self, outcome: str) -> Matrix:
        return self.adjoint(identity(self.dimension), outcome)

    def completeness(self) -> Matrix:
        result = zeros(self.dimension)
        for outcome in self.outcomes:
            result += self.outcome_effect(outcome)
        return result

    def is_complete(self) -> bool:
        return self.completeness() == identity(self.dimension)

    def probability(self, state: Matrix, outcome: str) -> Fraction:
        validate_density(state, self.dimension)
        probability = real_trace(self.branch(state, outcome))
        if not 0 <= probability <= 1:
            raise ArithmeticError("complete CP instrument produced an invalid probability")
        return probability

    def posterior(self, state: Matrix, outcome: str) -> Matrix | None:
        validate_density(state, self.dimension)
        branch = self.branch(state, outcome)
        probability = real_trace(branch)
        if not probability:
            return None
        if not 0 < probability <= 1:
            raise ArithmeticError("complete CP instrument produced an invalid probability")
        return branch / probability

    def _payload(self) -> object:
        return {
            "dimension": self.dimension,
            "outcomes": [
                [
                    outcome,
                    [
                        [term.weight.numerator, term.weight.denominator, matrix_payload(term.operator)]
                        for term in terms
                    ],
                ]
                for outcome, terms in self.branches
            ],
        }


@dataclass(frozen=True, slots=True, init=False)
class ProtocolNode:
    """One action followed by outcome-dependent continuation or None.

    The tree is a finite deterministic causal controller.  Every possible
    outcome must be present, including zero-probability outcomes; this is
    checked against the library before any probabilities are evaluated.
    """

    action: str
    branches: tuple[tuple[str, ProtocolNode | None], ...]

    def __init__(self, action: str, branches: Mapping[str, ProtocolNode | None]) -> None:
        _label(action)
        if not isinstance(branches, Mapping) or not branches:
            raise ValueError("a protocol node needs an outcome-to-continuation mapping")
        for outcome, child in branches.items():
            _label(outcome)
            if child is not None and not isinstance(child, ProtocolNode):
                raise TypeError("a continuation must be ProtocolNode or None")
        object.__setattr__(self, "action", action)
        object.__setattr__(self, "branches", tuple(sorted(branches.items())))

    def continuation(self, outcome: str) -> ProtocolNode | None:
        for label, child in self.branches:
            if label == outcome:
                return child
        raise KeyError(f"protocol does not declare outcome {outcome!r}")


Record = tuple[tuple[str, str], ...]


@dataclass(frozen=True, slots=True, init=False)
class InstrumentLibrary:
    """Fixed time-homogeneous instruments, available at every step.

    The fingerprint identifies the exact declared action/outcome/Kraus
    context.  It is intentionally representation-sensitive: no claim is
    made that distinct Kraus decompositions get an identical fingerprint.
    """

    entries: tuple[tuple[str, Instrument], ...]
    dimension: int
    fingerprint: str

    def __init__(self, actions: Mapping[str, Instrument]) -> None:
        if not isinstance(actions, Mapping) or not actions:
            raise ValueError("an instrument library needs a nonempty action mapping")
        for action, instrument in actions.items():
            _label(action)
            if not isinstance(instrument, Instrument):
                raise TypeError("actions must map to validated Instrument objects")
        entries = tuple(sorted(actions.items()))
        dimension = entries[0][1].dimension
        if any(instrument.dimension != dimension for _, instrument in entries):
            raise ValueError("all actions must share one Hilbert dimension")
        payload = {
            "schema": "ueot_qm.instrument_library.v1",
            "protocol_class": "all-finite-causal-combinations",
            "actions": [[action, instrument._payload()] for action, instrument in entries],
        }
        object.__setattr__(self, "entries", entries)
        object.__setattr__(self, "dimension", dimension)
        object.__setattr__(self, "fingerprint", _fingerprint(payload))

    @property
    def actions(self) -> tuple[str, ...]:
        return tuple(action for action, _ in self.entries)

    def instrument(self, action: str) -> Instrument:
        for label, instrument in self.entries:
            if label == action:
                return instrument
        raise KeyError(f"unknown action {action!r}")

    def outcomes(self, action: str) -> tuple[str, ...]:
        return self.instrument(action).outcomes

    def branch(self, operator: Matrix, action: str, outcome: str) -> Matrix:
        return self.instrument(action).branch(operator, outcome)

    def adjoint(self, effect: Matrix, action: str, outcome: str) -> Matrix:
        return self.instrument(action).adjoint(effect, outcome)

    def probability(self, state: Matrix, action: str, outcome: str) -> Fraction:
        return self.instrument(action).probability(state, outcome)

    def posterior(self, state: Matrix, action: str, outcome: str) -> Matrix | None:
        return self.instrument(action).posterior(state, outcome)

    def word_law(self, state: Matrix, actions: Iterable[str]) -> dict[tuple[str, ...], Fraction]:
        """Full open-loop outcome law, retaining all zero-probability words."""
        validate_density(state, self.dimension)
        records = {(): state}
        for action in actions:
            instrument = self.instrument(action)
            records = {
                prefix + (outcome,): instrument.branch(branch_state, outcome)
                for prefix, branch_state in records.items()
                for outcome in instrument.outcomes
            }
        return {record: real_trace(branch_state) for record, branch_state in records.items()}

    def record_probability(self, state: Matrix, record: Iterable[tuple[str, str]]) -> Fraction:
        """Trace of the composed branch maps for an externally fixed word."""
        validate_density(state, self.dimension)
        branch_state = state
        for action, outcome in record:
            branch_state = self.branch(branch_state, action, outcome)
        return real_trace(branch_state)

    def validate_protocol(self, tree: ProtocolNode | None) -> None:
        pending = [tree]
        visited: set[int] = set()
        while pending:
            node = pending.pop()
            if node is None:
                continue
            if not isinstance(node, ProtocolNode):
                raise TypeError("protocol must be ProtocolNode or None")
            if id(node) in visited:
                continue
            visited.add(id(node))
            expected = self.outcomes(node.action)
            actual = tuple(outcome for outcome, _ in node.branches)
            if actual != expected:
                raise ValueError(f"protocol branches for {node.action!r} must be {expected!r}")
            pending.extend(child for _, child in node.branches)

    def protocol_law(self, state: Matrix, tree: ProtocolNode | None) -> dict[Record, Fraction]:
        """Joint action/outcome record law of a complete finite causal tree."""
        validate_density(state, self.dimension)
        self.validate_protocol(tree)
        result: dict[Record, Fraction] = {}
        pending = [(tree, (), state)]
        while pending:
            node, record, branch_state = pending.pop()
            if node is None:
                result[record] = real_trace(branch_state)
                continue
            for outcome, child in reversed(node.branches):
                pending.append(
                    (
                        child,
                        record + ((node.action, outcome),),
                        self.branch(branch_state, node.action, outcome),
                    )
                )
        return result
