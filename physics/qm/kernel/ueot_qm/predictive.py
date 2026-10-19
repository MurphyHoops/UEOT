"""Exact finite-word observable closure and its normalized response quotient.

The declared protocol class consists of all finite causal combinations of
one fixed, time-homogeneous instrument library.  These routines do not claim
minimality for a smaller protocol language, a restricted reachable set, or
a smaller physically realizable Hilbert-space model.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction

from .algebra import (
    Matrix,
    hermitian_vector,
    identity,
    linear_coordinates,
    matrix_payload,
    rational,
    real_trace,
    validate_density,
)
from .instrument import InstrumentLibrary, ProtocolNode, Record, _fingerprint


_ENCODING_KEY = object()


@dataclass(frozen=True, slots=True, init=False)
class EncodedState:
    """Immutable physical response coordinates produced by encode/update.

    Construction is restricted to the model's factories.  A context hash
    identifies a response basis; it alone would not certify that an arbitrary
    externally supplied coordinate vector belongs to the physical image.
    No coordinate-only feasibility solver or external deserializer is claimed.
    """

    context_fingerprint: str
    coordinates: tuple[Fraction, ...]

    def __init__(
        self,
        context_fingerprint: str,
        coordinates: Iterable[Fraction],
        *,
        _key: object = None,
    ) -> None:
        if _key is not _ENCODING_KEY:
            raise TypeError("construct physical EncodedState values with model.encode/update")
        coordinates = tuple(rational(x) for x in coordinates)
        if not coordinates or coordinates[0] != 1:
            raise ValueError("the identity response coordinate must equal one")
        if any(not 0 <= x <= 1 for x in coordinates):
            raise ValueError("word-effect response coordinates must lie in [0,1]")
        object.__setattr__(self, "context_fingerprint", context_fingerprint)
        object.__setattr__(self, "coordinates", coordinates)


@dataclass(frozen=True, slots=True, init=False)
class PredictiveModel:
    """Close the real observable span exactly, then descend each branch.

    basis[0] is I.  Each subsequent basis matrix is an actual finite-word
    effect; dimension_history includes the final non-increasing iteration.
    The closure is a linear span, not an algebra closure or a CPTP model
    reduction into a new smaller Hilbert space.
    """

    library: InstrumentLibrary
    basis: tuple[Matrix, ...]
    dimension_history: tuple[int, ...]
    context_fingerprint: str
    _pullbacks: tuple[tuple[str, str, Matrix], ...]

    def __init__(self, library: InstrumentLibrary) -> None:
        if not isinstance(library, InstrumentLibrary):
            raise TypeError("PredictiveModel needs a validated InstrumentLibrary")
        basis = [identity(library.dimension)]
        vectors = [hermitian_vector(basis[0])]
        dimensions = [1]
        while True:
            previous_size = len(basis)
            # Freeze W_n for this round.  New effects enter W_(n+1).
            for effect in tuple(basis):
                for action in library.actions:
                    for outcome in library.outcomes(action):
                        candidate = library.adjoint(effect, action, outcome)
                        vector = hermitian_vector(candidate)
                        if linear_coordinates(vectors, vector) is None:
                            basis.append(candidate)
                            vectors.append(vector)
            dimensions.append(len(basis))
            if len(basis) == previous_size:
                break
            if len(basis) > library.dimension ** 2:
                raise ArithmeticError("Hermitian closure exceeded its ambient dimension")

        pullbacks = []
        for action in library.actions:
            for outcome in library.outcomes(action):
                rows = []
                for effect in basis:
                    target = hermitian_vector(library.adjoint(effect, action, outcome))
                    coefficients = linear_coordinates(vectors, target)
                    if coefficients is None:
                        raise ArithmeticError("observable closure is not invariant")
                    rows.append(coefficients)
                pullbacks.append((action, outcome, Matrix(rows)))

        payload = {
            "schema": "ueot_qm.predictive_model.v1",
            "library_fingerprint": library.fingerprint,
            "normalization": "first-coordinate-is-trace",
            "basis": [matrix_payload(effect) for effect in basis],
        }
        object.__setattr__(self, "library", library)
        object.__setattr__(self, "basis", tuple(basis))
        object.__setattr__(self, "dimension_history", tuple(dimensions))
        object.__setattr__(self, "context_fingerprint", _fingerprint(payload))
        object.__setattr__(self, "_pullbacks", tuple(pullbacks))

    @property
    def dimension(self) -> int:
        """Number of homogeneous response coordinates, including trace."""
        return len(self.basis)

    @property
    def hilbert_dimension(self) -> int:
        return self.library.dimension

    @property
    def fingerprint(self) -> str:
        return self.context_fingerprint

    def _encoded(self, coordinates: Iterable[Fraction]) -> EncodedState:
        return EncodedState(self.context_fingerprint, coordinates, _key=_ENCODING_KEY)

    def _check_encoded(self, state: EncodedState) -> EncodedState:
        if not isinstance(state, EncodedState):
            raise TypeError("expected an EncodedState produced by encode/update")
        if state.context_fingerprint != self.context_fingerprint:
            raise ValueError("encoded state belongs to a different protocol/basis context")
        if len(state.coordinates) != self.dimension:
            raise ValueError("encoded coordinate count does not match this model")
        return state

    def _as_encoded(self, state: Matrix | EncodedState) -> EncodedState:
        if isinstance(state, Matrix):
            return self.encode(state)
        return self._check_encoded(state)

    def encode(self, state: Matrix) -> EncodedState:
        validate_density(state, self.library.dimension)
        return self._encoded(real_trace(state @ effect) for effect in self.basis)

    def equivalent(self, first: Matrix, second: Matrix) -> bool:
        """Exact response equivalence for this library's finite protocols."""
        return self.encode(first).coordinates == self.encode(second).coordinates

    def pullback_matrix(self, action: str, outcome: str) -> Matrix:
        """Return A with I_y^(a*) B_j = sum_i A[j,i] B_i.

        For normalized x, A@x is the subnormalized response vector, its
        first coordinate is the outcome probability, and division by that
        coordinate gives the positive-probability posterior response.
        """
        for stored_action, stored_outcome, matrix in self._pullbacks:
            if stored_action == action and stored_outcome == outcome:
                return matrix
        # Give the same specific unknown-action/outcome error as the library.
        self.library.instrument(action).terms(outcome)
        raise ArithmeticError("a validated action/outcome has no pullback matrix")

    def branch_coordinates(
        self, state: EncodedState, action: str, outcome: str
    ) -> tuple[Fraction, ...]:
        """Subnormalized branch responses; no dense state is reconstructed."""
        self._check_encoded(state)
        matrix = self.pullback_matrix(action, outcome)
        return tuple(
            sum((entry.real * x for entry, x in zip(row, state.coordinates)), Fraction(0))
            for row in matrix.rows
        )

    def _transition(
        self, state: EncodedState, action: str, outcome: str
    ) -> tuple[Fraction, EncodedState | None]:
        responses = self.branch_coordinates(state, action, outcome)
        probability = responses[0]
        if not 0 <= probability <= 1:
            raise ArithmeticError("response update produced an invalid probability")
        if not probability:
            if any(responses):
                raise ArithmeticError("a zero-probability physical branch has nonzero responses")
            return probability, None
        return probability, self._encoded(x / probability for x in responses)

    def probability(self, state: EncodedState, action: str, outcome: str) -> Fraction:
        probability, _ = self._transition(state, action, outcome)
        return probability

    def update(self, state: EncodedState, action: str, outcome: str) -> EncodedState | None:
        """The descended positive-branch update; impossible outcomes give None."""
        _, posterior = self._transition(state, action, outcome)
        return posterior

    def word_law(
        self, state: Matrix | EncodedState, actions: Iterable[str]
    ) -> dict[tuple[str, ...], Fraction]:
        """Full outcome law computed solely by response-coordinate updates."""
        encoded = self._as_encoded(state)
        records: dict[tuple[str, ...], tuple[Fraction, EncodedState | None]] = {
            (): (Fraction(1), encoded)
        }
        for action in actions:
            outcomes = self.library.outcomes(action)
            next_records = {}
            for record, (mass, current) in records.items():
                for outcome in outcomes:
                    if current is None:
                        probability, posterior = Fraction(0), None
                    else:
                        probability, posterior = self._transition(current, action, outcome)
                    next_records[record + (outcome,)] = (mass * probability, posterior)
            records = next_records
        return {record: mass for record, (mass, _) in records.items()}

    def record_probability(
        self, state: Matrix | EncodedState, record: Iterable[tuple[str, str]]
    ) -> Fraction:
        current: EncodedState | None = self._as_encoded(state)
        mass = Fraction(1)
        for action, outcome in record:
            if current is None:
                self.pullback_matrix(action, outcome)
                continue
            probability, current = self._transition(current, action, outcome)
            mass *= probability
        return mass

    def protocol_law(
        self, state: Matrix | EncodedState, tree: ProtocolNode | None
    ) -> dict[Record, Fraction]:
        """Full adaptive record law, using no state beyond response coordinates."""
        encoded = self._as_encoded(state)
        self.library.validate_protocol(tree)
        result: dict[Record, Fraction] = {}
        pending = [(tree, (), Fraction(1), encoded)]
        while pending:
            node, record, mass, current = pending.pop()
            if node is None:
                result[record] = mass
                continue
            for outcome, child in reversed(node.branches):
                if current is None:
                    probability, posterior = Fraction(0), None
                else:
                    probability, posterior = self._transition(current, node.action, outcome)
                pending.append(
                    (child, record + ((node.action, outcome),), mass * probability, posterior)
                )
        return result
