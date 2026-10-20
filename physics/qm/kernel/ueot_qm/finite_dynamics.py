"""Exact finite mixture, Cesaro, and diagonal survival constructions.

The corresponding general mathematical statements live in Mixture.lean,
Cesaro.lean, and Survival.lean. This Python implementation is independently
tested executable evidence; the Python interpreter is not verified by Lean.
All rational inputs are exact and the existing density limit is dimension 4.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

from .algebra import Matrix, rational, require_small_dimension, validate_density, zeros
from .instrument import Instrument, InstrumentLibrary, KrausTerm


def _exact(value: int | Fraction) -> Fraction:
    if isinstance(value, bool):
        raise TypeError("booleans are not rational model parameters")
    return rational(value)


@dataclass(frozen=True, slots=True, init=False)
class ProbabilityWeights:
    """A nonempty, normalized finite distribution of nonnegative rationals."""

    values: tuple[Fraction, ...]

    def __init__(self, values: Sequence[int | Fraction]) -> None:
        values = tuple(_exact(value) for value in values)
        if not values or any(value < 0 for value in values) or sum(values) != 1:
            raise ValueError("weights must be nonnegative and sum to one exactly")
        object.__setattr__(self, "values", values)

    def total_variation(self, other: ProbabilityWeights) -> Fraction:
        if not isinstance(other, ProbabilityWeights):
            raise TypeError("comparison requires ProbabilityWeights")
        if len(self.values) != len(other.values):
            raise ValueError("weights must index the same finite library")
        return sum((abs(p - q) for p, q in zip(self.values, other.values)), Fraction()) / 2


def mix_instruments(components: Sequence[Instrument], weights: ProbabilityWeights) -> Instrument:
    """Concatenate actual weighted Kraus terms over a common outcome alphabet."""
    components = tuple(components)
    if not isinstance(weights, ProbabilityWeights):
        raise TypeError("mixture requires validated ProbabilityWeights")
    if len(components) != len(weights.values):
        raise ValueError("one weight is required for each component")
    if any(not isinstance(component, Instrument) for component in components):
        raise TypeError("all components must be complete Instrument objects")
    first = components[0]
    if any(component.dimension != first.dimension or component.outcomes != first.outcomes
           for component in components):
        raise ValueError("components must share a dimension and outcome alphabet")
    return Instrument({
        outcome: tuple(KrausTerm(term.operator, weight * term.weight)
                       for weight, component in zip(weights.values, components)
                       for term in component.terms(outcome))
        for outcome in first.outcomes
    })


@dataclass(frozen=True, slots=True, init=False)
class MixtureWeightBudget:
    """Bind a computed TV upper budget to two mixtures of one actual library.

    This does not accept a guessed bound or extend it to different component
    channels. The fingerprint records the exact Kraus representation, not an
    equivalence class of all representations of that channel.
    """

    components: tuple[Instrument, ...]
    left_weights: ProbabilityWeights
    right_weights: ProbabilityWeights
    left: Instrument
    right: Instrument
    component_fingerprint: str
    upper_bound: Fraction

    def __init__(self, components: Sequence[Instrument], left: ProbabilityWeights,
                 right: ProbabilityWeights) -> None:
        components = tuple(components)
        bound = left.total_variation(right)
        left_instrument = mix_instruments(components, left)
        right_instrument = mix_instruments(components, right)
        context = InstrumentLibrary({str(i): component for i, component in enumerate(components)})
        for name, value in (
            ("components", components), ("left_weights", left), ("right_weights", right),
            ("left", left_instrument), ("right", right_instrument),
            ("component_fingerprint", context.fingerprint), ("upper_bound", bound),
        ):
            object.__setattr__(self, name, value)


def channel_operator(instrument: Instrument, operator: Matrix) -> Matrix:
    """Apply the complete channel linearly, including to residual operators."""
    result = zeros(instrument.dimension)
    for outcome in instrument.outcomes:
        result += instrument.branch(operator, outcome)
    return result


def _steps(steps: int, *, positive: bool) -> None:
    if isinstance(steps, bool) or not isinstance(steps, int):
        raise TypeError("step count must be an integer")
    if steps < int(positive):
        raise ValueError("step count must be positive" if positive else "step count must be nonnegative")


def iterate_state(instrument: Instrument, state: Matrix, steps: int) -> Matrix:
    _steps(steps, positive=False)
    validate_density(state, instrument.dimension)
    for _ in range(steps):
        state = channel_operator(instrument, state)
    return state


def cesaro_average(instrument: Instrument, state: Matrix, steps: int) -> Matrix:
    """Return (rho_0 + ... + rho_(N-1))/N for an actual complete channel."""
    _steps(steps, positive=True)
    validate_density(state, instrument.dimension)
    total = zeros(instrument.dimension)
    for _ in range(steps):
        total += state
        state = channel_operator(instrument, state)
    return total / steps


def substochastic_instrument(rows: Sequence[Sequence[int | Fraction]]) -> Instrument:
    """Measure-prepare dilation of a row-substochastic matrix Q.

    The success Kraus term indexed by (i,j) has operator |j><i| and weight
    Q[i][j]. Loss on i has weight 1-sum_j Q[i][j]. Both branches together
    are exactly trace preserving. In Lean the outcomes are true and false;
    here their explicit names are 'survive' and 'lost'.
    """
    rows = tuple(tuple(_exact(value) for value in row) for row in rows)
    dimension = len(rows)
    require_small_dimension(dimension)
    if any(len(row) != dimension for row in rows):
        raise ValueError("the substochastic matrix must be square")
    if any(value < 0 for row in rows for value in row):
        raise ValueError("substochastic entries must be nonnegative")
    if any(sum(row) > 1 for row in rows):
        raise ValueError("each substochastic row must sum to at most one")

    def unit(j: int, i: int) -> Matrix:
        return Matrix([[int(a == j and b == i) for b in range(dimension)]
                       for a in range(dimension)])

    return Instrument({
        "survive": tuple(KrausTerm(unit(j, i), rows[i][j])
                         for i in range(dimension) for j in range(dimension)),
        "lost": tuple(KrausTerm(unit(i, i), 1 - sum(rows[i])) for i in range(dimension)),
    })
