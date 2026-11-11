"""Finite, visible-record quantum conditioning: a numerical reference only.

The exact witness checker is in exact_witnesses.py.  This module never treats a
floating residual, an LP status, or a numerical support decision as a proof.
Kraus indices remain hidden; leaf keys contain only original visible outcomes.
"""
from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Mapping, Union
import math

import numpy as np
from scipy.optimize import linprog

Array = np.ndarray
History = tuple[str, ...]


class ZeroAcceptanceProbability(ValueError):
    """No conditional law is returned for a zero-mass event."""


class NumericalConditioningError(ValueError):
    """Support/inversion cannot be trusted at the chosen numerical precision."""


def dagger(x: Array) -> Array:
    return x.conj().T


def hermitian(x: Array) -> Array:
    return (x + dagger(x)) / 2


def mass(x: Array) -> float:
    t = np.trace(x)
    if abs(t.imag) > 1e-9 * max(1.0, abs(t.real)):
        raise ValueError("non-real mass: the input is not a quantum state")
    return float(t.real)


def trace_distance(x: Array, y: Array) -> float:
    return float(np.abs(np.linalg.eigvalsh(hermitian(x - y))).sum() / 2)


def cq_distance(x: Mapping[History, Array], y: Mapping[History, Array]) -> float:
    sample = next(iter(x.values()), next(iter(y.values()), None))
    if sample is None:
        return 0.0
    z = np.zeros_like(sample)
    return sum(trace_distance(x.get(k, z), y.get(k, z)) for k in x.keys() | y.keys())


def validate_density(rho: Array, atol: float = 1e-10) -> None:
    if rho.ndim != 2 or rho.shape[0] != rho.shape[1] or not np.isfinite(rho).all():
        raise ValueError("density must be a finite square matrix")
    if np.linalg.norm(rho - dagger(rho)) > atol:
        raise ValueError("density is not Hermitian")
    if np.linalg.eigvalsh(hermitian(rho)).min() < -atol or abs(mass(rho) - 1) > atol:
        raise ValueError("density is not PSD with trace one")


@dataclass(frozen=True)
class Instrument:
    branches: Mapping[str, tuple[Array, ...]]

    def __post_init__(self) -> None:
        if not self.branches:
            raise ValueError("an instrument needs visible outcomes")
        b = {}
        shape = None
        for label, ks in self.branches.items():
            if not isinstance(label, str) or not ks:
                raise ValueError("each visible outcome needs a hidden Kraus tuple")
            a = []
            for k in ks:
                k = np.array(k, dtype=complex, copy=True)
                if k.ndim != 2 or k.shape[0] != k.shape[1] or not np.isfinite(k).all():
                    raise ValueError("only finite square carrier Kraus matrices are in scope")
                if shape is not None and shape != k.shape:
                    raise ValueError("inconsistent quantum carrier")
                shape = k.shape
                k.flags.writeable = False
                a.append(k)
            b[label] = tuple(a)
        object.__setattr__(self, "branches", MappingProxyType(b))

    @property
    def dimension(self) -> int:
        return next(iter(self.branches.values()))[0].shape[0]

    def gram(self) -> Array:
        return sum((dagger(k) @ k for ks in self.branches.values() for k in ks),
                   np.zeros((self.dimension, self.dimension), complex))

    def validate_complete(self, atol: float = 1e-9) -> None:
        if np.linalg.norm(self.gram() - np.eye(self.dimension)) > atol:
            raise ValueError("source or completed instrument is not trace preserving")

    def branch(self, label: str, x: Array) -> Array:
        return sum((k @ x @ dagger(k) for k in self.branches[label]), np.zeros_like(x))

    def adjoint(self, label: str, h: Array) -> Array:
        return sum((dagger(k) @ h @ k for k in self.branches[label]), np.zeros_like(h))

    def channel(self, x: Array) -> Array:
        return sum((self.branch(o, x) for o in self.branches), np.zeros_like(x))


@dataclass(frozen=True)
class Leaf:
    accepted: bool


@dataclass(frozen=True)
class Node:
    instrument: Instrument
    children: Mapping[str, "Tree"]
    action_cost: float = 1.0

    def __post_init__(self) -> None:
        if set(self.children) != set(self.instrument.branches):
            raise ValueError("tree children must exactly equal original visible outcomes")
        if not math.isfinite(self.action_cost) or self.action_cost < 0:
            raise ValueError("invalid action cost")
        object.__setattr__(self, "children", MappingProxyType(dict(self.children)))


Tree = Union[Leaf, Node]


def repeated_success_tree(instrument: Instrument, successes: set[str], horizon: int) -> Tree:
    if isinstance(horizon, bool) or not isinstance(horizon, int) or horizon < 0:
        raise ValueError("horizon must be a finite nonnegative integer")
    if not successes <= instrument.branches.keys():
        raise ValueError("unregistered success outcome")
    if horizon == 0:
        return Leaf(True)
    tail = repeated_success_tree(instrument, successes, horizon - 1)
    return Node(instrument, {o: tail if o in successes else Leaf(False)
                             for o in instrument.branches})


def backward_effects(tree: Tree, dimension: int) -> dict[History, Array]:
    effects: dict[History, Array] = {}
    eye = np.eye(dimension, dtype=complex)

    def walk(t: Tree, path: History) -> Array:
        if isinstance(t, Leaf):
            h = eye.copy() if t.accepted else np.zeros_like(eye)
        else:
            if t.instrument.dimension != dimension:
                raise ValueError("carrier changes are outside this reference scope")
            t.instrument.validate_complete()
            h = sum((t.instrument.adjoint(o, walk(t.children[o], path + (o,)))
                     for o in t.instrument.branches), np.zeros_like(eye))
            h = hermitian(h)
        ev = np.linalg.eigvalsh(h)
        if ev.min() < -1e-9 or ev.max() > 1 + 1e-9:
            raise ValueError("backward effect is outside [0,I]")
        effects[path] = h
        return h

    walk(tree, ())
    return effects


def full_leaf_law(tree: Tree, rho: Array) -> tuple[dict[History, Array], set[History]]:
    """Unnormalized CQ leaf blocks; never enumerate hidden Kraus labels."""
    blocks: dict[History, Array] = {}
    accepted: set[History] = set()

    def walk(t: Tree, x: Array, path: History) -> None:
        if isinstance(t, Leaf):
            blocks[path] = hermitian(x)
            if t.accepted:
                accepted.add(path)
            return
        for o, child in t.children.items():
            walk(child, t.instrument.branch(o, x), path + (o,))

    walk(tree, rho, ())
    return blocks, accepted


def acceptance_mass(blocks: Mapping[History, Array], accepted: set[History]) -> float:
    return sum(mass(blocks[k]) for k in accepted)


def normalized_accepted_law(blocks: Mapping[History, Array], accepted: set[History]
                            ) -> tuple[float, dict[History, Array]]:
    p = acceptance_mass(blocks, accepted)
    if not math.isfinite(p) or p < 0:
        raise NumericalConditioningError("acceptance mass is numerically invalid")
    if p == 0:
        raise ZeroAcceptanceProbability("zero acceptance mass; no arbitrary replacement state")
    # Keep rejected records as zero blocks in the same original record space.
    return p, {k: x / p if k in accepted else np.zeros_like(x) for k, x in blocks.items()}


@dataclass(frozen=True)
class PSDFactors:
    sqrt: Array
    inverse_sqrt: Array
    support: Array
    positive_eigenvalues: tuple[float, ...]
    clipped_negative_eigenvalues: tuple[float, ...]


def psd_factors(h: Array, relative_inverse_floor: float = 1e-12) -> PSDFactors:
    """Numerical support factors. Tiny positive values are NOT set to zero.

    Near rank ambiguity, fail explicitly. Tiny negative roundoff may be clipped;
    this decision remains numerical and is listed in the diagnostics.
    """
    if h.ndim != 2 or h.shape[0] != h.shape[1] or not np.isfinite(h).all():
        raise ValueError("PSD input must be a finite square matrix")
    if np.linalg.norm(h - dagger(h)) > 1e-10 * max(np.linalg.norm(h), np.finfo(float).tiny):
        raise ValueError("PSD input must be Hermitian")
    ev, u = np.linalg.eigh(hermitian(h))
    scale = max(float(np.max(np.abs(ev))), np.finfo(float).tiny)
    if float(ev.min()) < -1e-12 * scale:
        raise ValueError("effect is not PSD")
    positive = ev > 0
    pos = ev[positive]
    if pos.size and float(pos.min() / pos.max()) < relative_inverse_floor:
        raise NumericalConditioningError(
            "positive support eigenvalue is too small: require higher precision or an exact certificate")
    sq = np.sqrt(np.maximum(ev, 0))
    inv = np.zeros_like(ev)
    inv[positive] = 1 / sq[positive]
    return PSDFactors((u * sq) @ dagger(u), (u * inv) @ dagger(u),
                      (u * positive.astype(float)) @ dagger(u),
                      tuple(float(x) for x in pos), tuple(float(x) for x in ev if x < 0))


@dataclass(frozen=True)
class ConditionedReference:
    tree: Tree
    initial_state: Array
    acceptance_probability: float
    effects: Mapping[History, Array]
    supports: Mapping[History, Array]
    diagnostics: Mapping[History, PSDFactors]


def conditioned_reference(tree: Tree, rho: Array,
                          completion_label: str | None = None) -> ConditionedReference:
    validate_density(rho)
    effects = backward_effects(tree, rho.shape[0])
    source_law, accepted = full_leaf_law(tree, rho)
    p, _ = normalized_accepted_law(source_law, accepted)
    hp = mass(effects[()] @ rho)
    if abs(hp - p) > 1e-9 * max(1.0, abs(p)):
        raise NumericalConditioningError("source leaf mass differs from backward effect pairing")
    factors = {h: psd_factors(e) for h, e in effects.items()}
    initial = hermitian(factors[()].sqrt @ rho @ factors[()].sqrt / p)
    validate_density(initial, atol=1e-8)

    def walk(t: Tree, path: History) -> Tree:
        if isinstance(t, Leaf):
            return t
        f = factors[path]
        branches = {
            o: tuple(factors[path + (o,)].sqrt @ k @ f.inverse_sqrt for k in ks)
            for o, ks in t.instrument.branches.items()
        }
        # Complete on the unused orthogonal space using a HIDDEN Kraus under an
        # original visible label. No artificial observable Kraus record is added.
        label = completion_label if completion_label in branches else next(iter(branches))
        complement = np.eye(rho.shape[0]) - f.support
        branches[label] = branches[label] + (complement,)
        instrument = Instrument(branches)
        instrument.validate_complete(atol=2e-8)
        return Node(instrument, {o: walk(child, path + (o,)) for o, child in t.children.items()},
                    t.action_cost)

    return ConditionedReference(walk(tree, ()), initial, p, effects,
                                {h: f.support for h, f in factors.items()}, factors)


def expected_action_cost(tree: Tree, rho: Array) -> float:
    def walk(t: Tree, x: Array) -> float:
        if isinstance(t, Leaf):
            return 0.0
        return t.action_cost * mass(x) + sum(
            walk(child, t.instrument.branch(o, x)) for o, child in t.children.items())
    return walk(tree, rho)


def independent_retry_cost(tree: Tree, rho: Array, preparation: float = 0,
                           failed_reset: float = 0, other_per_attempt: float = 0) -> dict:
    """IID repeated preparations, resetting only failed trials by this convention."""
    if any(not math.isfinite(v) or v < 0 for v in (preparation, failed_reset, other_per_attempt)):
        raise ValueError("resource costs must be finite and nonnegative")
    validate_density(rho)
    backward_effects(tree, rho.shape[0])  # validate the actual complete source
    law, accepted = full_leaf_law(tree, rho)
    p, _ = normalized_accepted_law(law, accepted)
    action = expected_action_cost(tree, rho)
    c = action + preparation + (1 - p) * failed_reset + other_per_attempt
    return {"acceptance_probability": p, "attempts_per_output": 1 / p,
            "action_cost_per_attempt": action, "all_cost_per_attempt": c,
            "all_cost_per_output": c / p,
            "reset_convention": "charge only unsuccessful trials"}


def scaled_filter(h: Array, rho: Array, c: float | None = None) -> tuple[Instrument, float]:
    maximum = float(np.linalg.eigvalsh(hermitian(h)).max())
    if maximum <= 0:
        raise ZeroAcceptanceProbability("zero effect cannot prepare a conditional state")
    c = maximum if c is None else float(c)
    if not math.isfinite(c) or c < maximum * (1 - 1e-12):
        raise ValueError("filter scale must bound the effect norm")
    root = psd_factors(h / c).sqrt
    failure = psd_factors(np.eye(h.shape[0]) - h / c, relative_inverse_floor=0).sqrt
    instrument = Instrument({"pass": (root,), "fail": (failure,)})
    instrument.validate_complete()
    return instrument, mass(instrument.branch("pass", rho))


def branch_choi(ks: tuple[Array, ...]) -> Array:
    """Input-first Choi convention: vec(K)[input,output] = K[output,input]."""
    n = ks[0].size
    return sum((np.outer(k.reshape(-1, order="F"), k.reshape(-1, order="F").conj())
                for k in ks), np.zeros((n, n), complex))


def labelled_choi_vector(instrument: Instrument, labels: tuple[str, ...]) -> Array:
    if set(labels) != set(instrument.branches):
        raise ValueError("preserve exactly the specified visible labels")
    z = np.concatenate([branch_choi(instrument.branches[o]).reshape(-1) for o in labels])
    return np.concatenate([z.real, z.imag])


def common_observation_mixture(targets: Mapping[str, Instrument],
                               actions: Mapping[str, Mapping[str, Instrument]]) -> dict:
    """One shared probability vector across ALL supplied hidden configurations.

    The caller supplies ONE observation fibre. Independent fibres require separate
    calls. LP feasibility/infeasibility is numerical, never an exact certificate.
    """
    if not targets or not actions:
        raise ValueError("empty target fibre or action library")
    configurations = tuple(targets)
    names = tuple(actions)
    labels = tuple(next(iter(targets.values())).branches)
    dimension = next(iter(targets.values())).dimension
    for instrument in targets.values():
        instrument.validate_complete()
        if instrument.dimension != dimension:
            raise ValueError("observation fibre uses inconsistent carriers")
    for a in actions.values():
        if set(a) != set(configurations):
            raise ValueError("each action must cover the same observation fibre")
        for instrument in a.values():
            instrument.validate_complete()
            if instrument.dimension != dimension:
                raise ValueError("action library uses inconsistent carriers")
    b = np.concatenate([labelled_choi_vector(targets[x], labels) for x in configurations])
    columns = [np.concatenate([labelled_choi_vector(actions[a][x], labels)
                               for x in configurations]) for a in names]
    matrix = np.column_stack(columns)
    eq = np.vstack([matrix, np.ones((1, len(names)))])
    rhs = np.r_[b, 1.0]
    sol = linprog(np.zeros(len(names)), A_eq=eq, b_eq=rhs,
                  bounds=[(0, None)] * len(names), method="highs")
    if not sol.success:
        return {"status": "NUMERICAL_NO_FEASIBLE_MIXTURE", "solver_status": int(sol.status),
                "scope": "same weights on supplied fibre; one-step full-space labelled instruments",
                "exact_certificate": False}
    residual = float(np.linalg.norm(eq @ sol.x - rhs, ord=np.inf))
    return {"status": "NUMERICAL_FEASIBLE_MIXTURE", "weights": dict(zip(names, map(float, sol.x))),
            "residual": residual,
            "scope": "same weights on supplied fibre; one-step full-space labelled instruments",
            "exact_certificate": False}


def conditional_error_bound(epsilon: float, p: float, q: float) -> float:
    if not all(math.isfinite(v) for v in (epsilon, p, q)) or epsilon < 0 or not 0 < p <= 1 or not 0 < q <= 1:
        raise ValueError("positive acceptance masses and nonnegative full-CQ error required")
    return min(1.0, epsilon / max(p, q))
