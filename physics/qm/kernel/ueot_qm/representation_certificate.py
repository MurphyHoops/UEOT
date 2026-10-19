"""Portable exact witnesses for one finite quantum response representation.

The producer exports an existing PredictiveModel.  The checker neither runs
PredictiveModel nor solves its closure problem again: it checks word witnesses
and each claimed local pullback identity directly with exact matrices, and
checks real linear independence by a Frobenius Gram determinant.

The contract covers all finite words of the specified fixed, time-homogeneous
library.  It is not a statistical certificate, a smaller Hilbert realization,
or a Lean verification of this Python/JSON implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json
from typing import TYPE_CHECKING

from .algebra import Matrix, QComplex, identity, matrix_payload, zeros
from .instrument import InstrumentLibrary, KrausTerm

if TYPE_CHECKING:
    from .predictive import PredictiveModel


SCHEMA = "ueot_qm.finite_representation_certificate.v1"
PROTOCOL_CLASS = "all-finite-words-of-fixed-time-homogeneous-library"
SCALAR_DOMAIN = "Gaussian-rational-matrices-real-rational-coefficients"
_FIELDS = {
    "schema", "protocol_class", "scalar_domain", "normalization",
    "hilbert_dimension", "response_dimension", "library_fingerprint",
    "context_fingerprint", "library", "basis", "pullbacks",
}


class RepresentationCertificateError(ValueError):
    """The supplied data fail a declared representation contract."""


@dataclass(frozen=True, slots=True)
class RepresentationVerification:
    """Exact local checks passed for these bytes and this declared context.

    The two span inclusions follow mathematically from generation and closure.
    This receipt records executable checks; it is not a proof-assistant token.
    ``response_dimension`` includes the constant trace coordinate.
    """

    certificate_fingerprint: str
    library_fingerprint: str
    context_fingerprint: str
    hilbert_dimension: int
    response_dimension: int
    branch_count: int
    checked_word_count: int
    checked_pullback_identity_count: int
    gram_determinant: Fraction
    protocol_class: str = PROTOCOL_CLASS


def _fail(message: str) -> None:
    raise RepresentationCertificateError(message)


def _canonical(value: object) -> str:
    try:
        return json.dumps(
            value, ensure_ascii=True, sort_keys=True, separators=(",", ":"),
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise RepresentationCertificateError("certificate must contain exact JSON data") from error


def _hash(value: object) -> str:
    return sha256(_canonical(value).encode("utf-8")).hexdigest()


def _dictionary(value: object, fields: set[str], name: str) -> dict:
    if type(value) is not dict or set(value) != fields:
        _fail(f"{name} must contain exactly the declared fields")
    return value


def _integer(value: object, name: str) -> int:
    # JSON booleans compare equal to Python integers; reject them explicitly.
    if type(value) is not int:
        _fail(f"{name} must be an integer, not a float, string, or boolean")
    return value


def _fraction(numerator: object, denominator: object, name: str) -> Fraction:
    numerator = _integer(numerator, name)
    denominator = _integer(denominator, name)
    if denominator <= 0:
        _fail(f"{name} must have a positive denominator")
    value = Fraction(numerator, denominator)
    if (value.numerator, value.denominator) != (numerator, denominator):
        _fail(f"{name} must be in reduced canonical form")
    return value


def _matrix(value: object, dimension: int, name: str) -> Matrix:
    if type(value) is not list or len(value) != dimension:
        _fail(f"{name} has the wrong number of rows")
    rows = []
    for row in value:
        if type(row) is not list or len(row) != dimension:
            _fail(f"{name} has the wrong number of columns")
        result = []
        for entry in row:
            if type(entry) is not list or len(entry) != 4:
                _fail(f"{name} entries must be [real numerator, denominator, imaginary numerator, denominator]")
            result.append(QComplex(
                _fraction(entry[0], entry[1], name),
                _fraction(entry[2], entry[3], name),
            ))
        rows.append(result)
    return Matrix(rows)


def _label(value: object) -> str:
    if type(value) is not str or not value:
        _fail("action and outcome labels must be nonempty strings")
    return value


def _pullback(terms: tuple[KrausTerm, ...], effect: Matrix) -> Matrix:
    """Recompute from Kraus data, without using Instrument.adjoint."""
    result = zeros(effect.nrows)
    for term in terms:
        operator = term.operator
        result += (operator.adjoint() @ effect @ operator) * term.weight
    return result


def _checked_library(
    library: InstrumentLibrary,
) -> tuple[dict, dict[tuple[str, str], tuple[KrausTerm, ...]]]:
    """Recompute the public library payload, fingerprint, and completeness."""
    if not isinstance(library, InstrumentLibrary):
        _fail("expected_library must be a validated InstrumentLibrary")
    dimension = _integer(library.dimension, "Hilbert dimension")
    if not 1 <= dimension <= 4:
        _fail("this certificate implementation supports Hilbert dimensions 1..4")
    if not library.entries:
        _fail("the library must declare at least one action")
    action_names = tuple(_label(action) for action, _ in library.entries)
    if action_names != tuple(sorted(set(action_names))):
        _fail("library actions must be unique and canonically ordered")
    actions = []
    branches = {}
    for action, instrument in library.entries:
        if instrument.dimension != dimension or not instrument.branches:
            _fail("all instruments must share the declared dimension and have outcomes")
        names = tuple(_label(outcome) for outcome, _ in instrument.branches)
        if names != tuple(sorted(set(names))):
            _fail("instrument outcomes must be unique and canonically ordered")
        total = zeros(dimension)
        outcomes = []
        term_count = 0
        for outcome, terms in instrument.branches:
            terms = tuple(terms)
            branches[action, outcome] = terms
            serialized = []
            for term in terms:
                if not isinstance(term, KrausTerm):
                    _fail("the public branch must contain KrausTerm values")
                if term.operator.shape != (dimension, dimension):
                    _fail("a Kraus operator has the wrong Hilbert dimension")
                if not isinstance(term.weight, Fraction) or term.weight < 0:
                    _fail("Kraus weights must be nonnegative exact rationals")
                total += (term.operator.adjoint() @ term.operator) * term.weight
                serialized.append([
                    term.weight.numerator, term.weight.denominator,
                    matrix_payload(term.operator),
                ])
                term_count += 1
            outcomes.append([outcome, serialized])
        if not term_count or total != identity(dimension):
            _fail("the public action fails exact Kraus completeness")
        actions.append([action, {"dimension": dimension, "outcomes": outcomes}])
    payload = {
        "schema": "ueot_qm.instrument_library.v1",
        "protocol_class": "all-finite-causal-combinations",
        "actions": actions,
    }
    if _hash(payload) != library.fingerprint:
        _fail("the public library data do not match its stored fingerprint")
    return payload, branches


def _context_fingerprint(library_fingerprint: str, basis: tuple[Matrix, ...]) -> str:
    return _hash({
        "schema": "ueot_qm.predictive_model.v1",
        "library_fingerprint": library_fingerprint,
        "normalization": "first-coordinate-is-trace",
        "basis": [matrix_payload(effect) for effect in basis],
    })


def export_representation_certificate(model: PredictiveModel) -> dict:
    """Export an existing model and actual chronological word witnesses.

    The producer finds each basis element as a pullback of an earlier one;
    it does not invent a word from matching sampled response values.  The
    resulting ordinary dictionary can be serialized with ``json.dumps``.
    Verification is a separate call and is never represented by an export.
    """
    from .predictive import PredictiveModel

    if not isinstance(model, PredictiveModel):
        _fail("the producer requires an existing PredictiveModel")
    library_payload, branches = _checked_library(model.library)
    basis = model.basis
    if not basis or basis[0] != identity(model.hilbert_dimension):
        _fail("the model must start with the identity effect")
    words: list[tuple[tuple[str, str], ...]] = [()]
    for index in range(1, len(basis)):
        witness = None
        for parent in range(index):
            for action, outcome in branches:
                # This is the producer's public model interface.  Verification
                # uses the independent Kraus expression in _pullback instead.
                if model.library.adjoint(basis[parent], action, outcome) == basis[index]:
                    witness = ((action, outcome),) + words[parent]
                    break
            if witness is not None:
                break
        if witness is None:
            _fail("a model basis element has no earlier generated-word witness")
        words.append(witness)
    return {
        "schema": SCHEMA,
        "protocol_class": PROTOCOL_CLASS,
        "scalar_domain": SCALAR_DOMAIN,
        "normalization": "first-coordinate-is-trace",
        "hilbert_dimension": model.hilbert_dimension,
        "response_dimension": model.dimension,
        "library_fingerprint": model.library.fingerprint,
        "context_fingerprint": model.fingerprint,
        "library": library_payload,
        "basis": [
            {"effect": matrix_payload(effect), "word": [list(letter) for letter in word]}
            for effect, word in zip(basis, words)
        ],
        "pullbacks": [
            {"action": action, "outcome": outcome,
             "matrix": matrix_payload(model.pullback_matrix(action, outcome))}
            for action, outcome in branches
        ],
    }


def verify_representation_certificate(
    certificate: object,
    expected_library: InstrumentLibrary,
    *,
    expected_context_fingerprint: str | None = None,
) -> RepresentationVerification:
    """Check exact witnesses independently of the closure search/solver.

    The caller supplies the intended library as an external context anchor.
    With an expected context fingerprint the basis identity is also pinned.
    Without it, another correctly generated independent closed word basis
    for the same library is valid and may receive its own context fingerprint.

    Every branch and every basis index is checked, including impossible
    outcomes.  Witnesses are limited to d^2-1 letters, the maximum needed by
    the producer's basis-generation chain (at most 15 for d<=4).  This is a
    resource limit on exported evidence, not a horizon limit on the certified
    word language.  A finite word's chronological order is respected by applying
    Heisenberg pullbacks in reverse order, starting from I.
    """
    data = _dictionary(certificate, _FIELDS, "representation certificate")
    if data["schema"] != SCHEMA:
        _fail("unsupported representation certificate schema")
    if data["protocol_class"] != PROTOCOL_CLASS:
        _fail("unsupported protocol class: the library must be fixed and time homogeneous")
    if data["scalar_domain"] != SCALAR_DOMAIN:
        _fail("the certificate must use exact Gaussian rational data")
    if data["normalization"] != "first-coordinate-is-trace":
        _fail("the normalization coordinate contract differs")
    dimension = _integer(data["hilbert_dimension"], "Hilbert dimension")
    if not 1 <= dimension <= 4:
        _fail("this certificate implementation supports Hilbert dimensions 1..4")
    size = _integer(data["response_dimension"], "response dimension")
    if not 1 <= size <= dimension ** 2:
        _fail("response dimension must lie between 1 and the Hermitian dimension d^2")
    library_payload, branches = _checked_library(expected_library)
    if dimension != expected_library.dimension:
        _fail("the Hilbert dimension differs from the intended library")
    if data["library_fingerprint"] != expected_library.fingerprint:
        _fail("the certificate belongs to a different library")
    if _canonical(data["library"]) != _canonical(library_payload):
        _fail("the serialized Kraus library differs from the intended library")
    if type(data["basis"]) is not list or len(data["basis"]) != size:
        _fail("the certificate must provide every declared basis effect")
    effects = []
    words = []
    for index, item in enumerate(data["basis"]):
        item = _dictionary(item, {"effect", "word"}, "basis element")
        effect = _matrix(item["effect"], dimension, "basis effect")
        if not effect.is_hermitian():
            _fail("every basis effect must be Hermitian")
        if type(item["word"]) is not list:
            _fail("a word must be a finite JSON list of action/outcome pairs")
        if len(item["word"]) > dimension ** 2 - 1:
            _fail("word witness exceeds the supported d^2-1 generation-depth bound")
        word = []
        for letter in item["word"]:
            if type(letter) is not list or len(letter) != 2:
                _fail("every word letter must be an action/outcome pair")
            pair = (_label(letter[0]), _label(letter[1]))
            if pair not in branches:
                _fail("a word uses an undeclared action/outcome")
            word.append(pair)
        if index == 0 and (word or effect != identity(dimension)):
            _fail("basis[0] must be I with the empty-word witness")
        generated = identity(dimension)
        for pair in reversed(word):
            generated = _pullback(branches[pair], generated)
        if generated != effect:
            _fail("a basis effect differs from its actual chronological word effect")
        effects.append(effect)
        words.append(tuple(word))
    basis = tuple(effects)
    # This real Gram determinant tests independence without the producer's
    # Hermitian vectorization or linear_coordinates Gaussian solver.
    gram = Matrix([(left.adjoint() @ right).trace() for right in basis] for left in basis)
    if any(entry.imag for row in gram for entry in row):
        _fail("the Hermitian Frobenius Gram matrix must be exactly real")
    gram_determinant = gram.determinant()
    if gram_determinant.imag or gram_determinant.real <= 0:
        _fail("the word-effect basis is not real linearly independent")
    fingerprint = _context_fingerprint(expected_library.fingerprint, basis)
    if data["context_fingerprint"] != fingerprint:
        _fail("the basis data do not match their context fingerprint")
    if expected_context_fingerprint is not None and fingerprint != expected_context_fingerprint:
        _fail("the representation differs from the intended model context")
    if type(data["pullbacks"]) is not list or len(data["pullbacks"]) != len(branches):
        _fail("the certificate must provide every declared branch pullback")
    seen = set()
    for item in data["pullbacks"]:
        item = _dictionary(item, {"action", "outcome", "matrix"}, "branch pullback")
        pair = (_label(item["action"]), _label(item["outcome"]))
        if pair not in branches or pair in seen:
            _fail("branch pullbacks must cover the library exactly once")
        seen.add(pair)
        matrix = _matrix(item["matrix"], size, "pullback matrix")
        if any(entry.imag for row in matrix for entry in row):
            _fail("pullback coefficients must be real rationals")
        for index, effect in enumerate(basis):
            claimed = zeros(dimension)
            for coefficient, generator in zip(matrix[index], basis):
                claimed += generator * coefficient.real
            if claimed != _pullback(branches[pair], effect):
                _fail("a local pullback identity fails: Phi*(B_j) != sum_k A[j,k] B_k")
    if seen != set(branches):
        _fail("a declared library branch is missing")
    return RepresentationVerification(
        certificate_fingerprint=_hash(data),
        library_fingerprint=expected_library.fingerprint,
        context_fingerprint=fingerprint,
        hilbert_dimension=dimension,
        response_dimension=size,
        branch_count=len(branches),
        checked_word_count=len(words),
        checked_pullback_identity_count=size * len(branches),
        gram_determinant=gram_determinant.real,
    )
