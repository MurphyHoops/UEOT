"""Deterministic Lean instances from exact finite representation certificates.

Python checks the external library anchor and emits concrete rational data.
The generated module must then be compiled: its ``by decide`` proof checks
the actual finite matrix identities through ExactCertificate, independently
of the Python precheck. Exporting source is not a successful Lean build.

All user labels live in the JSON manifest. Lean identifiers come only from a
SHA256 digest; numeric Fin indices are bounded constructors, never labels or
modular Fin numerals. Ragged outcome/Kraus families are padded with explicit
zero weights, zero matrices, and zero pullback rows.

This is a producer of individually checkable instances, not a proof of this
Python producer or a formal JSON parser. The Lean presentation theorem does
not certify the Python Gram test or a minimal physical realization.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json

from .instrument import InstrumentLibrary
from .representation_certificate import (
    RepresentationCertificateError,
    verify_representation_certificate,
)


EXPORT_SCHEMA = "ueot_qm.lean_representation_export.v1"
MAX_LITERAL_BITS = 4096
MAX_PADDED_SCALARS = 65536
MAX_SOURCE_BYTES = 8 * 1024 * 1024


class LeanExportError(RepresentationCertificateError):
    """The input or its padded source exceeds the declared export contract."""


@dataclass(frozen=True, slots=True)
class LeanRepresentationExport:
    """Immutable source and metadata; no field asserts successful compilation."""

    module_name: str
    lean_source: str
    canonical_manifest: str

    @property
    def source_sha256(self) -> str:
        return sha256(self.lean_source.encode("utf-8")).hexdigest()

    @property
    def relative_source_path(self) -> str:
        return self.module_name.replace(".", "/") + ".lean"

    def to_dict(self) -> dict:
        """Return fresh metadata, without exposing shared mutable state."""
        return json.loads(self.canonical_manifest)


def _canonical(value: object) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True,
                      separators=(",", ":"), allow_nan=False)


def _plain_json(value: object, depth: int = 0) -> object:
    """Copy only plain schema-compatible JSON, without coercing bad inputs.

    The actual schema is shallower than 32 levels. This bound also rejects
    cycles before Python recursion becomes a resource failure. In particular,
    tuple arrays, nonstring object keys, floats, bools and subclasses are not
    silently normalized into an otherwise valid certificate.
    """
    if depth > 32:
        raise LeanExportError("certificate JSON nesting exceeds the schema contract")
    if type(value) is int:
        if value.bit_length() > MAX_LITERAL_BITS:
            raise LeanExportError("an exact literal exceeds the 4096-bit export limit")
        return value
    if type(value) is str:
        return value
    if type(value) is list:
        return [_plain_json(item, depth + 1) for item in value]
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise LeanExportError("certificate JSON object keys must be plain strings")
        return {key: _plain_json(item, depth + 1) for key, item in value.items()}
    raise LeanExportError("certificate requires plain exact JSON; no bool, float, tuple, or custom objects")


def _rat(numerator: int, denominator: int) -> str:
    if denominator == 1:
        return f"({numerator} : ℚ)"
    return f"(({numerator} : ℚ) / {denominator})"


def _vector(entries: list[str]) -> str:
    return "![" + ", ".join(entries) + "]"


def _matrix(entries: list[list[list[int]]]) -> str:
    def part(offset: int) -> str:
        return "!![" + "; ".join(
            ", ".join(_rat(entry[offset], entry[offset + 1]) for entry in row)
            for row in entries
        ) + "]"
    return "⟨" + part(0) + ", " + part(2) + "⟩"


def _zero_matrix(dimension: int) -> list[list[list[int]]]:
    return [[[0, 1, 0, 1] for _ in range(dimension)] for _ in range(dimension)]


def _fin(index: int, name: str) -> str:
    # An out-of-range value must fail its bound proof, never wrap modulo n.
    return f"(⟨{index}, by decide⟩ : {name})"


def _source(data: dict, layout: dict, module_name: str) -> str:
    dims = layout["dimensions"]
    d, a, o, k, r = (dims[name] for name in
                    ("hilbert", "actions", "outcomes", "kraus", "coordinates"))
    weights = _vector([_vector([_vector([_rat(*term["weight"]) for term in branch["terms"]])
                               for branch in action["outcomes"]])
                       for action in layout["actions"]])
    kraus = _vector([_vector([_vector([_matrix(term["operator"]) for term in branch["terms"]])
                             for branch in action["outcomes"]])
                     for action in layout["actions"]])
    basis = _vector([_matrix(entry["effect"]) for entry in data["basis"]])
    words = _vector([
        "[" + ", ".join(f"({_fin(ai, 'Action')}, {_fin(oi, 'Outcome')})"
                         for ai, oi in word) + "]"
        for word in layout["words"]
    ])
    coefficients = _vector([_vector([_vector([_vector([_rat(entry[0], entry[1])
                                                      for entry in row])
                                             for row in branch["pullback"]])
                                     for branch in action["outcomes"]])
                             for action in layout["actions"]])
    return f'''import UEOTQM.ExactCertificate

/-!
Generated exact numerical instance. Original labels and source bindings are
in the companion manifest. This source has no external verification oracle:
`checked` must be accepted by Lean's kernel before its consequences are used.
-/

namespace {module_name}

open UEOTQM
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Hilbert := Fin {d}
abbrev Action := Fin {a}
abbrev Outcome := Fin {o}
abbrev KrausIndex := Fin {k}
abbrev Coordinate := Fin {r}

def weights : Action → Outcome → KrausIndex → ℚ :=
  {weights}

def krausData : Action → Outcome → KrausIndex → Exact.OperatorData Hilbert :=
  {kraus}

def basisData : Coordinate → Exact.OperatorData Hilbert :=
  {basis}

def words : Coordinate → List (Action × Outcome) :=
  {words}

def coefficients : Action → Outcome → Coordinate → Coordinate → ℚ :=
  {coefficients}

def data : ExactCertificate.Data {d} {a} {o} {k} {r} where
  weight := weights
  kraus := krausData
  basis := basisData
  word := words
  unitIndex := {_fin(0, 'Coordinate')}
  coeff := fun e => coefficients e.1 e.2

theorem checked : ExactCertificate.check data = true := by decide +kernel

noncomputable def instruments := ExactCertificate.instrumentFamily data checked
noncomputable def presentation := ExactCertificate.presentation data checked

theorem all_word_response_iff (ρ σ : Density Hilbert) :
    presentation.coordinates ρ = presentation.coordinates σ ↔
      response instruments ρ = response instruments σ :=
  presentation.coordinates_eq_iff_response_eq ρ σ

theorem finite_tree_coordinates (π : Adaptive.Protocol Action Outcome)
    (ρ : Density Hilbert) (l : π.Leaf) :
    Adaptive.leafProbability instruments π ρ l =
      presentation.recordCoordinates (π.word l) (presentation.coordinates ρ)
        presentation.unitIndex :=
  Adaptive.leafProbability_eq_recordCoordinates_unit instruments presentation π ρ l

theorem all_finite_tree_laws (π : Adaptive.Protocol Action Outcome)
    (ρ σ : Density Hilbert)
    (h : presentation.coordinates ρ = presentation.coordinates σ) :
    Adaptive.leafProbability instruments π ρ =
      Adaptive.leafProbability instruments π σ :=
  Adaptive.leafProbability_eq_of_coordinates_eq instruments presentation h π

theorem complete_tree_normalization (π : Adaptive.Protocol Action Outcome)
    (ρ : Density Hilbert) :
    (∑ l : π.Leaf, Adaptive.leafProbability instruments π ρ l) = 1 :=
  Adaptive.sum_leafProbability instruments π ρ

theorem closed_coordinate_update (x : Set.range presentation.coordinates)
    (e : Action × Outcome) :
    Option.map Subtype.val (presentation.closedCoordinateUpdate x e) =
      presentation.coordinateUpdate x.val e :=
  presentation.closedCoordinateUpdate_map_val x e

#print axioms checked
#print axioms presentation
#print axioms all_word_response_iff
#print axioms finite_tree_coordinates
#print axioms all_finite_tree_laws
#print axioms complete_tree_normalization
#print axioms closed_coordinate_update

end {module_name}
'''


def export_lean_representation(
    certificate: object,
    expected_library: InstrumentLibrary,
    *,
    expected_context_fingerprint: str | None = None,
) -> LeanRepresentationExport:
    """Produce source requiring independent Lean acceptance for this instance.

    The fixed certificate contract has 1<=d<=4, 1<=r<=d² and witness length
    <=d²-1. This exporter also limits input integer literals to 4096 bits,
    padded scalar storage to 65536 entries, and source to 8 MiB. These limits
    constrain evidence generation, not the all-finite-word theorem's horizon.
    No uniform Lean build-time guarantee is implied.
    """
    data = _plain_json(certificate)
    try:
        checked = verify_representation_certificate(
            data, expected_library,
            expected_context_fingerprint=expected_context_fingerprint,
        )
    except RepresentationCertificateError as error:
        raise LeanExportError(str(error)) from error
    d, r = checked.hilbert_dimension, checked.response_dimension
    actions = data["library"]["actions"]
    a = len(actions)
    o = max(len(instrument["outcomes"]) for _, instrument in actions)
    k = max(len(terms) for _, instrument in actions for _, terms in instrument["outcomes"])
    scalar_count = a * o * (k * (1 + 2 * d * d) + r * r) + 2 * r * d * d
    if scalar_count > MAX_PADDED_SCALARS:
        raise LeanExportError("padded exact data exceed the 65536-scalar export limit")
    pullbacks = {(item["action"], item["outcome"]): item["matrix"]
                 for item in data["pullbacks"]}
    positions = {}
    padded = []
    for ai, (action, instrument) in enumerate(actions):
        branches = []
        for oi in range(o):
            present = oi < len(instrument["outcomes"])
            outcome, terms = instrument["outcomes"][oi] if present else (None, [])
            if present:
                positions[action, outcome] = [ai, oi]
            padded_terms = [
                {"index": ki, "original_index": ki if ki < len(terms) else None,
                 "padding": ki >= len(terms),
                 "weight": terms[ki][:2] if ki < len(terms) else [0, 1],
                 "operator": terms[ki][2] if ki < len(terms) else _zero_matrix(d)}
                for ki in range(k)
            ]
            branches.append({
                "index": oi, "label": outcome, "padding": not present,
                "original_kraus_count": len(terms), "terms": padded_terms,
                "pullback": pullbacks[action, outcome] if present else _zero_matrix(r),
            })
        padded.append({"index": ai, "label": action, "outcomes": branches})
    layout = {
        "dimensions": {"hilbert": d, "actions": a, "outcomes": o,
                       "kraus": k, "coordinates": r},
        "actions": padded,
        "words": [[positions[tuple(letter)] for letter in entry["word"]]
                  for entry in data["basis"]],
        "unit_index": 0,
    }
    module_name = "UEOTQM.Generated.Certificate_" + checked.certificate_fingerprint
    source = _source(data, layout, module_name)
    if len(source.encode("utf-8")) > MAX_SOURCE_BYTES:
        raise LeanExportError("generated Lean source exceeds the 8 MiB export limit")
    manifest = {
        "schema": EXPORT_SCHEMA,
        "status": "LEAN_SOURCE_EXPORTED_NOT_COMPILED",
        "module_name": module_name,
        "source_sha256": sha256(source.encode("utf-8")).hexdigest(),
        "certificate_fingerprint": checked.certificate_fingerprint,
        "library_fingerprint": checked.library_fingerprint,
        "context_fingerprint": checked.context_fingerprint,
        "python_precheck": "PASS",
        "certificate": data,
        "index_layout": layout,
        "audit_targets": [module_name + "." + name for name in (
            "checked", "presentation", "all_word_response_iff", "finite_tree_coordinates",
            "all_finite_tree_laws", "complete_tree_normalization", "closed_coordinate_update")],
        "limits": {"max_literal_bits": MAX_LITERAL_BITS,
                   "max_padded_scalars": MAX_PADDED_SCALARS,
                   "padded_scalars": scalar_count, "max_source_bytes": MAX_SOURCE_BYTES},
        "scope": [
            "Lean must independently accept exact weighted completeness, word effects and pullbacks",
            "All finite words and complete finite deterministic adaptive trees of the numeric padded model",
            "Dummy outcomes and terms have zero weights, matrices and pullback coefficients",
            "Labels and their numeric correspondence are retained as external source metadata",
            "No formal correctness claim for this Python exporter or its JSON parser",
            "No Lean proof of the Python Gram test, basis minimality or smaller Hilbert realization",
            "No empirical identification or physical-model applicability claim",
        ],
    }
    return LeanRepresentationExport(module_name, source, _canonical(manifest))
