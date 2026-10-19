"""Exact finite-spectrum adapters for the conditional G3 selector.

Representation coefficients and an EFT window are declared physical inputs.
This module sums actual entries before checking the selector contract.  It
does not certify the existence of that window or a complete quantum field
theory.  Python execution is not asserted to be verified by the Lean module.
"""

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction as F
from hashlib import sha256
import json


def _natural(value, name, *, positive=False):
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer, not a float or boolean")
    if value < (1 if positive else 0):
        raise ValueError(f"{name} must be {'positive' if positive else 'nonnegative'}")
    return value


def _rational(value, name):
    if type(value) is not int and not isinstance(value, F):
        raise TypeError(f"{name} must be an integer or Fraction")
    return F(value)


def _label(value, name):
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a nonempty label")
    return value


def _boolean(value, name):
    if type(value) is not bool:
        raise TypeError(f"{name} must be a boolean declaration")
    return value


def _entries(values, expected, name):
    result = tuple(values)
    if any(not isinstance(value, expected) for value in result):
        raise TypeError(f"{name} contains an invalid entry")
    labels = [value.name for value in result]
    if len(set(labels)) != len(labels):
        raise ValueError(f"{name} contains duplicate labels")
    return result


def _qtext(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else str(value)


class Orientation(Enum):
    R = "R"
    RBAR = "Rbar"

    @property
    def sign(self):
        return 1 if self is Orientation.R else -1


class MatterKind(Enum):
    WEYL = "left-handed Weyl"
    COMPLEX_SCALAR = "complex scalar"
    REAL_SCALAR = "real scalar"

    @property
    def screening_factor(self):
        return {MatterKind.WEYL: F(2, 3),
                MatterKind.COMPLEX_SCALAR: F(1, 3),
                MatterKind.REAL_SCALAR: F(1, 6)}[self]


@dataclass(frozen=True, slots=True)
class Family:
    """One color-singlet lepton and one color-fundamental quark multiplet.

    R/Rbar refer to the selected horizontal/extended-weak cubic channel, not
    the color orientation. Each multiplet yields one ordinary weak doublet
    per color if active. The two activity flags concern the weak window only.
    """

    name: str
    lepton: Orientation
    quark: Orientation
    lepton_active: bool = True
    quark_active: bool = True

    def __post_init__(self):
        _label(self.name, "family name")
        for value in (self.lepton, self.quark):
            if not isinstance(value, Orientation):
                raise TypeError("family representations must be Orientation values")
        _boolean(self.lepton_active, "lepton_active")
        _boolean(self.quark_active, "quark_active")


@dataclass(frozen=True, slots=True)
class ExtraMatter:
    """Extra matter with supplied full-row coefficients in the two inventories.

    weak_index includes every spectator multiplicity except copies. It is
    the total SU(2) Dynkin index per copy, not automatically a doublet index.
    cubic_unit is the signed selected-channel contribution per copy. Weak
    inactivity does not silently remove a parent-spectrum anomaly term.
    """

    name: str
    kind: MatterKind
    copies: int
    weak_index: F
    cubic_unit: F = F(0)
    weak_active: bool = True

    def __post_init__(self):
        _label(self.name, "extra matter name")
        if not isinstance(self.kind, MatterKind):
            raise TypeError("extra matter kind must be a MatterKind")
        _natural(self.copies, "copies")
        index = _rational(self.weak_index, "weak_index")
        cubic = _rational(self.cubic_unit, "cubic_unit")
        if index < 0:
            raise ValueError("ordinary matter Dynkin indices cannot be negative")
        if self.kind is not MatterKind.WEYL and cubic != 0:
            raise ValueError("a scalar cannot supply a chiral cubic anomaly")
        _boolean(self.weak_active, "weak_active")
        object.__setattr__(self, "weak_index", index)
        object.__setattr__(self, "cubic_unit", cubic)

    @property
    def cubic(self):
        return self.copies * self.cubic_unit if self.kind is MatterKind.WEYL else F(0)

    @property
    def screening(self):
        if not self.weak_active:
            return F(0)
        return self.copies * self.weak_index * self.kind.screening_factor


@dataclass(frozen=True, slots=True)
class CubicCompletion:
    """A declared signed completion contribution, with its external source.

    Supplying a number does not prove that its proposed inflow or completion
    mechanism exists. The selector requires the combined extra sum to vanish.
    """

    name: str
    coefficient: F
    source: str

    def __post_init__(self):
        _label(self.name, "completion name")
        _label(self.source, "completion source")
        object.__setattr__(self, "coefficient", _rational(self.coefficient, "coefficient"))


@dataclass(frozen=True, slots=True)
class WeakWindow:
    """Explicit model declarations; these booleans are not physical proofs."""

    name: str
    su2_carrier: bool
    perturbative: bool
    active_spectrum_complete: bool
    matching_established: bool

    def __post_init__(self):
        _label(self.name, "weak window name")
        for field in ("su2_carrier", "perturbative", "active_spectrum_complete",
                      "matching_established"):
            _boolean(getattr(self, field), field)

    @property
    def declared_valid(self):
        return (self.su2_carrier and self.perturbative
                and self.active_spectrum_complete and self.matching_established)


@dataclass(frozen=True, slots=True)
class Spectrum:
    nc: int
    anomaly_unit: F
    families: tuple
    window: WeakWindow
    extra_matter: tuple = ()
    completions: tuple = ()

    def __post_init__(self):
        _natural(self.nc, "nc", positive=True)
        object.__setattr__(self, "anomaly_unit", _rational(self.anomaly_unit, "anomaly_unit"))
        object.__setattr__(self, "families", _entries(self.families, Family, "families"))
        object.__setattr__(self, "extra_matter", _entries(self.extra_matter, ExtraMatter,
                                                        "extra_matter"))
        object.__setattr__(self, "completions", _entries(self.completions, CubicCompletion,
                                                       "completions"))
        if not isinstance(self.window, WeakWindow):
            raise TypeError("window must be an explicit WeakWindow declaration")


@dataclass(frozen=True, slots=True)
class ExactReceipt:
    """Immutable canonical JSON; callers receive fresh copies from to_dict."""

    canonical_json: str

    @classmethod
    def from_dict(cls, payload):
        return cls(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False))

    @property
    def sha256(self):
        return sha256(self.canonical_json.encode()).hexdigest()

    def to_dict(self):
        return json.loads(self.canonical_json)


def inspect_spectrum(spectrum):
    """Sum entries, expose failed physical contracts, and conditionally select.

    The function accepts no family-count target, final anomaly equation, or
    final screening budget. All numeric premises are computed from rows.
    """
    if not isinstance(spectrum, Spectrum):
        raise TypeError("inspect_spectrum requires a Spectrum")
    nc, a = spectrum.nc, spectrum.anomaly_unit
    rows = []
    family_cubic = F(0)
    family_screening = F(0)
    for family in spectrum.families:
        for role, orientation, colors, active in (
                ("lepton", family.lepton, 1, family.lepton_active),
                ("quark", family.quark, nc, family.quark_active)):
            cubic = colors * a * orientation.sign
            screening = F(colors, 3) if active else F(0)
            family_cubic += cubic
            family_screening += screening
            rows.append({"inventory": "ordinary", "family": family.name, "role": role,
                         "representation": orientation.value, "color_multiplicity": colors,
                         "cubic_unit": _qtext(a), "cubic_sign": orientation.sign,
                         "cubic_contribution": _qtext(cubic), "weak_active": active,
                         "weak_doublets": colors if active else 0,
                         "weak_index_per_doublet": "1/2",
                         "screening_contribution": _qtext(screening)})
    extra_cubic = F(0)
    extra_screening = F(0)
    for extra in spectrum.extra_matter:
        extra_cubic += extra.cubic
        extra_screening += extra.screening
        rows.append({"inventory": "extra matter", "name": extra.name,
                     "kind": extra.kind.value, "copies": extra.copies,
                     "weak_index_per_copy": _qtext(extra.weak_index),
                     "screening_factor": _qtext(extra.kind.screening_factor),
                     "cubic_unit": _qtext(extra.cubic_unit),
                     "cubic_contribution": _qtext(extra.cubic),
                     "weak_active": extra.weak_active,
                     "screening_contribution": _qtext(extra.screening)})
    completion_cubic = F(0)
    for completion in spectrum.completions:
        completion_cubic += completion.coefficient
        rows.append({"inventory": "declared completion", "name": completion.name,
                     "source": completion.source,
                     "cubic_contribution": _qtext(completion.coefficient),
                     "screening_contribution": "0",
                     "scope": "selected cubic channel only; physical mechanism unverified"})

    nf = len(spectrum.families)
    ell = sum(f.lepton is Orientation.R for f in spectrum.families)
    k = sum(f.quark is Orientation.R for f in spectrum.families)
    other_cubic = extra_cubic + completion_cubic
    total_cubic = family_cubic + other_cubic
    all_active = all(f.lepton_active and f.quark_active for f in spectrum.families)
    b2 = F(22, 3) - family_screening - extra_screening if spectrum.window.su2_carrier else None
    checks = {
        "complex_color_template": nc >= 3,
        "families_nonempty": nf > 0,
        "nonzero_anomaly_unit": a != 0,
        "homogeneous_lepton_R": ell == nf,
        "extra_cubic_sum_zero": other_cubic == 0,
        "total_cubic_cancelled": total_cubic == 0,
        "weak_window_declared": spectrum.window.declared_valid,
        "all_ordinary_doublets_active": all_active,
        "positive_full_one_loop_coefficient": b2 is not None and b2 > 0,
    }
    eligible = all(checks.values())
    residual = 2 * nc * k + nf - nc * nf
    budget = nf * (nc + 1)
    if eligible and (residual != 0 or budget >= 22 or (nc, nf, k) != (3, 3, 1)):
        raise ArithmeticError("derived spectrum premises contradict the proved selector")
    window = {name: getattr(spectrum.window, name) for name in
              ("name", "su2_carrier", "perturbative", "active_spectrum_complete",
               "matching_established")}
    return ExactReceipt.from_dict({
        "schema": "ueot_qm.spectrum_bridge.v1",
        "status": "SELECTOR_APPLIES" if eligible else "OUTSIDE_SELECTOR_CONTRACT",
        "nc": nc, "nf": nf, "lepton_R_count": ell, "quark_R_count": k,
        "anomaly_unit": _qtext(a), "rows": rows, "window_declarations": window,
        "sums": {"family_cubic": _qtext(family_cubic),
                 "extra_matter_cubic": _qtext(extra_cubic),
                 "completion_cubic": _qtext(completion_cubic),
                 "total_cubic": _qtext(total_cubic),
                 "ordinary_screening": _qtext(family_screening),
                 "extra_screening": _qtext(extra_screening),
                 "weak_b2": _qtext(b2) if b2 is not None else None},
        "contract_checks": checks,
        "failed_conditions": [name for name, passed in checks.items() if not passed],
        "derived": {"homogeneous_integer_residual": residual,
                    "ordinary_doublet_budget": budget,
                    "selector_premises_derived": eligible,
                    "selected_counts": {"nc": nc, "nf": nf, "k": k} if eligible else None},
        "scope": [
            "Cubic sign, representation multiplicities, and one-loop weights are sector inputs",
            "WeakWindow values declare external physical obligations; booleans are not proofs",
            "Additional cubic terms certify no inflow or matching mechanism by themselves",
            "The positive coefficient concerns the specified SU(2) window, not all-scale UV behavior",
            "No global-anomaly, vacuum, mass, phenomenology, or Python-to-Lean refinement claim",
        ],
    })


class SU3Representation(Enum):
    SINGLET = "1"
    FUNDAMENTAL = "3"
    ANTIFUNDAMENTAL = "3bar"

    @property
    def dimension(self):
        return 1 if self is SU3Representation.SINGLET else 3

    @property
    def index(self):
        return F(0) if self is SU3Representation.SINGLET else F(1, 2)

    @property
    def cubic(self):
        return {SU3Representation.SINGLET: 0, SU3Representation.FUNDAMENTAL: 1,
                SU3Representation.ANTIFUNDAMENTAL: -1}[self]


@dataclass(frozen=True, slots=True)
class Weyl331:
    """An explicitly left-handed Weyl row for su(3)C + su(3)L + u(1)X.

    Only singlet, fundamental, and antifundamental nonabelian representations
    are supported. Their dimension, quadratic index, and cubic index are
    declared conventions; arbitrary representation theory is outside scope.
    """

    name: str
    color: SU3Representation
    left: SU3Representation
    x: F
    copies: int = 1

    def __post_init__(self):
        _label(self.name, "Weyl row name")
        if not isinstance(self.color, SU3Representation) or not isinstance(self.left, SU3Representation):
            raise TypeError("Weyl representations must be supported SU3Representation values")
        _natural(self.copies, "Weyl copies")
        object.__setattr__(self, "x", _rational(self.x, "X charge"))


def local_331_anomalies(fields):
    """Independently sum six local perturbative anomaly coefficients from rows."""
    fields = _entries(fields, Weyl331, "Weyl fields")
    totals = {name: F(0) for name in ("C3", "L3", "C2X", "L2X", "grav2X", "X3")}
    rows = []
    for field in fields:
        dc, dl, x, n = field.color.dimension, field.left.dimension, field.x, field.copies
        terms = {"C3": n * dl * field.color.cubic,
                 "L3": n * dc * field.left.cubic,
                 "C2X": n * dl * field.color.index * x,
                 "L2X": n * dc * field.left.index * x,
                 "grav2X": n * dc * dl * x,
                 "X3": n * dc * dl * x ** 3}
        for name, value in terms.items():
            totals[name] += value
        rows.append({"name": field.name, "color": field.color.value, "left": field.left.value,
                     "X": _qtext(x), "copies": n,
                     "contributions": {name: _qtext(value) for name, value in terms.items()}})
    return ExactReceipt.from_dict({
        "schema": "ueot_qm.local_331_anomalies.v1", "rows": rows,
        "totals": {name: _qtext(value) for name, value in totals.items()},
        "all_six_cancel": all(value == 0 for value in totals.values()),
        "scope": "Declared SU(3) fundamental conventions; six local anomaly sums only",
    })


def generalized_331_fields(families, beta_over_sqrt3, *, include_exotic_lepton_completion=True):
    """Produce explicit left-handed rows with Q = T3 + beta T8 + X.

    z = beta/sqrt(3) is exact rational. Color is fixed to SU(3) here. Ordinary
    lepton and quark charges are (0,-1) and (2/3,-1/3); singlet completions are
    listed per family. The family count and both orientations remain inputs.
    """
    families = _entries(families, Family, "families")
    z = _rational(beta_over_sqrt3, "beta_over_sqrt3")
    _boolean(include_exotic_lepton_completion, "include_exotic_lepton_completion")
    singlet, fund, anti = (SU3Representation.SINGLET, SU3Representation.FUNDAMENTAL,
                           SU3Representation.ANTIFUNDAMENTAL)
    rows = []
    for family in families:
        sl, sq = family.lepton.sign, family.quark.sign
        lr = fund if sl == 1 else anti
        qr = fund if sq == 1 else anti
        xl, xq = -F(1, 2) - sl * z / 2, F(1, 6) - sq * z / 2
        qe, qj = -F(1, 2) - sl * 3 * z / 2, F(1, 6) - sq * 3 * z / 2
        prefix = family.name + "/"
        rows.extend((Weyl331(prefix + "L", singlet, lr, xl),
                     Weyl331(prefix + "ec", singlet, singlet, F(1)),
                     Weyl331(prefix + "Q", fund, qr, xq),
                     Weyl331(prefix + "uc", anti, singlet, -F(2, 3)),
                     Weyl331(prefix + "dc", anti, singlet, F(1, 3)),
                     Weyl331(prefix + "Jc", anti, singlet, -qj)))
        if include_exotic_lepton_completion:
            rows.append(Weyl331(prefix + "Ec", singlet, singlet, -qe))
    return tuple(rows)
