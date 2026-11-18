"""Shared serialization and observed-event helpers; no simulation truth access."""
from __future__ import annotations
import hashlib, importlib.util, json, os
from fractions import Fraction
from pathlib import Path
import numpy as np

BASE = Path(__file__).resolve().parent

def load_json(path):
    return json.loads(Path(path).read_text())

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def dump_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def rational(value):
    return float(Fraction(str(value)))

def dynamics():
    default = BASE / "dynamics.py"
    if not default.exists():
        default = BASE.parent / "work_b" / "dynamics.py"
    path = Path(os.environ.get("UEOT_DYNAMICS_PATH", str(default)))
    spec = importlib.util.spec_from_file_location("persistent_bath_c_input", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module, path

def observable(name):
    p = {"I": np.eye(2, dtype=complex), "X": np.array([[0,1],[1,0]],complex),
         "Y": np.array([[0,-1j],[1j,0]],complex), "Z": np.diag([1.,-1.]).astype(complex)}
    return np.kron(p[name[0]], p[name[1]])

def event_probabilities(blocks, eta, name):
    """Retain the four stopped records and both terminal outcomes, unconditioned."""
    op = observable(name)
    result = []
    for record in ("f", "pf", "ppf", "ppp"):
        block = blocks[record]
        weight = float(np.trace(block).real)
        mean = float(np.trace(op @ block).real)
        result.extend(((weight - eta*mean)/2, (weight + eta*mean)/2))
    p = np.asarray(result)
    if np.min(p) < -1e-12 or abs(p.sum()-1) > 1e-10:
        raise ValueError("invalid complete event distribution")
    return p

def iv_endpoint_fraction(value, upper=False):
    sign, man, exp, _ = value._mpi_[int(upper)]
    result = Fraction((-1 if sign else 1) * man)
    return result * (Fraction(2) ** exp)

def outward_fraction(value, upper=False, digits=12):
    fraction = iv_endpoint_fraction(value, upper)
    scale = 10**digits
    scaled = fraction * scale
    integer = scaled.numerator // scaled.denominator
    if upper and Fraction(integer) != scaled:
        integer += 1
    return Fraction(integer, scale)

def decimal_string(value, digits=12):
    value = Fraction(value)
    scale = 10**digits
    integer = (value*scale + Fraction(1,2)).numerator // (value*scale + Fraction(1,2)).denominator
    sign = "-" if integer < 0 else ""
    integer = abs(integer)
    return f"{sign}{integer//scale}.{integer%scale:0{digits}d}"
