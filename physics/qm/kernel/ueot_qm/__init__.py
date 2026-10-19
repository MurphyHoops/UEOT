"""Exact small-dimensional UEOT-QM operations and predictive quotients.

Physical assumptions are explicit: Gaussian-rational complex matrices and
complete weighted Kraus instruments on dimensions 1..4.  The executable
checks and response algorithms in this package are not machine proofs in
Lean and do not reconstruct quantum theory from the generic UEOT Core.
"""

from .algebra import (
    MAX_PSD_DIMENSION,
    Matrix,
    QComplex,
    diagonal,
    hermitian_vector,
    identity,
    linear_coordinates,
    outer,
    rational,
    real_trace,
    validate_density,
    zeros,
)
from .instrument import Instrument, InstrumentLibrary, KrausTerm, ProtocolNode, Record
from .predictive import EncodedState, PredictiveModel

from .representation_certificate import (
    RepresentationCertificateError,
    RepresentationVerification,
    export_representation_certificate,
    verify_representation_certificate,
)
from .spectrum import (
    Orientation, MatterKind, Family, ExtraMatter, CubicCompletion,
    WeakWindow, Spectrum, inspect_spectrum, SU3Representation, Weyl331,
    local_331_anomalies, generalized_331_fields,
)


__all__ = [
    "MAX_PSD_DIMENSION",
    "QComplex",
    "Matrix",
    "identity",
    "zeros",
    "diagonal",
    "outer",
    "rational",
    "real_trace",
    "validate_density",
    "hermitian_vector",
    "linear_coordinates",
    "KrausTerm",
    "Instrument",
    "InstrumentLibrary",
    "ProtocolNode",
    "Record",
    "EncodedState",
    "PredictiveModel",
    "RepresentationCertificateError",
    "RepresentationVerification",
    "export_representation_certificate",
    "verify_representation_certificate",
    "Orientation",
    "MatterKind",
    "Family",
    "ExtraMatter",
    "CubicCompletion",
    "WeakWindow",
    "Spectrum",
    "inspect_spectrum",
    "SU3Representation",
    "Weyl331",
    "local_331_anomalies",
    "generalized_331_fields",
]
