"""Kernel 1.2: portable response witnesses and explicit spectrum rows.

Run from any directory. The JSON contains the actual finite representation
certificates, their independently recomputed receipts, and conditional spectrum
results. Rational strings are exact. No external empirical data are used.
"""

from dataclasses import asdict, replace
from fractions import Fraction as F
import json

from ueot_qm import (
    Matrix, QComplex, diagonal, identity, KrausTerm, Instrument,
    InstrumentLibrary, PredictiveModel, ProtocolNode,
    export_representation_certificate, verify_representation_certificate,
    Orientation as O, MatterKind as M, Family, ExtraMatter, CubicCompletion,
    WeakWindow, Spectrum, inspect_spectrum,
    generalized_331_fields, local_331_anomalies,
)


def main():
    p0, p1 = diagonal([1, 0]), diagonal([0, 1])
    choices = {
        "Z": Instrument({"0": [KrausTerm(p0)], "1": [KrausTerm(p1)]}),
        "H": Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), F(1, 2))]}),
        "S": Instrument({"ok": [KrausTerm(diagonal([1, QComplex(0, 1)]))]}),
    }
    representations = {}
    for actions in (("Z",), ("H", "Z"), ("H", "S", "Z")):
        library = InstrumentLibrary({name: choices[name] for name in actions})
        model = PredictiveModel(library)
        certificate = export_representation_certificate(model)
        receipt = verify_representation_certificate(
            certificate, library, expected_context_fingerprint=model.context_fingerprint)
        representations["+".join(actions)] = {
            "certificate": certificate,
            "independent_verification": asdict(receipt),
        }

    library = InstrumentLibrary({name: choices[name] for name in ("H", "Z")})
    model = PredictiveModel(library)
    final_z = ProtocolNode("Z", {"0": None, "1": None})
    adaptive = ProtocolNode("Z", {
        "0": ProtocolNode("H", {"ok": final_z}),
        "1": final_z,
    })
    rho = identity(2) / 2
    dense = library.protocol_law(rho, adaptive)
    coordinates = model.protocol_law(model.encode(rho), adaptive)
    if dense != coordinates or sum(dense.values()) != 1:
        raise ArithmeticError("the complete adaptive law is inconsistent")

    def three(prefix):
        return (Family(prefix + "1", O.R, O.R),
                Family(prefix + "2", O.R, O.RBAR),
                Family(prefix + "3", O.R, O.RBAR))

    ordinary = three("a")
    mixed = (Family("m1", O.R, O.R), Family("m2", O.RBAR, O.RBAR))
    one = (Family("one", O.R, O.RBAR),)
    six = ordinary + three("b")
    window = WeakWindow("declared complete ordinary SU(2) window", True, True, True, True)
    higgs = ExtraMatter("H", M.COMPLEX_SCALAR, 1, F(1, 2))
    cases = {
        "three_with_higgs": Spectrum(3, 1, ordinary, window, (higgs,)),
        "mixed_two": Spectrum(3, 1, mixed, window),
        "replicated_six": Spectrum(3, 1, six, window),
        "compensated_one": Spectrum(3, 1, one, window, (), (
            CubicCompletion("extra", 2, "declared external contribution; mechanism open"),)),
        "zero_anomaly_unit": Spectrum(3, 0, one, window),
        "twenty_scalar_doublets": Spectrum(3, 1, ordinary, window, (
            ExtraMatter("twenty H", M.COMPLEX_SCALAR, 20, F(1, 2)),)),
        "six_with_inactive_second_packet": Spectrum(3, 1, ordinary + tuple(
            replace(f, lepton_active=False, quark_active=False) for f in three("b")), window),
    }
    spectra = {name: inspect_spectrum(value).to_dict() for name, value in cases.items()}
    six_anomalies = {
        name: local_331_anomalies(generalized_331_fields(families, F(1, 5))).to_dict()
        for name, families in (("three", ordinary), ("mixed_two", mixed), ("six", six))
    }
    six_anomalies["three_missing_Ec"] = local_331_anomalies(generalized_331_fields(
        ordinary, F(1, 5), include_exotic_lepton_completion=False)).to_dict()
    output = {
        "schema": "ueot_qm.kernel_demo.v1.2",
        "representations": representations,
        "adaptive": {
            "policy": "Z; after 0 run H then Z; after 1 run Z",
            "initial_state": "I/2",
            "record_law": [{"record": record, "probability": probability}
                           for record, probability in dense.items()],
            "total_probability": sum(dense.values()),
            "dense_equals_coordinates": dense == coordinates,
        },
        "spectrum_cases": spectra,
        "six_local_331_anomalies_at_beta_over_sqrt3_one_fifth": six_anomalies,
        "scope": [
            "Representation witnesses cover all finite words of their fixed operation library",
            "Word witness length is an evidence resource bound, not a protocol horizon",
            "All spectrum windows and representation rules are declared sector inputs",
            "The six local anomaly sums do not establish a complete physical theory",
            "Python execution and JSON parsing are not asserted to be verified by Lean",
        ],
    }
    print(json.dumps(output, indent=2, ensure_ascii=False,
                     default=lambda x: str(x) if isinstance(x, F) else x))


if __name__ == "__main__":
    main()
