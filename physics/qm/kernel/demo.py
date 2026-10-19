"""End-to-end exact QM kernel examples; run from any working directory."""

from dataclasses import asdict
from fractions import Fraction as F
import json

from ueot_qm import (Matrix, QComplex, diagonal, identity, KrausTerm,
                     Instrument, InstrumentLibrary, PredictiveModel, ProtocolNode)
from ueot_qm.certificates import (compare_finite_protocols, certify_postselection,
                                  TransportStep, verify_transport_trace)


def main():
    p0, p1 = diagonal([1, 0]), diagonal([0, 1])
    plus, minus = Matrix([[1, 1], [1, 1]]) / 2, Matrix([[1, -1], [-1, 1]]) / 2
    choices = {
        "Z": Instrument({"0": [KrausTerm(p0)], "1": [KrausTerm(p1)]}),
        "H": Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), F(1, 2))]}),
        "S": Instrument({"ok": [KrausTerm(diagonal([1, QComplex(0, 1)]))]}),
    }
    contexts = {}
    for names in (("Z",), ("H", "Z"), ("H", "S", "Z")):
        lib = InstrumentLibrary({name: choices[name] for name in names})
        model = PredictiveModel(lib)
        contexts["+".join(names)] = {
            "hilbert_dimension": lib.dimension,
            "response_dimension_including_trace": model.dimension,
            "dimension_history": model.dimension_history,
            "plus_minus_equivalent": model.equivalent(plus, minus),
            "context_fingerprint": model.context_fingerprint,
        }
    lib = InstrumentLibrary({name: choices[name] for name in ("H", "Z")})
    model = PredictiveModel(lib)
    word = ["H", "H", "Z"]
    direct, encoded = lib.word_law(p0, word), model.word_law(model.encode(p0), word)
    if direct != encoded:
        raise ArithmeticError("dense and response-coordinate computations disagree")
    z = ProtocolNode("Z", {"0": None, "1": None})
    narrow = compare_finite_protocols(lib, lib, {"plus-minus": (plus, minus)}, {"Z": z})
    wider = compare_finite_protocols(lib, lib, {"plus-minus": (plus, minus)},
                                     {"Z": z, "HZ": ProtocolNode("H", {"ok": z})})
    postselection = certify_postselection(
        {"common": F(99, 100), "a": F(1, 100), "b": 0},
        {"common": F(99, 100), "a": 0, "b": F(1, 100)}, {"a", "b"})
    transport = verify_transport_trace(
        [F(1, 10), F(1, 10), F(1, 5)], F(1, 5),
        [TransportStep(F(1, 2), F(1, 10), "checked finite scalar example, step 0"),
         TransportStep(2, F(1, 20), "checked finite scalar example, step 1")])
    output = {
        "schema": "ueot_qm.kernel_demo.v1",
        "arithmetic": "exact Gaussian rationals; probabilities printed as rational strings",
        "contexts": contexts,
        "interference": {
            "initial_state": "|0><0|", "actions": word,
            "record_law": [{"outcomes": key, "probability": value} for key, value in direct.items()],
            "dense_equals_coordinates": direct == encoded,
        },
        "finite_protocol_certificate": {
            "Z_only_maximum_tv": narrow.maximum_tv,
            "Z_and_HZ_maximum_tv": wider.maximum_tv,
            "scope": wider.scope,
            "scope_changed": narrow.scope_fingerprint != wider.scope_fingerprint,
        },
        "postselection": asdict(postselection),
        "scalar_transport": asdict(transport),
        "interpretation": "Executable QM operations and protocol quotients; physical sector inputs remain explicit.",
    }
    print(json.dumps(output, indent=2, ensure_ascii=False, default=lambda x: str(x) if isinstance(x, F) else x))


if __name__ == "__main__":
    main()
