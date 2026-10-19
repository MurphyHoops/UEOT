"""Reproducible exact numerical inputs for the Lean certificate bridge.

Writing a Lean file only exports a candidate. ``verify_lean_exports.py`` runs
the independent Lean kernel checks and records their actual outcomes.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

from ueot_qm import (
    Instrument, InstrumentLibrary, KrausTerm, Matrix, PredictiveModel,
    QComplex, diagonal, export_lean_representation,
    export_representation_certificate, identity,
)


def example_libraries() -> dict[str, InstrumentLibrary]:
    """Six declared finite physical models, including genuinely complex data.

    H uses the exact matrix numerator and weight 1/2. Different actions have
    different outcome counts; the ragged example also varies the number of
    Kraus terms and retains an explicit impossible outcome.
    """
    p0, p1 = diagonal([1, 0]), diagonal([0, 1])
    z = Instrument({"0": [KrausTerm(p0)], "1": [KrausTerm(p1)]})
    h = Instrument({"ok": [KrausTerm(
        Matrix([[1, 1], [1, -1]]), Fraction(1, 2),
    )]})
    s = Instrument({"ok": [KrausTerm(diagonal([1, QComplex(0, 1)]))]})
    coarse = Instrument({"done": [KrausTerm(p0), KrausTerm(p1)]})
    zzero = Instrument({
        "0": [KrausTerm(p0)], "1": [KrausTerm(p1)], "impossible": [],
    })
    p4 = diagonal([1, 0, 0, 0])
    return {
        "z": InstrumentLibrary({"Z": z}),
        "hz": InstrumentLibrary({"H": h, "Z": z}),
        "hsz": InstrumentLibrary({"H": h, "S": s, "Z": z}),
        "ragged": InstrumentLibrary({"coarse": coarse, "H": h, "Z": zzero}),
        "d1": InstrumentLibrary({"phase": Instrument({
            "ok": [KrausTerm(Matrix([[QComplex(1, 1)]]), Fraction(1, 2))],
            "zero": [],
        })}),
        "d4": InstrumentLibrary({"project": Instrument({
            "hit": [KrausTerm(p4)], "miss": [KrausTerm(identity(4) - p4)],
        })}),
    }


def export_examples(output_dir: Path | None = None) -> dict:
    """Export deterministic source/manifest bytes; never assert Lean success."""
    if output_dir is not None:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
    examples = []
    for name, library in example_libraries().items():
        model = PredictiveModel(library)
        certificate = export_representation_certificate(model)
        exported = export_lean_representation(
            certificate, library,
            expected_context_fingerprint=model.context_fingerprint,
        )
        manifest = exported.to_dict()
        manifest_text = exported.canonical_manifest + "\n"
        entry = {
            "name": name,
            "source_path": name + ".lean",
            "manifest_path": name + ".manifest.json",
            "source_sha256": exported.source_sha256,
            "manifest_sha256": sha256(manifest_text.encode("utf-8")).hexdigest(),
            "module_name": exported.module_name,
            "certificate_fingerprint": manifest["certificate_fingerprint"],
            "library_fingerprint": library.fingerprint,
            "context_fingerprint": model.context_fingerprint,
            "dimensions": manifest["index_layout"]["dimensions"],
            "original_branch_count": len(certificate["pullbacks"]),
            "original_pullback_identity_count": len(certificate["pullbacks"]) * model.dimension,
            "status": "LEAN_SOURCE_EXPORTED_NOT_COMPILED",
        }
        examples.append(entry)
        if output_dir is not None:
            (output_dir / entry["source_path"]).write_text(exported.lean_source, encoding="utf-8")
            (output_dir / entry["manifest_path"]).write_text(manifest_text, encoding="utf-8")
    index = {
        "schema": "ueot_qm.lean_examples.v1",
        "version": "31.3-kernel.1.3",
        "status": "LEAN_SOURCE_EXPORTED_NOT_COMPILED",
        "examples": examples,
        "interpretation": {
            "scalars": "exact Gaussian-rational matrices and nonnegative rational weights",
            "certificate": "nonnegative weights, completeness, empty unit word, generated basis, local closure",
            "lean_check": "each checked theorem must independently pass decide +kernel",
            "consequence": "all finite words and complete finite deterministic adaptive trees of the checked model",
            "limits": [
                "No universal formal verification of Python, its JSON parser, or its exporter",
                "No Lean refinement of the Gram test, basis search or elimination",
                "No uniform execution-time bound, experimental identification or unconditional G3 result",
            ],
        },
    }
    if output_dir is not None:
        (output_dir / "exports.json").write_text(
            json.dumps(index, indent=2, ensure_ascii=False) + "\n", encoding="utf-8",
        )
    return index


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        help="write each complete Lean source and companion manifest here")
    args = parser.parse_args()
    print(json.dumps(export_examples(args.output_dir), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
