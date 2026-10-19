# UEOT-QM Lean package — v31.3 / Kernel 1.3

This package implements a finite complex quantum sector and typed UEOT Core bridges. It inherits the exact Lean **4.33.1** and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` from `../ueot-core`.

**Current status: LOCAL_VERIFIED_CI_PENDING.** The actual unified local `lake build UEOTQM` has passed: **196 explicit theorem declarations across 13 generic modules**, followed by **213 actual named axiom reports PASS**. Six generated numerical instances and four same-data false witnesses are separately compiled and audited; their reused consequences are not counted as additional generic theorems. The runtime suite has **87 passing test methods**.

See the [v31.3 proof receipt](../../physics/qm/kernel/evidence/v31.3/lean-verification.json), [instance verification](../../physics/qm/kernel/evidence/v31.3/lean-exports/verification.json), [claim ledger](../../physics/qm/status/CLAIM_LEDGER_v31.3.json), and [current integration status](../../physics/qm/status/CURRENT.json). The preceding v31.2 completed PR #333 and the successful resulting-main workflow 39294335590; its [integration receipt](../../physics/qm/kernel/evidence/v31.2/integration-verification.json) supplements the original local receipt.

Frozen Core definitions, sources, the four counted generators, and the 106-item coverage ledger are not changed by this increment.

## Build and verify

From this directory, with the pinned toolchain available:

```bash
python3 scripts/check_dependencies.py
lake exe cache get
lake build UEOTQM
lake env lean scripts/AxiomAudit.lean > axiom-audit.log
python3 scripts/check_axioms.py
python3 ../../physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports
python3 scripts/record_source.py --output /tmp/qm-source-manifest.json
```

The [QM workflow](../../.github/workflows/ueot-qm.yml) uses the same gates. Its official compiler installer verifies the archive SHA256, exact version, and compiler commit; it does not disable TLS or change the pinned toolchain. The source gate rejects proof escapes. Actual axiom reports may use only `propext`, `Classical.choice`, and `Quot.sound`.

## Generic modules

| Module | Explicit theorems | Mathematical interface |
|---|---:|---|
| [Basic](UEOTQM/Basic.lean) | 7 | Finite complex PSD density operators, real mass, zero-mass characterization, normalization |
| [Instrument](UEOTQM/Instrument.lean) | 14 | Complete Kraus maps, probabilities, posterior, arbitrary finite identity ancilla |
| [Operational](UEOTQM/Operational.lean) | 20 | All-word response, quotient decoder, positive continuation, closed reachable update |
| [Transport](UEOTQM/Transport.lean) | 4 | Actual Core weighted-chain theorem applied to a scalar recurrence |
| [Selector](UEOTQM/Selector.lean) | 11 | Conditional three-color/three-family selection without atomicity and premise controls |
| [Observables](UEOTQM/Observables.lean) | 25 | Actual trace duality, word effects, minimal real observable span and finite generation |
| [FiniteCoordinates](UEOTQM/FiniteCoordinates.lean) | 21 | Local presentation, all-word iff, matrix updates and closed coordinate posteriors |
| [Adaptive](UEOTQM/Adaptive.lean) | 11 | Complete finite adaptive trees, normalized leaf laws and coordinate composition |
| [Spectrum](UEOTQM/Spectrum.lean) | 15 | Actual row sums to conditional anomaly/weak-budget selection, explicit counterexamples |
| [Weighted](UEOTQM/Weighted.lean) | 16 | Nonnegative weights to ordinary square-root Kraus matrices; exact branch, pullback, probability and posterior identities |
| [Ragged](UEOTQM/Ragged.lean) | 19 | Finite embeddings and zero padding; outcome-dependent Kraus types and zero outcome probabilities |
| [Exact](UEOTQM/Exact.lean) | 24 | Computable Gaussian-rational matrices, injective actual complex interpretation and operation transport |
| [ExactCertificate](UEOTQM/ExactCertificate.lean) | 9 | Decidable local conditions to actual instruments, finite presentation and all-word/adaptive consequences |
| **Total** | **196** | Generic source declarations; positive and negative generated instances are reported separately |

The 213 named audit targets are all 196 explicit theorems plus 17 listed proof-bearing constructions. The previous nine constructions remain; eight new targets are `WeightedInstrument.toInstrument`, `RaggedInstrument.toWeighted`, `WeightedInstrument.padOutcomes`, `Exact.MatrixData.instDecidableEq`, and `ExactCertificate.conditionsDecidable`, `weightedInstrument`, `instrumentFamily`, `presentation`, all under `UEOTQM`. This is not a census of compiler-generated constants or a claim of an axiom-free foundation.

## Exact certificate interface

The computable `ExactCertificate.Data d a o k r` contains rational weight tables, Gaussian-rational Kraus and basis matrices, actual record words, an empty-word index, and rational local coefficients. Its checker verifies five conditions: nonnegativity; complete weighted Kraus sums for every action; an empty distinguished word; equality of each numeric basis matrix with its actual word effect; and every branch's full local pullback expansion.

```lean
theorem checked : UEOTQM.ExactCertificate.check data = true := by decide +kernel
noncomputable def instruments := UEOTQM.ExactCertificate.instrumentFamily data checked
noncomputable def presentation := UEOTQM.ExactCertificate.presentation data checked
```

The checker does not assume global sufficiency. `check_sound`, actual complex interpretation and square-root weighted realization construct a `FiniteObservablePresentation`. Existing theorems then provide equality of all finite-word responses iff finite coordinates agree, complete finite adaptive leaf laws, and the closed positive-probability update.

`Exact.MatrixData.mul` implements `(A+iB)(C+iD)=(AC-BD)+i(AD+BC)` and `adjoint` implements transpose with the imaginary sign reversed. The interpretation is injective and preserves all checked operations. The generic weighted and ragged bridges preserve actual operations under their explicitly stated finite embeddings. No rational approximation of square roots is used.

## Generated proof instances

The runtime's `export_lean_representation` emits concrete numerical source, not an oracle proof. Six [committed fixtures](../../physics/qm/kernel/certificates/v31.3/exports.json) cover Z, HZ, HSZ, ragged instruments, a complex 1-dimensional example, and a 4-dimensional projector. Each instance independently checks the data and prints seven axiom reports for `checked`, its proof-bearing `presentation`, and five public consequences: all-word iff, finite-tree coordinates, equal leaf laws, normalization, and closed coordinate update. Thus 42 instance audit targets are separate from the 213 generic targets.

The verifier regenerates and byte-compares all six sources, their complete manifests and the index. It then compiles the actual source bytes and checks the exact expected audit target set. Four post-generation corruptions must fail at the original true-check theorem; a companion containing the identical numeric definitions must also prove `check data = false`. Both compilation outcomes, source hashes, shared data-prefix hashes and actual axioms are recorded. Environment errors or failed reduction alone do not count as rejection evidence.

The generator's manifest deliberately retains `LEAN_SOURCE_EXPORTED_NOT_COMPILED`; a later source-bound verification receipt records actual success. No claim is made that Python, JSON parsing, basis search, elimination, Gram independence, or the source exporter is universally verified. The theorem's object is the supplied numeric padded model. User labels remain external metadata; generated Fin indices use explicit bound proofs instead of modular numeral coercion.

## Finite representation contract

`Observables` defines actual Heisenberg pullbacks and chronological word effects from the existing Kraus maps. Its trace-duality theorem identifies those effects with the Schrödinger record probabilities. `observableSpace` is the real span of all finite word effects; its minimal closed-space property and existence of finitely many actual word generators are theorem outputs.

`FiniteObservablePresentation` supplies only finite words, an empty-word index, real branch coefficients, and local identities:

\[
B_j=E_{w_j},\qquad B_u=I,\qquad
\Phi_e^*(B_j)=\sum_k A_{e,jk}B_k.
\]

From those local data, the module derives full-span equality and

\[
x(\rho)=x(\sigma)\iff R_\rho=R_\sigma.
\]

It then derives the branch law `A @ x`, every finite record law, and positive-probability normalization. `closedCoordinateUpdate` computes directly from coordinates and has type

```lean
Set.range C.coordinates → (A × O) → Option (Set.range C.coordinates)
```

A posterior density representative is used only to prove membership of the result in the same physical coordinate image. The returned coordinates are computed from the supplied coordinate value. Zero probability returns `none`.

The Lean presentation permits redundant generators: spanning and sufficiency do not require independence. The Python certificate checker additionally verifies independence by a real Frobenius Gram determinant. The mathematical presentation theorem does not prove that the checker or JSON decoder implements it correctly.

`Adaptive` supplies a deterministic finite tree with one continuation for every outcome. Theorems connect its normalized leaf probabilities both to actual word responses and to the finite coordinate record computation. Adaptive-tree results do not add arbitrary time dependence or unmodeled environmental memory to the operation library.

## Spectrum contract

`Spectrum.spectrum_selects_three` consumes finite family entries, a nonzero rational anomaly unit, explicit extra matter and additional signed cubic contributions. It derives the selector's integer equation from actual sums under the homogeneous-lepton and zero-extra-sum hypotheses. Positivity of the complete declared SU(2) one-loop coefficient, with nonnegative extra screening and active ordinary rows, derives the strict weak budget. The theorem then calls `Selector.selects_three_without_atomicity`.

The target family count, the final integer anomaly equation and the final weak budget are not input fields of this bridge. Representation coefficients, the allowed matter template, validity of the declared matching window, and the physical interpretation of the anomaly and one-loop rules remain sector obligations. The Python module additionally sums six local 331 anomalies; this is distinct from the Lean module's selected cubic channel and weak budget. See the [spectrum review](../../physics/qm/audits/SPECTRUM_BRIDGE_v31.2.md).

## Direct Core reuse

| Existing Core theorem | Actual QM consumer |
|---|---|
| `UEOT.V3.Compression.QuotientDescent.existsUnique_descend` | `UEOTQM.existsUnique_responseDecoder` |
| `UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate` | `UEOTQM.existsUnique_reachableResponseUpdate`, `UEOTQM.existsUnique_closedReachableUpdate` |
| `UEOT.V3.Compression.TransportCertificate.weighted_chain_bound` | `UEOTQM.Transport.scalar_transport_certificate` |

Quantum compatibility is proved from actual Kraus/posterior definitions and prefix-closed word responses. It is not supplied as a field assuming the desired update theorem. The closed update carries the posterior as a witness of membership in the same response range.

## Scope

The finite complex density/Kraus sector is explicit input. No reconstruction of Hilbert space, Born probabilities, a value of Planck's constant, or a complete real-world gauge theory is asserted. The arithmetic spectrum bridge does not establish representation theory, global anomalies, a vacuum, masses or phenomenological viability.

The [executable Python kernel](../../physics/qm/kernel/README.md) uses exact Gaussian rationals, nonnegative rational Kraus weights and a finite word-effect basis. Its new `export_representation_certificate` / `verify_representation_certificate` API checks portable exact witnesses without rerunning the closure producer. This is executable evidence, not a Lean proof token.

The exact Gaussian-rational interpretation, nonnegative weighted-Kraus realization, finite ragged-index embeddings, and generic exact certificate checker are now proved in Lean. Open program refinements remain: the JSON parser and exporter on all inputs, closure-search termination and Gaussian elimination, PSD decision procedures, label-to-index mapping as a program, and Python adaptive-tree traversal. The new finite-generator existence theorem does not establish the search program or a dedicated Lean proof of the Hermitian `d²` dimension formula. A smaller response representation also does not imply a smaller physical CPTP Hilbert realization.

The Python representation checker supports Hilbert dimensions 1–4, at most `d²` basis effects, and word witnesses of length at most `d²−1`. These bound the evidence format rather than the language of future finite records. That representation checker has no uniform integer-bit or operation-library cap; the separate Lean exporter imposes the explicit bounds listed below. Another valid short-word basis is accepted under its own context when an expected basis fingerprint is not pinned; arbitrary linear mixtures are outside this word-witness format.

## Runtime and evidence

The [runtime manual](../../physics/qm/kernel/README.md) documents the export API, exact examples and independent tests. Each verification receipt binds the tested source bytes rather than merely naming a release. The source manifest includes generic Lean modules, locks, scripts, runtime source, fixed proof fixtures and the workflow. Reusing local dependency caches does not replace the actual proof build or axiom audit.

The exporter additionally limits input literals to 4096 bits, padded scalar storage to 65536 entries and source size to 8 MiB. The separate representation checker retains its own contract. These bounds constrain evidence construction, not future finite-word length; no uniform compilation-time guarantee is asserted.

The next quantum bridges are a concrete local metric/conditioning contract, CPTP Cesàro limits, and diagonal CP survival. Physical G3 applicability, QDRR experiments, CV energy/definition-domain control, and model-specific QFT/RG remain separately tracked in the [whole-QM roadmap](../../physics/qm/ROADMAP.md).
