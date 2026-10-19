# UEOT-QM Lean package — v31.2 / Kernel 1.2

This package implements the finite quantum sector and its typed UEOT Core bridges. It inherits the exact toolchain and dependency revisions of `../ueot-core`.

**Current status: LOCAL_VERIFIED_CI_PENDING.** The official Lean **4.33.1** release has completed the actual local `lake build UEOTQM` with exit code **0**. All **128 explicit theorem declarations across nine modules compile**, and **137 actual named axiom reports PASS**, using only `propext`, `Classical.choice`, and `Quot.sound`. The companion runtime has also passed **72 test methods and both demos**.

These local results are bound to source commit [`323db6d1c2e5`](https://github.com/MurphyHoops/UEOT/commit/323db6d1c2e50a432bdcf6a6872212426cc826ce). See the [v31.2 local proof receipt](../../physics/qm/kernel/evidence/v31.2/lean-verification.json) and [claim ledger](../../physics/qm/status/CLAIM_LEDGER_v31.2.json). GitHub Actions remains queued; remote CI for [PR #333](https://github.com/MurphyHoops/UEOT/pull/333) and resulting-main integration have not yet been accepted. The latest version with completed main-branch acceptance remains **v31.1 / Kernel 1**.

The toolchain remains Lean **4.33.1**, with Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. Frozen Core definitions, sources, counted generators and the 106-item coverage ledger are not modified by this package increment.

Previously accepted Kernel 1 passed [workflow 39270031506](https://github.com/MurphyHoops/UEOT/actions/runs/39270031506) at commit `0791ea34f1ba108c738915921f8e7d923371d0cd`: 56 theorem declarations across five modules, the unified root import, and 59 actual axiom reports. Its exact runtime passed 32 test methods. Those receipts remain unchanged and certify their original source bytes.

## Build

With Elan/Lake installed, from this directory:

```bash
python3 scripts/check_dependencies.py
lake exe cache get
lake build UEOTQM
lake env lean scripts/AxiomAudit.lean > axiom-audit.log
python3 scripts/check_axioms.py
```

The dedicated [QM workflow](../../.github/workflows/ueot-qm.yml) checks out an explicit commit, checks the Core dependency lock, records source identity, compiles the unified root import, and audits actual axiom dependencies. The accepted standard foundation is `propext`, `Classical.choice`, and `Quot.sound`. The source gate rejects proof escapes. The named audit covers every explicit theorem and the nine listed proof-bearing constructions; it is not a census of compiler-generated constants or a claim of an axiom-free foundation.

## Modules

| Module | Explicit theorems | Mathematical interface |
|---|---:|---|
| [Basic](UEOTQM/Basic.lean) | 7 | Finite complex PSD density operators, nonnegative real trace, zero-mass characterization, positive-mass normalization |
| [Instrument](UEOTQM/Instrument.lean) | 14 | Kraus completeness, positive branches, probability law, posterior, arbitrary finite identity-ancilla amplification |
| [Operational](UEOTQM/Operational.lean) | 20 | Actual all-word record response, quotient decoder, positive-branch continuation, closed response-range update |
| [Transport](UEOTQM/Transport.lean) | 4 | Explicit scalar recurrence and true Core weighted-chain reuse |
| [Selector](UEOTQM/Selector.lean) | 11 | Conditional three-color/three-family selection without atomicity; premise and replication controls |
| [Observables](UEOTQM/Observables.lean) | 25 | Actual Kraus trace duality, generated word effects, smallest closed real observable space, finite-dimensionality and finite word-generator existence |
| [FiniteCoordinates](UEOTQM/FiniteCoordinates.lean) | 21 | Finite local presentation, equality with the full observable span, exact coordinate record laws, normalized and closed coordinate updates |
| [Adaptive](UEOTQM/Adaptive.lean) | 11 | Finite complete adaptive trees, unique leaf records, normalized leaf laws, response and coordinate compatibility |
| [Spectrum](UEOTQM/Spectrum.lean) | 15 | Actual finite spectrum sums, derived anomaly and weak-budget premises, composition with the existing selector, explicit counterexamples |
| **Total** | **128** | All explicit declarations passed the actual local unified build; remote CI and main integration remain pending |

The nine additional audited constructions are `normalize`, `Instrument.posterior`, `nextReachableResponse`, `pairingLinear`, `heisenbergLinear`, `FiniteObservablePresentation.closedCoordinateUpdate`, `Adaptive.Protocol.leafFintype`, `Spectrum.oneHiggs`, and `Spectrum.twentyHiggs`, all under `UEOTQM`. Together with the explicit theorem declarations they give 137 named audit targets; all 137 actual local reports passed the audit against the reviewed standard foundation.

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

Open implementation bridges include exact-data and JSON interpretation, weighted Kraus and differing outcome/Kraus index adapters, closure-search termination and Gaussian elimination, PSD decision procedures, and the Python adaptive-tree traversal. The new finite-generator existence theorem does not establish the search program or a dedicated Lean proof of the Hermitian `d²` dimension formula. A smaller response representation also does not imply a smaller physical CPTP Hilbert realization.

The checker supports Hilbert dimensions 1–4, at most `d²` basis effects, and word witnesses of length at most `d²−1`. These bound the evidence format rather than the language of future finite records. Integer bit lengths and the operation-library size have no uniform implementation cap. Another valid short-word basis is accepted under its own context when an expected basis fingerprint is not pinned; arbitrary linear mixtures are outside this word-witness format.

## Runtime and evidence

From the repository root:

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/verify_kernel.py --output /tmp/ueot-qm-runtime-v312.json
```

The 72 current tests comprise 32 existing kernel tests, 18 representation-certificate tests and 22 spectrum/anomaly tests. `demo_v312.py` emits the full finite representation certificates, independently recomputed verification receipts, an adaptive record-law comparison, spectrum row receipts and local 331 anomaly sums. Runnable API examples are in the [kernel README](../../physics/qm/kernel/README.md).

New evidence belongs in `physics/qm/kernel/evidence/v31.2/`. The [v31.2 local proof receipt](../../physics/qm/kernel/evidence/v31.2/lean-verification.json) records the successful local build, actual axiom audit and source identity. Its `LOCAL_VERIFIED_CI_PENDING` status keeps local verification distinct from remote CI and main-branch acceptance. The historical [Kernel 1 build receipt](../../physics/qm/kernel/evidence/lean-verification.json), [axiom reports](../../physics/qm/kernel/evidence/proof-axioms.json), and [runtime receipt](../../physics/qm/kernel/evidence/runtime-verification.json) retain their original source identity; they are not reused as new-source proof evidence.

See the [v31.2 theory and coverage report](../../physics/qm/UEOT_QM_KERNEL_v31.2.md), [v31.2 claim ledger](../../physics/qm/status/CLAIM_LEDGER_v31.2.json), and [source/representation review](../../physics/qm/audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md). The [v31.1 report](../../physics/qm/UEOT_QM_KERNEL_v31.1.md) remains the historical first-kernel reference.

