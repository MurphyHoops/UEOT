# UEOT-QM Lean package

This package implements the finite quantum sector and its typed UEOT Core bridges. It inherits the exact toolchain and dependency revisions of `../ueot-core`.

Kernel 1 passed [workflow 39270031506](https://github.com/MurphyHoops/UEOT/actions/runs/39270031506) at commit `0791ea34f1ba108c738915921f8e7d923371d0cd`: 56 theorem declarations across five modules, the unified root import, and 59 actual axiom reports. The accompanying exact runtime passed 32 test methods. The receipt below binds these statements to the tested source bytes.

## Build

With Elan/Lake installed, from this directory:

```bash
python3 scripts/check_dependencies.py
lake exe cache get
lake build UEOTQM
lake env lean scripts/AxiomAudit.lean > axiom-audit.log
python3 scripts/check_axioms.py
```

The dedicated [QM workflow](../../.github/workflows/ueot-qm.yml) checks out an explicit commit, records proof-source hashes, compiles the root import, and audits actual axiom dependencies. The accepted standard foundation is `propext`, `Classical.choice`, and `Quot.sound`. The source gate rejects new proof escapes. This is not a claim of an axiom-free foundation.

## Modules

| Module | Mathematical interface |
|---|---|
| `Basic` | Finite complex PSD density operators, nonnegative real trace, zero-mass characterization, positive-mass normalization |
| `Instrument` | Kraus completeness, positive branches, probability law, posterior, arbitrary finite identity-ancilla amplification |
| `Operational` | Actual all-word record response, quotient decoder, positive-branch continuation, closed `range → input → Option range` update |
| `Transport` | Explicit scalar recurrence and true Core weighted-chain reuse |
| `Selector` | Conditional three-color/three-family selection without atomicity; premise and replication controls |

## Direct Core reuse

| Existing Core theorem | Actual QM consumer |
|---|---|
| `UEOT.V3.Compression.QuotientDescent.existsUnique_descend` | `UEOTQM.existsUnique_responseDecoder` |
| `UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate` | `UEOTQM.existsUnique_reachableResponseUpdate`, `UEOTQM.existsUnique_closedReachableUpdate` |
| `UEOT.V3.Compression.TransportCertificate.weighted_chain_bound` | `UEOTQM.Transport.scalar_transport_certificate` |

Quantum compatibility is proved from actual Kraus/posterior definitions and prefix-closed word responses. It is not supplied as a field assuming the desired update theorem. The closed update carries the posterior as a witness of membership in the same response range.

## Scope

The finite complex density/Kraus sector is explicit input. No reconstruction of Hilbert space, Born probabilities, a value of Planck's constant, or a complete real-world gauge theory is asserted. The G3 theorem retains its anomaly, spectrum-count and weak-budget hypotheses.

The executable Python kernel in [physics/qm/kernel](../../physics/qm/kernel/README.md) uses exact Gaussian rationals, nonnegative rational Kraus weights and a finite observable basis. Its data embedding, weighted/ragged-index adapter, W* closure algorithm, PSD decision procedure and finite adaptive-tree interpreter are not formally refined to this Lean package in v1.

See the [theory and coverage report](../../physics/qm/UEOT_QM_KERNEL_v31.1.md), [claim ledger](../../physics/qm/status/CLAIM_LEDGER_v31.1.json), and [actual build/axiom receipt](../../physics/qm/kernel/evidence/lean-verification.json).

