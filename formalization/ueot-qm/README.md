# UEOT-QM Lean package — v31.11

Finite complex quantum physics and typed read-only Core interfaces, pinned to Lean **4.33.1** and Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**.

Current new-source acceptance: **OperationalEquivalence**, 28 explicit theorems, 43 explicitly named declarations and 80 exported namespace constants audited. The actual targeted build and exhaustive namespace axiom audit passed with only `propext`, `Classical.choice`, `Quot.sound`; ordinary linter warnings remain. [Current scoped receipt](../../physics/qm/kernel/evidence/v31.11/lean-verification.json), [recursive input identity](../../physics/qm/kernel/evidence/v31.11/source-manifest.json), and [nine-result bindings](../../physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/chapter67_formal_bindings.json) state exactly what was checked.

The public source inventory is 50 modules, 987 explicit theorems and 1365 named axiom requests. This is an inventory, not a claim that the entire historical local gate was rerun. The inherited v31.10 unified acceptance covers 49 modules, 959 theorems and 1285 requests at its own [proof receipt](../../physics/qm/kernel/evidence/v31.10/lean-verification.json). Its original finite-conditioning chain is retained. All 49 old QM module files and all consumed Core sources remain unchanged; the new public import and audit/configuration additions have separate current source identities.

The new bridge proves raw single-system/complete-ancillary statistics iff actual complex-linear map equality iff rectangular Choi equality. It derives rectangular Kraus event positivity, trace nonincrease and actual ancillary amplification. Labelled sequential composition and sum congruence are formalized. Full finite Test/parallel/quotient-tree packaging and abstract OPT reconstruction remain paper responsibilities. No finite-precision or infinite-dimensional theorem is inferred from these exact finite proofs.

## Build and verify

The current targeted gate is:

```bash
python3 scripts/verify_operational_equivalence.py --output-dir /tmp/qm-operational-equivalence-proof
```

It records actual target compilation and every exported constant in the new namespace. The inherited full public-package gate remains available with its original finite-conditioning increment labels:

```bash
python3 scripts/verify_finite_conditioning.py --output-dir /tmp/qm-finite-conditioning-proof
```

This helper checks pinned dependencies, builds the complete public package, executes the complete named axiom audit, and binds the exact recursive sources before/after. Existing independent certificate/witness gates remain available:

```bash
python3 scripts/verify_finite_witnesses.py --output-dir /tmp/qm-finite-witnesses
python3 ../../physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports
python3 ../../physics/qm/conditioning/verify_runtime.py --output-dir /tmp/qm-finite-conditioning-runtime
```

The new runtime requires NumPy/SciPy/SymPy. CI installs pinned tested versions and runs its actual regression gates. Historical local witness runs retain their own identities; command availability is not evidence that all old gates were rerun in this local acceptance.

## Package modules

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
| [Effects](UEOTQM/Effects.lean) | 30 | Actual PSD effects and Born bounds; complete and selected pullbacks; finite record effects |
| [Stability](UEOTQM/Stability.lean) | 30 | All-effect response pseudodistance, actual channel contraction and defect, Core transport composition and positive-event posterior bounds |
| [Mixture](UEOTQM/Mixture.lean) | 23 | Actual finite density/instrument mixtures; all-effect and all-state total-variation bounds; rational weight and separately proved component-error budgets |
| [Cesaro](UEOTQM/Cesaro.lean) | 23 | Actual fixed-channel averages, exact endpoint residuals, finite-dimensional density compactness, invariant subsequential limits and stationary-state existence |
| [Survival](UEOTQM/Survival.lean) | 32 | Complete measure-prepare realization of substochastic kernels; actual all-success records, conditional QSD laws and a typed Doob realization consuming frozen Core theorems |
| [ClassicalSector](UEOTQM/ClassicalSector.lean) | 24 | Complete finite probability simplices and effects, convex-extreme purity, actual marginals and absence of pure extensions for a two-point half-mixture over any finite classical auxiliary carrier |
| [CorePurificationBoundary](UEOTQM/CorePurificationBoundary.lean) | 32 | Actual Core stochastic/control/terminal-quotient model, full-simplex-to-PMF dynamics, genuine trajectory marginal, declared finite Core slice and same-source purification separation |
| [RealLocalTomography](UEOTQM/RealLocalTomography.lean) | 37 | Distinct actual real composite density states with identical probabilities for every real product effect; an actual real joint effect distinguishes them, and complex local effects provide a deletion control |
| [QuantumDoob](UEOTQM/QuantumDoob.lean) | 32 | Selected-success record QSD laws, invertible-filter normalization, left-eigenmetric-to-Kraus completeness, all-operator finite intertwining and actual finite conditioning for every initial density |
| [RecordProbability](UEOTQM/RecordProbability.lean) | 9 | All finite record events; attained TV and event characterization |
| [RectangularChannels](UEOTQM/RectangularChannels.lean) | 29 | Actual rectangular CPTP, arbitrary finite ancilla, partial traces and contraction |
| [QuantumPurification](UEOTQM/QuantumPurification.lean) | 25 | Full-state convex purity and actual arbitrary finite Gram purification |
| [OperationalSystems](UEOTQM/OperationalSystems.lean) | 25 | Complete classical/real/complex presentations, seven laws and independent candidate principles |
| [ClassicalQuantumMemory](UEOTQM/ClassicalQuantumMemory.lean) | 39 | Actual joint record-memory channels for arbitrary finite adaptive trees |
| [QuantumDoobModel](UEOTQM/QuantumDoobModel.lean) | 17 | Precisely extracted prior noncommuting model and common states |
| [QuantumDoobDynamics](UEOTQM/QuantumDoobDynamics.lean) | 43 | Same model exact iterates, unique Doob stationarity and true source conditioning |
| [QuantumSeparation](UEOTQM/QuantumSeparation.lean) | 9 | 合法效应实张成、完整密度分离及距离零的矩阵含义 |
| [ComplexLocalTomography](UEOTQM/ComplexLocalTomography.lean) | 11 | 所有产品效应识别任意有限复联合态，并接回原 complexModel |
| [PureStateCharacterization](UEOTQM/PureStateCharacterization.lean) | 5 | 从完整凸极点和正 Gram 列导出归一向量，构成完整纯性 iff |
| [PurificationUniqueness](UEOTQM/PurificationUniqueness.lean) | 22 | 真实同载体辅助酉、矩形等距通道和异辅助载体共同直和 |
| [HistoryChannels](UEOTQM/HistoryChannels.lean) | 23 | 真实读取/去相干历史通道、PSD 块权重、合法块效应和同输入加权缺陷 |
| [ActionRecordBudget](UEOTQM/ActionRecordBudget.lean) | 31 | 共同有限因果控制器、原协议全态回接、逐动作和及完整记录 TV |
| [QuantumTraceDistance](UEOTQM/QuantumTraceDistance.lean) | 25 | Actual matrix absolute value, PSD spectral parts, attained all-effect distance and noncircular support certificates |
| [BinaryDiscrimination](UEOTQM/BinaryDiscrimination.lean) | 9 | Actual optimal equal-prior binary discrimination and exact finite certificates |
| [PurificationIsometry](UEOTQM/PurificationIsometry.lean) | 9 | Exact auxiliary cardinal direction and direct isometry between arbitrary same-marginal full pure states |
| [PurificationDimension](UEOTQM/PurificationDimension.lean) | 14 | Actual matrix-rank lower bound, spectral-support compression and exact attained minimal auxiliary dimension |
| [StoppingProtocols](UEOTQM/StoppingProtocols.lean) | 21 | Actual absorbing completion of finite stopping trees, exact decoder and zero invalid history blocks |
| [StoppingRecordBudget](UEOTQM/StoppingRecordBudget.lean) | 29 | Legal effect extension, original leaf-memory isometry and true remaining-probability action budgets |
| **Historical v31.9 subtotal** | **854** |41 modules; witnesses and generated instances are separate |
| [QuantumFiniteWindow](UEOTQM/QuantumFiniteWindow.lean) | 39 | Original finite instruments, singular support completion and complete conditional CQ output |
| [QuantumFiniteWindowSpectral](UEOTQM/QuantumFiniteWindowSpectral.lean) | 10 | PSD spectral factory, backward Gram kernel elimination and source-only endpoint |
| [QuantumActionRealizability](UEOTQM/QuantumActionRealizability.lean) | 12 | Flagged Choi maps and the actual Core convex-hull/PMF bridge |
| [QuantumReachableActionRealizability](UEOTQM/QuantumReachableActionRealizability.lean) | 3 | Prescribed reachable input and common-observation realization criteria |
| [QuantumActionCounterexamples](UEOTQM/QuantumActionCounterexamples.lean) | 11 | Visible-label, shared-observation and separator controls |
| [QuantumActionPauliWitness](UEOTQM/QuantumActionPauliWitness.lean) | 8 | Exact finite allowed-action randomization witness |
| [QuantumInitializationCost](UEOTQM/QuantumInitializationCost.lean) | 16 | Physical scaled filters, original source weights and retry cost recurrence |
| [QuantumPostselectionError](UEOTQM/QuantumPostselectionError.lean) | 6 | Sharp complete-output to postselected trace-distance bounds |

| [OperationalEquivalence](UEOTQM/OperationalEquivalence.lean) |28 | Positive physical systems, unnormalized all-effect separation, actual-map and rectangular Choi equality, complete finite ancillary statistics, rectangular TNI events, labelled congruence |

The companion [《UEOT物理学》3.8](../../physics/qm/book/UEOT_PHYSICS.md) has 68 chapters, six appendices and 182 numbered results in complete Chinese and English texts. All 173 previous numbered-result objects and 96 previous claim objects are preserved exactly. Paper arguments, microscopic infinite-dimensional domains, robust model certificates and empirical responsibilities extend beyond this formal package. Hardware confirmation and independent complex-sector selection remain open.
