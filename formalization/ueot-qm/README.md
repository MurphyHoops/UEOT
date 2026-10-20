# UEOT-QM Lean package — v31.5 / Kernel 1.5

This package implements a finite complex quantum sector and typed UEOT Core bridges. It inherits the exact Lean **4.33.1** and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` from `../ueot-core`.

The continuous companion monograph is [《UEOT物理学》正式 3.1](../../physics/qm/book/UEOT_PHYSICS.md), chapters 0–53 and appendices A–F, with its [PDF edition](../../physics/qm/book/UEOT_PHYSICS.pdf) in the same directory. Chapters 49–50 explain the executable certificate chain and actual quantum stability contract; chapters 51–53 add finite-mixture budgets, Cesàro stationary-state existence, and the diagonal quantum survival/Core bridge. The monograph's mathematical exposition and physical hypotheses have a separate scope from the declarations checked by this package.

**Current status: LOCAL_VERIFIED_CI_PENDING.** The actual unified local `lake build UEOTQM` passed with exit code 0: **334 explicit theorem declarations across 18 generic modules**, followed by **392 unique actual named axiom reports PASS**. The runtime suite has **100 passing test methods**, and all **four demos** passed. The retained mathematical witnesses passed 39 separate named audits; six generated numerical instances passed 42 further audits. Four corrupted true-check proofs were rejected, and four companion proofs established `check data = false` for the identical corrupted data, with four additional audit reports. These witness and instance targets are separate from the generic totals. Remote PR and resulting-main acceptance for this increment remain pending; [CURRENT.json](../../physics/qm/status/CURRENT.json) is the authority for subsequent integration status.

The current evidence includes the [build execution](../../physics/qm/kernel/evidence/v31.5/build-execution.json), [actual axiom reports](../../physics/qm/kernel/evidence/v31.5/proof-axioms.json), [axiom execution](../../physics/qm/kernel/evidence/v31.5/axiom-execution.json), [source manifest](../../physics/qm/kernel/evidence/v31.5/source-manifest.json), [instance verification](../../physics/qm/kernel/evidence/v31.5/lean-exports/verification.json), [runtime receipt](../../physics/qm/kernel/evidence/v31.5/runtime-verification.json), and [demo receipt](../../physics/qm/kernel/evidence/v31.5/demos-verification.json). The source manifest supplies the authoritative file set, count and tested byte identities. The v31.5 authoring baseline is `97d033ff83125822e9926f5bd36afd08dbd153ef`; a baseline commit alone does not identify later uncommitted proof or verification inputs.

**Verified history.** v31.4 had 15 generic modules, 256 explicit theorems and 287 named audit targets, recorded in its [proof receipt](../../physics/qm/kernel/evidence/v31.4/lean-verification.json), [55-entry source manifest](../../physics/qm/kernel/evidence/v31.4/source-manifest.json), and [claim ledger](../../physics/qm/status/CLAIM_LEDGER_v31.4.json). Its authoring baseline was `0c093e9fae990d6ef8d670163b84ec93bd6fb025`. The published v31.4 source is `3b227e3d08e6faa8252e3dd2e3ea4e5536dae007`, its tree is `2fb88d6bace94ec9ec682dc3ea120718c692f80a`, and the verified resulting-main commit is `d6926c7a8b650280a2357b6eb0cb8d86fca3953a` with the same tree. Its [integration receipt](../../physics/qm/kernel/evidence/v31.4/integration-verification.json) records successful PR #337 workflow 39345492165 and resulting-main workflow 39345953198. The preceding v31.3 completed PR #335 and resulting-main workflow 39300120071, as recorded in its separate [integration receipt](../../physics/qm/kernel/evidence/v31.3/integration-verification.json). These historical acceptance records do not assert remote acceptance of v31.5.

Frozen Core definitions, sources, the four counted generators, and the 106-item coverage ledger are not changed by this increment.

## Build and verify

From this directory, with the pinned toolchain available:

```bash
python3 scripts/check_dependencies.py
lake exe cache get
lake build UEOTQM
lake env lean scripts/AxiomAudit.lean > axiom-audit.log
python3 scripts/check_axioms.py
python3 scripts/verify_finite_witnesses.py --output-dir /tmp/qm-finite-witnesses
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
| [Effects](UEOTQM/Effects.lean) | 30 | Actual PSD effects and Born bounds; complete and selected pullbacks; finite record effects |
| [Stability](UEOTQM/Stability.lean) | 30 | All-effect response pseudodistance, actual channel contraction and defect, Core transport composition and positive-event posterior bounds |
| [Mixture](UEOTQM/Mixture.lean) | 23 | Actual finite density/instrument mixtures; all-effect and all-state total-variation bounds; rational weight and separately proved component-error budgets |
| [Cesaro](UEOTQM/Cesaro.lean) | 23 | Actual fixed-channel averages, exact endpoint residuals, finite-dimensional density compactness, invariant subsequential limits and stationary-state existence |
| [Survival](UEOTQM/Survival.lean) | 32 | Complete measure-prepare realization of substochastic kernels; actual all-success records, conditional QSD laws and a typed Doob realization consuming frozen Core theorems |
| **Total** | **334** | 18 generic modules; dedicated witnesses and generated instances are reported separately |

The **392** generic named audit targets are all **334** explicit theorems plus **58** listed constructions and definitions. v31.5 adds **78 theorems + 27 definitions = 105 audited names**: Mixture adds 23 + 7, Cesaro adds 23 + 7, and Survival adds 32 + 13. The preceding v31.4 total was **256 + 31 = 287**; its own increment comprised 60 theorems and 14 definitions, documented in the [effect/stability review](../../physics/qm/audits/EFFECT_STABILITY_REVIEW_v31.4.md) and [focused receipt](../../physics/qm/kernel/evidence/v31.4/metric-focused-audit.json). Audited definitions include both proof-bearing constructions and data definitions; they are not additional theorem declarations. These counts exclude compiler-generated constants, the 39 dedicated witness targets, the 42 generated positive-instance targets, and the four generated false-check targets. All audits retain the same reviewed standard foundation; this is not a claim of an axiom-free foundation.

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

The runtime's `export_lean_representation` emits concrete numerical source, not an oracle proof. Six [committed fixtures](../../physics/qm/kernel/certificates/v31.3/exports.json) cover Z, HZ, HSZ, ragged instruments, a complex 1-dimensional example, and a 4-dimensional projector. Each instance independently checks the data and prints seven axiom reports for `checked`, its proof-bearing `presentation`, and five public consequences: all-word iff, finite-tree coordinates, equal leaf laws, normalization, and closed coordinate update. These fixtures were regenerated and actually rechecked against the v31.5 package; their 42 instance audit targets are separate from the 392 generic targets and the dedicated witnesses below.

The verifier regenerates and byte-compares all six sources, their complete manifests and the index. It then compiles the actual source bytes and checks the exact expected audit target set. Four post-generation corruptions must fail at the original true-check theorem; a companion containing the identical numeric definitions must also prove `check data = false`. Both compilation outcomes, source hashes, shared data-prefix hashes and actual axioms are recorded. Environment errors or failed reduction alone do not count as rejection evidence.

The generator's manifest deliberately retains `LEAN_SOURCE_EXPORTED_NOT_COMPILED`; a later source-bound verification receipt records actual success. No claim is made that Python, JSON parsing, basis search, elimination, Gram independence, or the source exporter is universally verified. The theorem's object is the supplied numeric padded model. User labels remain external metadata; generated Fin indices use explicit bound proofs instead of modular numeral coercion.

## Retained mathematical witnesses

Two source files preserve the new modules' exact examples and premise controls as a separate verification gate:

| Witness source | Explicit theorems | Definitions | Named audits |
|---|---:|---:|---:|
| [MixtureExamples](scripts/witnesses/MixtureExamples.lean) | 5 | 4 | 9 |
| [SurvivalTwoState](scripts/witnesses/SurvivalTwoState.lean) | 24 | 6 | 30 |
| **Total** | **29** | **10** | **39** |

The mixture witnesses prove the exact one-half rational budget, sharpness on orthogonal density states, and failure of a weight-only bound when the component library changes. The two-state survival witnesses instantiate the actual quantum/Core bridge for every finite record length, distinguish the QSD from the Doob invariant law, and show why the initial law, row orientation and failure completion matter. These are proof-checked mathematical examples, separate from the runtime's finite six-step checks and from the six generated representation certificates.

After the ordinary package build, `python3 scripts/verify_finite_witnesses.py --output-dir /tmp/qm-finite-witnesses` recompiles both retained sources and requires every explicit theorem/definition to have exactly one matching allowed-axiom report. The gate records the actual pinned compiler invocation, witness bytes, verifier and configuration, and all repository-local general source/import artifacts before and after execution. It rejects missing or duplicate audit reports, unreviewed axioms, failed invocations and changed inputs. `--lake` can select an explicit Lake executable and `--timeout-seconds` sets the per-invocation limit. Source and artifact hashes bind the execution; the ordinary build remains the prerequisite establishing the imported artifacts.

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

## Actual effects and stability contract

`Effect ι` contains an actual matrix `E`, a proof that `E` is PSD, and a proof that `1 - E` is PSD. `Effect.probability` is the existing real trace pairing with an actual density matrix. Positivity follows through a PSD factorization and trace cyclicity, without assuming the noncommuting product `E * ρ` itself is PSD. Complement positivity then proves every Born probability lies in `[0, 1]`.

`Instrument.pullbackEffects` proves that a complete Kraus instrument pulls a family of outcome-dependent effects back to an effect. `channelState` sums all outcomes and constructs the actual trace-one output density. `branchEffect` instead places an effect at one outcome and zero at the others; it does not treat a selected branch as trace preserving. `recordTest_matrix` identifies the resulting recursive effect with the existing finite-word effect, so every finite record is also an allowed effect test.

`effectDistance` takes the real supremum of **all** effect probability differences:

\[
d_{\mathrm{eff}}(\rho,\sigma)
=\sup_{0\preceq E\preceq I}|P_E(\rho)-P_E(\sigma)|.
\]

The supremum is proved nonempty and bounded. The module derives nonnegativity, the upper bound 1, symmetry, the triangle inequality and control of every common finite-word response. `effectDistance_eq_zero_iff` states equality of all effect probabilities; density-matrix separation, a `MetricSpace` instance and identification with trace or diamond norms are not proved here.

For complete channels on the same finite carrier, `channelState_effectDistance_le` derives contraction from the actual Heisenberg pullback. The defect is also defined from actual outputs:

\[
\delta(F,G)=\sup\bigl(\{0\}\cup
\{d_{\mathrm{eff}}(F(\tau),G(\tau)):\tau\text{ is a Density}\}\bigr).
\]

Inserting zero handles an empty density type. The proved perturbation inequality is

\[
d_{\mathrm{eff}}(\Phi(\rho),\Psi(\sigma))
\le d_{\mathrm{eff}}(\rho,\sigma)+\delta(\Phi,\Psi).
\]

`channelTrajectory_transport_certificate` supplies this derived quantum recurrence to the existing Core transport bridge. `channelTrajectory_effectDistance_le_sum` gives initial error plus the sum of actual step defects, and `channelTrajectory_response_sub_le_sum` bounds every word in a **common subsequent instrument library**. The two channel sequences may have different outcome and Kraus types from each other; within each sequence those types are fixed while the matrices may vary with time.

For the same instrument and selected outcome, `posterior_effectDistance_le` requires **both branch probabilities to be strictly positive** and proves

\[
d_{\mathrm{eff}}(\rho_{\mid o},\sigma_{\mid o})
\le 2d_{\mathrm{eff}}(\rho,\sigma)/p_\rho(o).
\]

The lower-bound version additionally requires `0 < η` and `η ≤ pρ(o)` and replaces the denominator by `η`. `probability_pos_of_effectDistance_lt` proves the second branch remains positive when the input error is strictly smaller than the first event probability. Conditioning may amplify error; zero-probability posteriors remain undefined.

This closes the **finite common-carrier complete-channel / positive-event slice of QMU-04**. `channelDefect` itself is a noncomputable supremum. The v31.5 mixture results below supply certified upper bounds for a declared finite-mixture model; they do not compute arbitrary channel defects exactly. Outcome-forgetting channel defects do not automatically control different instruments' labeled or adaptive histories, and finite identity-ancilla positivity does not supply a stabilized norm comparison. Those extensions need explicit models and further proofs. See the [v31.4 report](../../physics/qm/UEOT_QM_KERNEL_v31.4.md) and [mathematical review](../../physics/qm/audits/EFFECT_STABILITY_REVIEW_v31.4.md) for the inherited stability layer.

## Actual mixtures and certified budgets

`Mixture.Weights β` contains only nonnegative normalized real weights. `density` constructs the actual matrix sum, and `weightedInstrument` / `instrument` add a component Kraus index with actual matrices `sqrt(p b) • K b o k`. Density positivity, trace one and instrument completeness are proved from the component objects and the weights. Branch, Heisenberg pullback and complete-channel identities are derived by expanding these actual matrices. Zero-weight terms remain valid.

For a common finite component library, the module proves

\[
\operatorname{TV}(p,q)=\tfrac12\sum_b|p_b-q_b|,\qquad
\delta\!\left(\sum_b p_b\Phi_b,\sum_b q_b\Phi_b\right)
\le\operatorname{TV}(p,q).
\]

The factor one half follows by centering each effect probability at one half and using equality of total weights. The bound holds for every density input and every effect, not just a tested sample. When the component channels also change, `channelDefect_joint_change_le` proves

\[
\delta\!\left(\sum_b p_b\Phi_b,\sum_b q_b\Psi_b\right)
\le\operatorname{TV}(p,q)+\sum_b q_b\delta(\Phi_b,\Psi_b).
\]

The two libraries share the finite matrix carrier and component correspondence; their outcome/Kraus types may differ from each other. `RationalWeights.toWeights` and `tv_toWeights` transport exact finite rational expressions into these real bounds. The rational joint-budget theorem still requires a separately established upper bound for **each actual component defect**. It does not infer those bounds from finite input-state samples or from a caller's unchecked numeric guess.

The same-library TV budget is computable and can be sharp, but can also overestimate the defect: equal component channels give zero defect even when the weights differ. The Python `MixtureWeightBudget` binds the weights to the actual shared component library; its correctness on all inputs is a separate program-refinement obligation. After each step's types and model correspondence are matched, these proved budgets can be supplied to the existing `channelTrajectory` / Core transport composition. This is the finite-mixture slice of usable defect certification, not an arbitrary-channel exact-distance algorithm.

## Actual Cesàro averages and stationary-state existence

For one fixed complete instrument, `Cesaro.iterateState` uses the actual `channelState` trajectory. `averageState I ρ N hN` constructs the PSD trace-one average for `0 < N`, including the initial state:

\[
\rho_n=\Phi^n(\rho_0),\qquad
\bar\rho_N=\frac1N\sum_{n=0}^{N-1}\rho_n.
\]

`orbitSum_telescope` and `matrix_residual` prove the matrix identity

\[
\Phi(\bar\rho_N)-\bar\rho_N=\frac{\rho_N-\rho_0}{N}.
\]

Every effect probability residual is at most `1/N`, and `effectDistance_residual_le` gives the same all-effect bound. This controls one further channel application to the average; it is not a distance estimate to a selected stationary state.

The module then proves that the actual PSD trace-one matrix set is closed and bounded, hence compact in the usual finite-dimensional complex matrix topology. `Matrix.Norms.L2Operator` supplies the Euclidean operator norm while preserving that topology. The density norm bound one gives a matrix residual bound `2/N`. These are proved properties of actual matrices, not compactness or invariance supplied as certificate fields.

`averageSequence` uses averages of length `n + 1`. `subsequence_limit_invariant` and `subsequence_limit_density` show that any convergent strictly increasing subsequence has a stationary density limit. `exists_stationary_subsequence` obtains such a subsequence from compactness. Given any initial density, `exists_stationary_of_density` supplies a stationary density; `exists_stationary` requires a nonempty finite carrier and constructs `normalizedIdentity` as its initial seed.

This proof uses QM matrix algebra and Mathlib finite-dimensional analysis. It does **not** directly invoke frozen Core P-PER or M-OI; their persistence language supplies motivation, whereas direct Core transport reuse is the separate stability chain above. The module proves subsequential limits and stationary-state existence. It does not prove uniqueness, convergence of the original iterates, a full Cesàro spectral-projection theorem, mixing rates, infinite-dimensional compactness, or empirical convergence of stochastic trajectories. Periodic-channel and nonunique-fixed-state examples preserve these distinctions.

## Diagonal survival and the frozen Core spectral bridge

`Survival.instrument` converts a nonnegative row-substochastic matrix `Q` into an actual complete instrument. The success terms have matrix `|j⟩⟨i|` and weight `Q i j`; failure terms supply each row's missing mass. `instrument_branch`, `measurePrepare_diagonal` and `killedIterate_diagonal` prove

\[
\mathcal K_Q(\operatorname{diag}p)=\operatorname{diag}(pQ),\qquad
\mathcal K_Q^n(\operatorname{diag}p)=\operatorname{diag}(pQ^n).
\]

`killedIterate` is the existing `recordOperator` for the actual length-`n` all-success word. `survivalMass_eq_response` identifies its trace with the same library's record response. The lifetime task stops at the first failure; the completion does not add an absorbing cemetery register to the Hilbert space. The measure-prepare success map removes input off-diagonal coherence, so this realizes a classical killed kernel inside quantum operations rather than covering every noncommutative survival map.

For a supplied normalized nonnegative `q`, `r > 0`, and left relation `qQ = r q`, the `qsd_*` theorems consume frozen Core results and derive the actual surviving operator `r^n • diag q`, record probability `r^n`, positive-event conditional state `diag q`, and `r ≤ 1`. The left spectral data are premises. Their existence, uniqueness and the identification of `r` with the full spectral radius are not derived here. Zero-mass conditioning is undefined.

`doobInstrument` requires nonnegative `Q`, `r > 0`, strictly positive `h`, and the right relation `Qh = r h`; these prove row stochasticity of

\[
\widetilde Q_{ij}=\frac{Q_{ij}h_j}{r h_i}.
\]

The constructor itself does not require the original row-substochastic bound; interpreting `Q` as the original killed process additionally uses that bound. Given the left relation, nonnegative `q` and `sum(q_i h_i) = 1`, `doobDensity` constructs the invariant law `π_i = q_i h_i`. The actual success branch, every finite all-success record, its probability one, and the corresponding conditional state are proved to preserve `diag π`. The QSD `q` and the Doob invariant law `π` are generally different. No infinite-horizon conditioning limit or general noncommutative Perron theorem is asserted; the monograph's geometric lifetime expectation remains an analytic consequence beyond the named finite-record theorems.

## Direct Core reuse

| Existing Core theorem | Actual QM consumer |
|---|---|
| `UEOT.V3.Compression.QuotientDescent.existsUnique_descend` | `UEOTQM.existsUnique_responseDecoder` |
| `UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate` | `UEOTQM.existsUnique_reachableResponseUpdate`, `UEOTQM.existsUnique_closedReachableUpdate` |
| `UEOT.V3.Compression.TransportCertificate.weighted_chain_bound` | `UEOTQM.Transport.scalar_transport_certificate`, then the actual quantum `UEOTQM.channelTrajectory_transport_certificate` |
| `UEOT.V3.QSDPerron.leftPerron_pow` | `UEOTQM.Survival.qsd_killedIterate` |
| `UEOT.V3.QSDPerron.qsd_survival_mass_pow` | `UEOTQM.Survival.qsd_survival_pow` |
| `UEOT.V3.QSDPerron.qsd_all_steps` | `UEOTQM.Survival.qsd_conditionalState` |
| `UEOT.V3.QSDPerron.perron_root_le_one_of_substochastic` | `UEOTQM.Survival.qsd_rate_le_one` |
| `UEOT.V3.QSDPerron.doobTransform_row_sum` | `UEOTQM.Survival.doobInstrument`, `UEOTQM.Survival.doob_success_probability` |
| `UEOT.V3.QSDPerron.doobInvariant_sum` | `UEOTQM.Survival.doobDensity`, `UEOTQM.Survival.doob_survivalMass` |
| `UEOT.V3.QSDPerron.doobInvariant_stationary` | `UEOTQM.Survival.doob_success_branch`, then its finite-record and conditional-state consequences |

Quantum compatibility is proved from actual Kraus/posterior definitions and prefix-closed word responses. It is not supplied as a field assuming the desired update theorem. The closed update carries the posterior as a witness of membership in the same response range.

## Scope

The finite complex density/Kraus sector is explicit input. No reconstruction of Hilbert space, Born probabilities, a value of Planck's constant, or a complete real-world gauge theory is asserted. The arithmetic spectrum bridge does not establish representation theory, global anomalies, a vacuum, masses or phenomenological viability.

The [executable Python kernel](../../physics/qm/kernel/README.md) uses exact Gaussian rationals, nonnegative rational Kraus weights and a finite word-effect basis. Its new `export_representation_certificate` / `verify_representation_certificate` API checks portable exact witnesses without rerunning the closure producer. This is executable evidence, not a Lean proof token.

The exact Gaussian-rational interpretation, nonnegative weighted-Kraus realization, finite ragged-index embeddings, and generic exact certificate checker are now proved in Lean. Open program refinements remain: the JSON parser and exporter on all inputs, closure-search termination and Gaussian elimination, PSD decision procedures, label-to-index mapping as a program, and Python adaptive-tree traversal. The new finite-generator existence theorem does not establish the search program or a dedicated Lean proof of the Hermitian `d²` dimension formula. A smaller response representation also does not imply a smaller physical CPTP Hilbert realization.

The Python representation checker supports Hilbert dimensions 1–4, at most `d²` basis effects, and word witnesses of length at most `d²−1`. These bound the evidence format rather than the language of future finite records. That representation checker has no uniform integer-bit or operation-library cap; the separate Lean exporter imposes the explicit bounds listed below. Another valid short-word basis is accepted under its own context when an expected basis fingerprint is not pinned; arbitrary linear mixtures are outside this word-witness format.

## Runtime and evidence

The [runtime manual](../../physics/qm/kernel/README.md) documents the export API, exact examples and independent tests. Each verification receipt binds the tested source bytes rather than merely naming a release. The source manifest includes generic Lean modules, locks, scripts, runtime source, fixed proof fixtures and the workflow. Reusing local dependency caches does not replace the actual proof build or axiom audit.

The exporter additionally limits input literals to 4096 bits, padded scalar storage to 65536 entries and source size to 8 MiB. The separate representation checker retains its own contract. These bounds constrain evidence construction, not future finite-word length; no uniform compilation-time guarantee is asserted.

The next stability work extends certified defect bounds beyond the declared finite-mixture model and adds explicit contracts for labeled histories, adaptive instruments or auxiliary systems as needed. Density separation and norm identification remain separate mathematical obligations. Further dynamics work includes full Cesàro spectral-projection results, uniqueness and mixing-rate hypotheses, noncommutative CP survival/Perron existence, and infinite-horizon conditioning limits. The actual finite Cesàro subsequence/existence and diagonal survival slices described above are now proved. Physical G3 applicability, QDRR experiments, CV energy/definition-domain control, and model-specific QFT/RG remain separately tracked in the [whole-QM roadmap](../../physics/qm/ROADMAP.md).
