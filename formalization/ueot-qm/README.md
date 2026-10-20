# UEOT-QM Lean package — v31.7

This package implements a finite complex quantum sector and typed UEOT Core bridges with pinned Lean **4.33.1** and Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**.

**Current status: MAIN_VERIFIED.** Actual unified compilation passed: 29 modules, 646 explicit theorems and 855 unique named axiom reports, exit 0, 8793 jobs. Seven persistent witness files passed 151 separate reports (110 theorems, 39 definitions, two abbreviations). Six exact certificates /42 audits, four paired corrupt-data controls, 100 runtime methods and four demos passed. The actual 80-input source manifest has SHA256 b453ce5028eb1ef7d324326245ae5c6cc1a0bf3f40cabf691f25bb1aae7a5911. [Proof receipt](../../physics/qm/kernel/evidence/v31.7/lean-verification.json), [source manifest](../../physics/qm/kernel/evidence/v31.7/source-manifest.json) and [CURRENT](../../physics/qm/status/CURRENT.json) separate local execution from remote acceptance.

The continuous companion [《UEOT物理学》3.3](../../physics/qm/book/UEOT_PHYSICS.md) contains chapters 0–59 and appendices A–F, 131 numbered results and an actual 203-page [PDF](../../physics/qm/book/UEOT_PHYSICS.pdf). Its full mathematical exposition and physical hypotheses exceed the limited declarations formally checked here.

Historical [v31.6](../../physics/qm/kernel/evidence/v31.6/integration-verification.json) had 22 modules, 459 explicit theorems and 573 audits, with PR #345 and resulting-main CI accepted. Earlier version evidence retains its own source identities. Frozen Core definitions, its four counted generators and the 106-item coverage ledger are not modified by this increment.

## v31.7 scope and remaining responsibilities

QuantumPurification constructs a Gram factor from PSD, proves normalized vector states are extreme in the complete density space, and proves an actual pure joint state has the original density as its actual partial trace. It does not assume a supplied purification or prove the converse pure-state characterization.

OperationalSystems models complete classical, complex and real state/effect sets, proves seven elementary laws, and keeps candidate purification and tomography properties independent. Purification existence holds for the complex presentation; classical purification and real local tomography fail. The seven laws are not a complete list of reconstruction axioms.

RectangularChannels gives actual different-input/output Kraus channels, arbitrary finite ancillary amplification and partial traces. ClassicalQuantumMemory connects each arbitrary finite protocol leaf to its original Kraus record operator and true probability, retaining the record and terminal state. Its current perturbation estimate uses an actual whole-channel defect; reducing it to stepwise action budgets remains open.

QuantumDoobDynamics proves exact all-complex-matrix iterates and unique Doob stationarity only for the published rational model. For every initial density it derives the true source success mass, the actual conditioned state, exact all-effect distance scaling to the source fixed state and geometric convergence bounds. Success mass tends to zero. The legal identity-Doob witness demonstrates that positive spectral data alone do not imply mixing. General spectral existence, essential purification uniqueness, complex local tomography, infinite conditioning and empirical applicability require separate work.

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
| **Total** | **646** | 29 package modules; concrete witnesses and generated instances are reported separately |

The **855** package audit targets comprise all **646** explicit theorems plus **209** other reviewed named targets. The v31.7 increment has 187 explicit theorems and 95 other targets, totaling 282 audits; all new explicit declarations, two named instances, two registered instance projections and six structure constructors are covered. The historical v31.6 increment was **125 theorems + 56 other targets = 181 audits**. Its module totals are ClassicalSector **37**, CorePurificationBoundary **51**, RealLocalTomography **50**, and QuantumDoob **43**. All explicit definitions, abbreviations, structures and named instances in these four new modules are included, together with `Classical.Effect.mk` and `QuantumDoob.InvertibleFilter.mk`. The three public Core quotient-type instances are intentionally retained and audited; they supply finite-carrier and discrete-measurable interfaces for imported use. No compiler-generated-constant census is claimed.

The historical v31.5 count was **334 + 58 = 392**, with an increment of **78 theorems + 27 definitions = 105 audited names**: Mixture added 23 + 7, Cesaro added 23 + 7, and Survival added 32 + 13. The preceding v31.4 total was **256 + 31 = 287**; its own increment comprised 60 theorems and 14 definitions, documented in the [effect/stability review](../../physics/qm/audits/EFFECT_STABILITY_REVIEW_v31.4.md) and [focused receipt](../../physics/qm/kernel/evidence/v31.4/metric-focused-audit.json). Audited constructions and type declarations are not additional theorem declarations. The current package totals exclude the **151** dedicated witness targets, the **42** generated positive-instance targets and the **four** generated false-check targets. All audits use the same allowed standard foundation; this is not a claim of an axiom-free foundation.

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

The runtime's `export_lean_representation` emits concrete numerical source, not an oracle proof. Six [committed fixtures](../../physics/qm/kernel/certificates/v31.3/exports.json) cover Z, HZ, HSZ, ragged instruments, a complex 1-dimensional example, and a 4-dimensional projector. Each instance independently checks the data and prints seven axiom reports for `checked`, its proof-bearing `presentation`, and five public consequences: all-word iff, finite-tree coordinates, equal leaf laws, normalization, and closed coordinate update. These fixtures were regenerated and actually rechecked against the historical v31.5/v31.6 packages and the final v31.7 package, each with its own source-bound verification receipt. Their 42 instance audit targets are separate from the current 855 package targets and the dedicated witnesses below.

The verifier regenerates and byte-compares all six sources, their complete manifests and the index. It then compiles the actual source bytes and checks the exact expected audit target set. Four post-generation corruptions must fail at the original true-check theorem; a companion containing the identical numeric definitions must also prove `check data = false`. Both compilation outcomes, source hashes, shared data-prefix hashes and actual axioms are recorded. Environment errors or failed reduction alone do not count as rejection evidence.

The generator's manifest deliberately retains `LEAN_SOURCE_EXPORTED_NOT_COMPILED`; a later source-bound verification receipt records actual success. No claim is made that Python, JSON parsing, basis search, elimination, Gram independence, or the source exporter is universally verified. The theorem's object is the supplied numeric padded model. User labels remain external metadata; generated Fin indices use explicit bound proofs instead of modular numeral coercion.

## Retained mathematical witnesses

Seven actual witness files pass a separate compiler-and-axiom gate.

| Source | Theorems | Definitions | Abbreviations | Named reports |
|---|---:|---:|---:|---:|
| MixtureExamples | 5 | 4 | 0 | 9 |
| SurvivalTwoState | 24 | 6 | 0 | 30 |
| RealTomographyTwoRebit | 5 | 0 | 0 | 5 |
| QuantumDoobExamples | 28 | 12 | 0 | 40 |
| QuantumPurificationExamples | 13 | 7 | 0 | 20 |
| ClassicalQuantumMemoryExamples | 15 | 5 | 2 | 22 |
| QuantumDoobDynamicsExamples | 20 | 5 | 0 | 25 |
| Total | 110 | 39 | 2 | 151 |

The new sources check a full-density Bell purification and restricted-state fake purity; deleted-record identity channels with record TV one and an actual two-step feedback event; and the same noncommuting true conditional model plus a legal identity-Doob non-mixing control. Source-level abbreviations are explicitly audited rather than silently omitted.

The verifier requires each explicit theorem, definition and abbreviation to have exactly one actual matching allowed-axiom report. It binds all witness source bytes, the verifier, configuration and 86 recursive QM/Core source-and-olean inputs before and after execution. Missing/duplicate reports, unsupported declarations, changed inputs, unreviewed axioms and failed invocations are rejected. The ordinary package build establishes the imported artifacts. See the [actual v31.7 witness receipt](../../physics/qm/kernel/evidence/v31.7/finite-witnesses/verification.json). Runtime method counts and six numerical certificate instances remain separate.


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

## Full classical states and an actual Core purification boundary

`ClassicalSector.State X` is the complete finite probability simplex `Mixture.Weights X`. Its effects are every function into `[0,1]`; indicator effects separate all states. `mix`, `pushforward` and `marginalLeft` are actual probability operations. `IsPure` quantifies every nontrivial convex decomposition into states of this complete simplex. It is not defined as Dirac form or as membership in a selected list.

For two distinct points, the half-mixture of their Dirac states is not pure. More strongly, `no_pure_extension_halfMix` quantifies an arbitrary finite auxiliary type `B` and excludes every pure state in the complete product simplex `State (X × B)` with that left marginal. The proof constructs conditional rows of any purported extension and exhibits a nontrivial convex decomposition. There is no fixed auxiliary-cardinality bound or nonempty-auxiliary premise. Separate positive controls construct ordinary extensions when an auxiliary point is supplied and pure extensions of Dirac states.

`CorePurificationBoundary` uses the existing `survivalMicroKernel` on `Bool × Bool`, an explicitly chosen complete registered observation, the actual `terminalSetoid`, and `organizationalTerminalControl`. The terminal quotient's failure to merge the two supported states is derived from the registered attributes and quotient equality. It is not assumed as an injectivity field.

The full-simplex map `toPMF` agrees with actual Core transition rows, and `toPMF_stepState` identifies stochastic state evolution with the actual PMF bind for every initial simplex state. `actualPathLaw` is the existing infinite stationary trajectory measure under the explicitly constructed safe policy. The key marginal theorem is a genuine measure pushforward:

\[
(\texttt{actualPathLaw}).\operatorname{map}
\bigl(\omega\mapsto\texttt{terminalControl.f}(\omega(1))\bigr)
=\operatorname{toMeasure}\bigl(\operatorname{toPMF}(\texttt{firstQuotientState})\bigr).
\]

`classical_purification_separation` combines that same-source marginal, the absence of every finite classical pure extension, and `FiniteCoreSlice`. The latter is an explicit conjunction of 14 properties: stochastic normalization, registered readout, stable quotient, actual control/reward/value relations, viability at every finite horizon, actual PMF rows and an almost-sure safe trajectory. It is the declared finite H1–H6 interface slice, not a certificate for every Core theorem. The policy is constructed and proved safe; zero reward does not uniquely select it by optimization.

The full classical state/effect/composite interpretation is an explicit model choice. Thus the result identifies a purification obstruction in this stated Core-compatible interpretation; it does not prove universal failure of quantum reconstruction from all UEOT extensions. A deletion control uses the existing restricted-readout Core model: the two supported points then merge, and the corresponding quotient marginal becomes Dirac and pure. This shows why the registered observation matters.

## Actual real-quantum local tomography boundary

`RealLocalTomography` works with the existing complex matrices while explicitly requiring real entries for the real sector. For `Y` equal to the Pauli-Y matrix, set

\[
P=Y\otimes Y,\qquad
\rho_\pm=\tfrac14(I\pm P).
\]

The matrices `rhoPlus` and `rhoMinus` are actual PSD, trace-one `Density` objects with real entries. Their positivity comes from proved Hermitian-involution projector identities. The product of any two actual effects is constructed as an actual joint effect. `all_real_product_probabilities_equal` quantifies **every** pair of local real effects, and proves equal Born probabilities on these two states.

The actual real joint effect `(I + P)/2` has probabilities one and zero, so the two densities are distinct and globally distinguishable. This is a counterexample to local tomography for the stated real tensor-composite model, not a finite sampling failure. The retained witness also proves that no finite real linear combination of real local product operators equals the distinguishing joint effect. When the local reality restriction is removed, the constructed complex local effects distinguish the states; that restriction is essential.

This module does not derive local tomography from Core or prove that it uniquely selects complex quantum theory. It also does not establish a real-quantum purification obstruction. Classical purification and real local tomography are distinct tests of distinct proposed reconstruction principles.

## Noncommutative finite quantum survival and Doob dynamics

`QuantumDoob` begins with one selected branch `Φ` of an actual complete instrument. `successOperator` uses the existing `recordOperator` on the literal repeated-success word, and `successMass_eq_response` identifies its mass with the same library's actual record probability. A supplied right eigen-density `Φ(ρ*) = r ρ*`, with `r > 0`, gives the true finite record operator `r^n ρ*`, success probability `r^n`, and unchanged positive-probability conditional state. The source instrument's actual probability bounds imply `r ≤ 1`.

`InvertibleFilter` supplies only matrices `S,T` and the two inverse equations `TS = ST = I`. Write

\[
F(X)=SXS^\dagger,\qquad H=S^\dagger S,\qquad
\mathcal F(\rho)=F(\rho)/\operatorname{Tr}F(\rho).
\]

Invertibility and the PSD zero-trace theorem prove strictly positive filtered mass for every density. The normalized `F.state` is therefore an actual `Density` construction. It is generally nonlinear, and the unnormalized filter need not decrease trace. Its normalizer must not be read as a physical success probability.

Given the actual left Heisenberg eigenrelation `Φ*(H) = r H` and `r > 0`, `doob_complete` proves the weighted Kraus Gram identity. `doobWeighted` and the existing verified square-root conversion then construct the ordinary complete instrument with Kraus matrices

\[
\widetilde K_k=r^{-1/2}S K_k T.
\]

Completeness and stationarity are conclusions, not supplied fields. The actual transformed map and its finite iterations satisfy, for every complex operator,

\[
\widetilde\Phi(X)=r^{-1}F\bigl(\Phi(TXT^\dagger)\bigr),\qquad
\widetilde\Phi^n(F(X))=r^{-n}F(\Phi^n(X)).
\]

`eigenmetric_successMass` proves the corresponding real-trace `mass` identity on all complex operators. For density inputs the relevant PSD traces are real. The same left spectral data prove strictly positive actual source survival for every initial density and every finite length, without a right eigenstate assumption. `doob_finite_conditioning` then proves

\[
\mathcal F\left(\frac{\Phi^n(\rho)}{\operatorname{Tr}\Phi^n(\rho)}\right)
=\widetilde\Phi^n(\mathcal F(\rho)).
\]

The right eigen-density assumption is separately needed to conclude that `F.state ρ*` is a fixed point of the actual transformed `channelState`. The transformed visible outcome type is `Unit`, with the Kraus indices summed internally. The named record results concern repeated selected-success words; they do not assert equality of arbitrary monitored Kraus paths or of different operation libraries. General initial source probabilities need not equal `r^n`.

The rational two-dimensional witness uses `r = 3/16`, `S = diag(2,1)` and

\[
\rho_* =\tfrac15\begin{pmatrix}1&2\\2&4\end{pmatrix},\qquad
\sigma_+=\mathcal F(\rho_*)=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

Its exact source Kraus family includes an identity component and two noncommuting Kraus matrices; the success map sends `|0⟩⟨1|` to `|0⟩⟨1|/16`, retaining input coherence. Failure Kraus complete the source Gram sum. The filter normalizer is `8/5`, explicitly greater than one. The actual Doob map has the full **complex-trace** formula

\[
\widetilde\Phi(X)=\tfrac13X+\tfrac23\operatorname{Tr}(X)\sigma_+.
\]

This extends the earlier measure-prepare embedding beyond maps whose output is always diagonal. Spectral-data existence, dominance, uniqueness and infinite conditioning limits are not outputs of the generic construction. The new noncommutative module uses the declared quantum matrix structure; its own proof chain does not directly call Core to derive that structure. The separate diagonal `Survival` bridge retains its direct Core theorem calls.

## Direct Core reuse

| Existing Core theorem or constructor | Actual QM consumer |
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
| `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.registered_organizational_attributes_preserved` | `UEOTQM.CorePurificationBoundary.terminal_eq_iff`, then actual terminal-quotient injectivity |
| `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.organizationalTerminalControl` | `UEOTQM.CorePurificationBoundary.terminalControl` |
| `UEOT.V3.FiniteStablePartition.terminal_stable` | `UEOTQM.CorePurificationBoundary.finiteCoreSlice_holds` |
| `UEOT.V3.ViabilityTrajectory.stationaryTrajMeasure_coordinate` | `UEOTQM.CorePurificationBoundary.actualPath_first_quotient_marginal` |
| `UEOT.V3.ViabilityTrajectory.all_times_safe_of_coordinate_one` | `UEOTQM.CorePurificationBoundary.actualPath_all_times_safe` |
| `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.registered_survival_two_hidden_states_merge` | `UEOTQM.CorePurificationBoundary.restricted_support_merge`, then the pure restricted-readout quotient marginal |

Quantum compatibility is proved from actual Kraus/posterior definitions and prefix-closed word responses. It is not supplied as a field assuming the desired update theorem. The closed update carries the posterior as a witness of membership in the same response range.

## Scope

The finite complex density/Kraus sector is explicit input. No reconstruction of Hilbert space, Born probabilities, a value of Planck's constant, or a complete real-world gauge theory is asserted. The arithmetic spectrum bridge does not establish representation theory, global anomalies, a vacuum, masses or phenomenological viability.

The [executable Python kernel](../../physics/qm/kernel/README.md) uses exact Gaussian rationals, nonnegative rational Kraus weights and a finite word-effect basis. Its new `export_representation_certificate` / `verify_representation_certificate` API checks portable exact witnesses without rerunning the closure producer. This is executable evidence, not a Lean proof token.

The exact Gaussian-rational interpretation, nonnegative weighted-Kraus realization, finite ragged-index embeddings, and generic exact certificate checker are now proved in Lean. Open program refinements remain: the JSON parser and exporter on all inputs, closure-search termination and Gaussian elimination, PSD decision procedures, label-to-index mapping as a program, and Python adaptive-tree traversal. The new finite-generator existence theorem does not establish the search program or a dedicated Lean proof of the Hermitian `d²` dimension formula. A smaller response representation also does not imply a smaller physical CPTP Hilbert realization.

The Python representation checker supports Hilbert dimensions 1–4, at most `d²` basis effects, and word witnesses of length at most `d²−1`. These bound the evidence format rather than the language of future finite records. That representation checker has no uniform integer-bit or operation-library cap; the separate Lean exporter imposes the explicit bounds listed below. Another valid short-word basis is accepted under its own context when an expected basis fingerprint is not pinned; arbitrary linear mixtures are outside this word-witness format.

## Runtime and evidence

The [runtime manual](../../physics/qm/kernel/README.md) documents the export API, exact examples and independent tests. Each verification receipt binds the tested source bytes rather than merely naming a release. The source manifest includes generic Lean modules, locks, scripts, runtime source, fixed proof fixtures and the workflow. Reusing local dependency caches does not replace the actual proof build or axiom audit.

The exporter additionally limits input literals to 4096 bits, padded scalar storage to 65536 entries and source size to 8 MiB. The separate representation checker retains its own contract. These bounds constrain evidence construction, not future finite-word length; no uniform compilation-time guarantee is asserted.

The next reconstruction work needs typed complete state, effect, composite, discard and convex-purity interfaces, together with constructive quantum examples and the existing countermodels. The next stability work needs an explicit joint classical-record/quantum-memory CPTP representation and actual label-aware defects; outcome-forgetting defects do not supply that result. Density separation and norm identification remain separate mathematical obligations. The current rational noncommutative Doob model gives a concrete next target for exact iterates, uniqueness and conditional-state rates. General spectral-data existence, dominance, full Cesàro projection results and infinite-horizon conditioning remain separate tasks. Physical G3 applicability, QDRR experiments, CV energy/definition-domain control, and model-specific QFT/RG remain separately tracked in the [whole-QM roadmap](../../physics/qm/ROADMAP.md).
