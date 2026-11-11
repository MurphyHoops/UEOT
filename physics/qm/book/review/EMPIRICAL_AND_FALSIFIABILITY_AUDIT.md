# Empirical and falsifiability audit / 实证与可证伪性审查

## 1. Identity, scope, and audit status

**Review date:** 2026-11-11 (UTC). **Reviewer:** internal agent B, independently assigned to empirical claims, primary literature, competing explanations, and experimental statistics. This is an internal scientific red-team review, not external peer review.

The reviewed Chinese source is `physics/qm/book/UEOT_PHYSICS.md`, edition 3.5, in repository `MurphyHoops/UEOT`, at commit `3d443ec29eb17af1fc00699a74e2d42d73516d81`; SHA-256 `b726e3b9033d79ef949b8e83469901fe728aa28ab204b2e4d55bf36a18b412f0`. It contains chapters 0–65 and appendices A–F. This report is a derivative review of those chapters and their existing result IDs; it does not establish a second claim ledger. `CHAPTER_DOSSIER.json`, `SOURCE_MANIFEST.json`, and the existing Core→Physics contract remain the authoritative project registries.

**Subsequent research update:** §9 extends this review to newly merged chapter 66 at main `925e3a8a411c0b1bab99dd9150bf005893656140`, yielding coverage of all 67 chapters and appendices A–F for the enlarged publication. The initial 66-chapter identities, findings, and `[0,65]` metadata correction are retained as historical checkpoints; they are not retrospectively rewritten as reviews of a chapter that had not yet been supplied.

Coverage means that every chapter was checked for empirical assertions, scientific status, numerical-evidence language, and originality boundaries. High-risk chapters 6–8, 17–18, 28, 31, 34, 36–42, 46–48 and the source/evidence appendices received close contextual review. This is not a claim to have independently re-proved every mathematical theorem or rerun every Lean/build gate. Original literature was located and checked at the depth recorded in the companion `PRIOR_ART_AND_EXPERIMENTAL_STATUS.md`. No hardware experiment, acquisition of unpublished data, or independent reanalysis of experimental raw counts was performed.

**Overall finding:** the baseline already makes unusually explicit distinctions between standard quantum mechanics, conditional UEOT constructions, formal proof, synthetic benchmarks, and nature. No inspected passage justifies saying that UEOT has a confirmed new natural law, that Core uniquely derives complex quantum mechanics, or that QDRR has detected objective collapse. The main publication improvements are to attach actual experimental sources to the record discussion, correct one bibliographic title, update a stale chapter-range example, and preserve the mathematical/empirical boundary in translation. Mechanism selection remains OPEN.

## 2. Required corrections and additions

| Audit item | Location | Finding | Required editorial action |
|---|---|---|---|
| B-01 | Appendix C.3, item 4 | The title attached to arXiv:1512.00589 is not the current paper title. | Use Pollock et al., *Non-Markovian quantum processes: Complete framework and efficient characterization*, PRA **97**, 012127 (2018), DOI `10.1103/PhysRevA.97.012127`. Retain the separate PRL **120**, 040405 operational-Markov paper in item 3. |
| B-02 | §48.2 YAML | `chapter_range: [0, 56]` is stale despite the surrounding 0–65 description. | Change to `[0, 65]`; this is metadata repair, not a mathematical migration. |
| B-03 | Chapters 6–8 | Sound caution about Quantum Darwinism has too little source-resolved experimental context. | Add a compact table of actual photonic, NV, and superconducting experiments, with precise observable and inference boundaries. Do not import a paper's promotional language as a stronger conclusion. |
| B-04 | §§8.4, 41.2; R3/R4 | Hardware mismatch and fundamental nonunitarity are correctly distinguished. | Preserve this distinction; explicitly classify QDRR as a proposed protocol family, not an already executed UEOT experiment. |
| B-05 | §28.1 | The frozen inverse-alpha input is already described as a reproduction input, not a current precision determination. | Optionally identify its CODATA 2018 provenance without changing the benchmark number or rerunning the frozen test for cosmetic reasons. |
| B-06 | Public-record explanation | Mutual-information plateaus alone need not certify accessible classical records; stronger objectivity conditions need their own hypotheses. | If strong Quantum Darwinism/SBS is discussed, cite the 2021 correction: conditional pairwise independence is insufficient; full conditional factorization is required. Do not retroactively claim the existing book made this error. |
| B-07 | Whole book | The proposed expression `q=exp(-xi Lambda)` is **absent** from the bound source. | Do not describe it as an existing universal law of this edition. Any contextual discussion must identify it as an additional model ansatz with a specified generator, units, and time regime. |
| B-08 | Existing verification receipts | Historical/local source states are distinct from observed current remote acceptance. | Keep original receipts unchanged and attach the root editor's separately verified current commit/CI identities to the publication manifest. Agent B did not independently query GitHub CI. |

No correction in this table requires altering the physical kernel, raw data, frozen Core, or Lean source. Chinese/English insertion text is supplied separately for integration.

## 3. Claim-to-test matrix

The claim IDs below are existing book IDs or explicitly named research packages. “No data” means no UEOT experiment in the reviewed edition, not that quantum mechanics lacks experimental support.

| Existing claim / chapter | Standard-physics prediction | Additional UEOT or model premise | Possible difference and observable | Data and estimator | Statistical contract | Present status | Failure condition / competing explanation |
|---|---|---|---|---|---|---|---|
| Public records, ch.6 | Unitary entanglement can distribute distinguishable pointer information while retaining global coherence. | Chosen record algebra, fragment partition and allowed access. | No necessary new natural prediction. Measure fragment information and global coherence separately. | Published QD experiments listed in companion report; no UEOT counts. | Tomography/entropy uncertainties, fragment choice and accessible-information definition must be explicit. | Standard-QM-compatible reconstruction. | A claimed public-record criterion fails if records cannot be read reliably or their reading disturbs the stipulated record; this does not falsify QM. |
| SRN classification, ch.7 | A CPTP map strongly preserving every within-branch state has a correlation-matrix Schur form. | Exact strong nondisturbance, fixed projectors, finite dimension; stronger than population preservation. | Channel model test through populations, intra-branch states and inter-branch coherences. | Prepare/tomograph sufficient inputs; no acquired data. | Simultaneous confidence region and separate model-residual test. | Conditional theorem; empirical applicability untested here. | Leakage, population transfer or within-branch disturbance invalidates the SRN model. |
| P-QQDR-01–03, ch.8 | Reversing all controlled record-writing degrees of freedom recovers coherence when intervening joint dynamics is reversed. | Specified writing isometry, full unitary extension, known initial register and bounded uncontrolled environment. | A constrained extra channel could leave residual off-diagonal factor `K_ab`; standard uncontrolled environments can do so too. | Phase-pair expectations estimate real/imaginary `K_ab`; no QDRR hardware data. | For independent fixed-expectation outputs in each setting, the stated Hoeffding union bound applies; retain PSD-projection residual. | Proposed tomography/diagnostic protocol. | Candidate model fails when calibrated confidence region excludes its predicted channel. An excess residual rejects the combined control/noise model before it identifies fundamental collapse. |
| M-01–02, ch.38 | Finite-dimensional CP homogeneous dephasing semigroups obey rate and cycle-phase constraints. | Fixed branch decomposition and time-homogeneous semigroup with finite rates. | Measured rates and cycle phase must satisfy the bound. | Fit at multiple times with phase-unwrapping convention; no acquired data. | Propagate correlated fit/calibration uncertainty into joint inequality. | Conditional constraints, not a unique UEOT prediction. | Violation may reject Markov homogeneity, SRN, calibration, or CP model assumptions. Nonzero cycle phase excludes diagonal Gaussian diffusion only, not classical Poisson phase jumps. |
| M-03–05; E-01–02, ch.39 | Standard quantum environments can generate channels outside classical diagonal random-unitary phases. | Four fixed branches, prepared `+_4`, stated effect and calibrated pointer preservation. | Event probability below the classical lower bound excludes that noise class. | Event count and calibration data; no acquired data. | Ideal lower bound `p*=0.0158446719…`; zero accepted events in 188 trials give fixed-sample tail <0.05 only under the stated null. | Analytic witness with exact/model checks. | Ordinary non-diagonal unitaries, leakage, SPAM or uncontrolled quantum environment remain alternatives unless separately excluded. Witness success is not evidence of collapse. |
| P-UST-01–02, ch.46 | Conditional Bernoulli lower bounds imply binomial tail domination / nonnegative supermartingale tests. | Every history-conditioned trial obeys `p_t≥p_0`, with valid calibration information. | Valid rejection despite allowed temporal dependence. | Full ordered binary record, predetermined stopping/test parameters. | Calibration plus test error at most `alpha_cal+alpha_test`; no post-hoc maximization over q. | Statistical theorem, not executed test. | A marginal/time-average bound is insufficient; hidden common-variable counterexample in §46.2 shows failure. |
| C-02–04, ch.40 | Standard normalized diffusive SSE has linear CP ensemble dynamics and QND Born-weight absorption. | Specified noise law, Hermitian A, gamma, finite spectrum; `[H,A]=0` for absorption theorem. | As a fundamental hypothesis it needs independently fixed rate/activation and predictions beyond ordinary monitoring. | Branch weights, contrast, heating or diffusion measured under the same parameters; no new data. | Joint likelihood/confidence set across observables, nuisance hardware bounds, held-out prediction. | Conditional stochastic model; fundamental interpretation OPEN. | Candidate is rejected by any calibrated observation outside its jointly predicted region; fitting each dataset with a different strength is not a test. |
| C-05, ch.41 | Every finite CPTP channel has an environmental dilation; finite multi-time causal processes admit memory dilation. | No unrestricted “hidden-environment exclusion” is supplied. | System-only CPTP statistics alone need not distinguish collapse from a quantum environment. | Any finite set of system interventions; no new empirical assertion. | Compare complete intervention process, not just one-time reduced state. | Identifiability obstruction. | A new mechanism must constrain alternatives or predict shared parameter relations, energy costs, or independently controlled global reversal. |
| G-01–02, ch.36 | Gauge anomaly and one-loop beta calculations constrain a stipulated matter spectrum. | Frozen representations, thresholds and scalar census. | Five-color countermodel prevents unconditional three-color/three-generation uniqueness. | Algebraic/exact checks, not particle-discovery data. | No statistical acceptance; empirical spectrum matching is a separate task. | Conditional classification and counterexample. | A representation/threshold change requires recalculation; local anomaly cancellation does not prove global consistency or nature's choice. |
| F-01–03, ch.37 | Rank-one nonuniversal neutral currents imply algebraic flavor relations. | Specified extra vector, rank-one splitting, nondegenerate mass basis, mixing and EFT domain. | Correlated neutral-current/FCNC amplitudes could constrain this candidate. | No fitted collision/flavor dataset in book; matrix inputs are model parameters. | Full matching, running, hadronic uncertainty and simultaneous parameter confidence set are needed. | Testable model relations; no UEOT-specific observation. | Failure of rank-one relations rejects that candidate. Heavy-vector decoupling or vanishing splitting prevents a parameter-free discovery prediction. |
| QED/QFT/RG/EFT, ch.21–30,45 | Known actions and approximations reproduce standard perturbative or finite-lattice quantities. | Action, field content, scale, scheme, regulator and truncation choices. | No independent new prediction presently supplied. | Frozen exact/floating benchmarks, no new collision data. | Numerical error differs from physical truncation and parameter error. | Standard-physics reproduction and interface construction. | Wrong convergence, symmetry, threshold or error control invalidates a computation; matching a known result alone does not select UEOT. |
| Finite kernel, ch.49–65 | Finite complex QM has the listed probability, purification, distance and protocol properties. | Complete state/effect/Kraus models and finite controller contracts. | Device applications need calibrated implementations; formal acceptance has no novel physical effect by itself. | Exact rational witnesses and bound source receipts. | Deterministic mathematical acceptance, not frequentist evidence about nature. | Formalized mathematical pieces within the quantum sector. | An implementation not satisfying the input contract is outside scope; alternate Core-compatible sectors remain relevant to selection. |

## 4. Numerical and statistical checks actually made in this review

The following small arithmetic checks were executed locally in Python on 2026-11-11. The reproducible standard-library script `empirical_number_check.py` and actual receipt `EMPIRICAL_NUMBER_CHECK.json` additionally verify the adjacent integer thresholds using 80-digit decimal arithmetic; all eight checks passed. Run `python empirical_number_check.py --output EMPIRICAL_NUMBER_CHECK.json` in the script directory. The receipt binds the script SHA-256, source identity, inputs, formulas, runtime and actual timestamp. These are scoped calculations, not a rerun of the inherited 757-check benchmark suite and not new experimental data:

| Quantity | Recomputed value | Interpretation |
|---|---|---|
| `ceil(2 log(2×6/0.05)/0.12²)` | 762 | §8.3 samples **per setting**, for six real settings and outputs in `[-1,1]`. |
| `(3−2√2)/(4(2+1/√2))` | 0.0158446719248555 | Ideal event lower bound in ch.39/46. |
| `(1−p*)^187` | 0.0504547642260996 | Zero accepted events in 187 trials do not reach the displayed 5% threshold. |
| `(1−p*)^188` | 0.0496553250398911 | Zero accepted events in 188 trials reach the displayed ideal fixed-sample threshold. |
| `p*²/8` | 0.0000313817035508 | With zero SPAM allowance, the book's conservative `p_0≥p*−sqrt(8 ell)` is informative only below this pointer-error scale. It is a limitation of this bound, not a proven hardware impossibility. |

The original text already states the crucial qualifications: per-setting independent samples for Hoeffding; conditional trial bounds for dependent trials; finite simultaneous calibration coverage; no post-hoc q optimization; no silent deletion of leakage; and no universal claim that 188 shots suffice on real hardware. These qualifications must survive translation.

## 5. Mechanism and exponential-law boundary

No occurrence of `q=e^{-xi Lambda}` was found in the bound book; the occurrences of `xi` in the QED portion concern a gauge parameter. It would be inaccurate to audit an absent equation as if it were the edition's proposed universal collapse law.

For any future use of an exponential attenuation ansatz, specify what q is (amplitude, probability, or coherence magnitude), what Lambda measures, and how xi acquires inverse units so that the exponent is dimensionless. A fixed two-branch dephasing semigroup can have `K_01(t)=exp[(-Gamma+i omega)t]`; a time-local commuting model can replace Gamma t by an integrated rate. Those are model-dependent results. Positive cumulative damping cannot describe arbitrary coherent revival, and non-Markovian memory cannot be compressed into the same nonnegative universal rate without additional proof. A zero coherence at finite time also need not belong to a finite-rate time-homogeneous semigroup.

Core does not presently specify a numerical `K_01`, an actualization strength, or an objective-record activation rule. Defining “objective record” observationally and then choosing a loss parameter after seeing the data would not identify a mechanism. A physically distinguishable candidate must fix its activation domain and cross-observable relations before the test. If its allowed strength includes zero without an independent lower bound, a null result constrains the strength but cannot reject the entire enlarged family.

## 6. Whole-book empirical coverage

Codes in this **review table only**: **S** standard physics/mathematics; **C** conditional construction; **N** numerical/formal witness; **T** proposed empirical test; **O** unresolved mechanism or applicability. These are not replacements for the book's D/P/K/H/S/E/N/O or C/B/S/P/E/O/X fields. The per-chapter row points to the empirical responsibility, not an assertion of external confirmation.

Rows 0–65 and A–F describe the initial edition-3.5 review. The explicitly marked row 66 is the subsequent v31.10 research increment reviewed in §9; the enlarged book's 173-ID count does not alter the historical 161-ID checkpoint.

| Chapter | Evidence role and audit outcome |
|---|---|
| 0 | C/O: seven-level boundaries, input identities and no-completion claims are essential. |
| 1 | C/O: Core bridge organizes quantum realizations; it does not select natural complex QM. |
| 2 | S/C/O: cited operational reconstruction is an external conditional theorem, not empirical confirmation; preprint status retained. |
| 3 | C: Fisher/action/Born route depends on its statistical and amplitude choices; no independent measured constant derived. |
| 4 | S: standard finite states, effects and channels; quantum realization is an input. |
| 5 | C: prediction equivalence depends on allowed instruments and access. |
| 6 | S/C: coherent parent and public records; add actual QD experimental references and accessible-record caution. |
| 7 | C/T: exact SRN classification; actual apparatus must satisfy strong nondisturbance. |
| 8 | T/O: QDRR and tomography proposed; no executed UEOT hardware experiment. |
| 9 | S/C: no-cloning, QEC and metrology are standard; application gains depend on noise and resources. |
| 10 | S/C: infinite-dimensional domain/normality requirements are not experimental claims. |
| 11 | S/C/O: CCR/Weyl and common action scale require inputs; no new value of hbar. |
| 12 | S/N: standard solvable-model calculations and reproduction checks. |
| 13 | S/C: finite-mode Gaussian model; not universal continuum physics. |
| 14 | S/C: symmetry/spin inputs and physical selections stay explicit. |
| 15 | S/C: statistics/Fock/superselection requires fixed observables and sector. |
| 16 | S/N: finite many-body examples do not prove thermodynamic-limit phases. |
| 17 | S/C: GKSL/thermal-bath approximations need their time and bath regimes. |
| 18 | S/C: interventions and process memory; correct framework title in Appendix C. |
| 19 | S/C: thermodynamic response uses equilibrium/detailed-balance assumptions. |
| 20 | C: task objectives/control costs are chosen; no universal natural optimizer established. |
| 21 | S/O: relativistic/QFT assumptions separately supplied. |
| 22 | S/N: free-scalar calculations; field existence/continuum requirements remain distinct. |
| 23 | S/C: Dirac/Maxwell degrees of freedom from specified field model. |
| 24 | S/N: scattering/functionals are standard computations with perturbative domains. |
| 25 | S/N: one-loop benchmarks, scheme and truncation explicitly required. |
| 26 | S/C/O: Wilsonian, object and intervention coarse-graining not interchangeable. |
| 27 | S/N: QED Ward/BRST checks do not establish a full nonperturbative gauge theory. |
| 28 | S/N: alpha input is frozen; no precision experiment or UEOT constant prediction. |
| 29 | S/C: gauge/SM candidate and anomaly checks; global consistency distinct. |
| 30 | S/C/O: Higgs/Yukawa/neutrino inputs do not become derived particle masses. |
| 31 | C: generation/color result limited to stated spectral/weak-window assumptions. |
| 32 | C/O: earlier topological and selection routes retain countermodels/open status. |
| 33 | C: implementation contract does not amount to realized hardware. |
| 34 | S/N/T: device and control paths; Majorana sources are theoretical proposals, not claimed observations. |
| 35 | C: instrument/record error composition needs physically bounded defects. |
| 36 | C/N: correct high-energy field census retains five-color counterexample. |
| 37 | C/T: rank-one flavor sum rules need matching/data before exclusion. |
| 38 | C/T: cycle-phase constraints do not exclude every classical noise model. |
| 39 | C/T: four-level witness excludes a named model class; quantum environment remains possible. |
| 40 | S/C/O: stipulated SSE gives conditional absorption/heating; fundamental actualization remains unselected. |
| 41 | S/C: dilation identifiability obstruction properly retained. |
| 42 | T/O: executable research contract, with explicit absence of hardware results. |
| 43 | S/C: ring flux/boundary spectrum is standard model physics, not a new hbar derivation. |
| 44 | S/N/T: Berry/SSH have original prior art; local peak alone not a topological certificate. |
| 45 | S/N/O: finite lattice existence and one-plaquette Z2 enumeration do not prove QCD mass gap. |
| 46 | C/T: correct conditional-null/optional-stopping distinctions; arithmetic checked. |
| 47 | T/O: roadmap deliverables remain prospective, with failure gates. |
| 48 | C: three status axes distinct; stale YAML range requires correction. |
| 49 | N: exact certificate/finite Lean acceptance, not experiment. |
| 50 | C/N: probability distance and conditional error bounds need real defect certificates. |
| 51 | C/N: same-library mixtures; arbitrary unknown noise not silently included. |
| 52 | S/C/N: stationary/Cesaro statements differ from general mixing or apparatus equilibration. |
| 53 | C/N: supplied spectral objects; finite survival and Doob distributions not interchangeable. |
| 54 | C/N: classical-sector countermodel is mathematical selection evidence. |
| 55 | S/C/N: real-sector local tomography separation is exact model probability separation. |
| 56 | C/N: coherent finite Doob channel; no general infinite conditioning theorem. |
| 57 | S/C/N: finite purification and operational presentations; reconstruction backgrounds still needed. |
| 58 | C/N: joint records and feedback need actual access/controller model. |
| 59 | C/N: exact noncommuting example not a universal convergence law. |
| 60 | S/C/N: complete complex local tomography; no unique natural sector inferred. |
| 61 | S/C/N: purification-unitary existence not certified numerical synthesis or empirical proof. |
| 62 | C/N: same causal controller and modeled quantum memory; true calibration inputs still needed. |
| 63 | S/C/N: trace-distance/Helstrom relation standard; formalization does not establish new physics. |
| 64 | S/C/N: exact rank/minimal ancilla dimension differs from tolerance-dependent hardware cost. |
| 65 | C/N: bounded finite stopping protocols; unbounded/continuous limits remain separate. |
| 66 (subsequent research increment) | S/C/N/T: same-source finite conditional CQ law, restricted action realizability, initialization, early-stop cost and error. All 16 sections and the original Doob precedent were reviewed; no hardware data or unconditional resource advantage. See §9 and `CH66_EMPIRICAL_REVIEW.md`. |
| A | S/C: units and external theorem responsibility; keep hypotheses alongside use. |
| B | Registry of 161 result IDs; count is neither originality count nor experimental confirmations. |
| C | Source/provenance; one title correction; add experiment identities without copying third-party content. |
| D | 757 inherited checks are exact/deterministic/synthetic, executed historically; no raw experimental data. |
| E | Publication/build identity; local build and remote CI are separate evidence. |
| F | Formal declaration/source audit; accepted names do not prove the whole physical theory. |

## 7. What remains OPEN after publication

1. A physically motivated mechanism that selects the full complex quantum state/effect/composition structure from Core-compatible alternatives.
2. A fully specified actualization law with a rate, activation rule, composite-system behavior, energy budget and independently discriminating data.
3. An executed QDRR dataset with raw time-ordered outcomes, calibration, all leakage/failure records, model alternatives and preregistered rejection conditions.
4. A calibration regime that makes the four-level witness's conservative probability bound informative.
5. A particle-physics selection mechanism excluding surviving spectra under correctly computed thresholds, rather than changing the premise after seeing the desired color/generation count.
6. Controlled extensions to infinite-dimensional memory, unbounded stopping, nonperturbative continuum QFT and quantum gravity.

These are scientific or development obligations, not publication defects that can be repaired by stronger wording. The revised book should explain them clearly without presenting an internal review as scientific-community endorsement.

## 8. Rights and evidence handling

Only bibliographic metadata, links, short original summaries, and independently written analysis are proposed for integration. No third-party article, figure, dataset, or code is relicensed or republished. Historical CC BY book expression retains its existing grant; the root editor must apply `LICENSE`, `LICENSE_SCOPE.md`, `COPYRIGHT.md`, `physics/LICENSING.md`, and `PUBLICATION_RIGHTS.md` to new original editorial/translation expression. This review does not modify those policies.

## 9. Chapter 66 research increment: 67-chapter coverage

The newly merged v31.10 research book is edition 3.6, with chapters 0–66 and 173 stable IDs; the bilingual publication is being advanced to edition 3.7. This update was read from main `925e3a8a411c0b1bab99dd9150bf005893656140`. Its research book SHA-256 is `eabce172cd32773e21fa5373359d0fef7e52442b5d0368e11268130b4f89e921`; the assigned chapter extraction SHA-256 is `0b108dcda4c78483230101adf48869a1e2cee4441b67665d4e1cf4429d128b3a`, matching main up to boundary whitespace. The entire new chapter, book diff, current research status, runtime/Lean receipts, and committed remote-verification records were read. `CH66_EMPIRICAL_REVIEW.md` gives the detailed review of all 12 new result IDs and the numerical examples.

**Incremental conclusion:** PASS for the stated empirical and resource scope. The chapter constructs a conditional process within standard finite complex quantum mechanics; it does not add an independently observed UEOT mechanism. Its prospective tests concern implementation of a specified instrument/control/resource contract. The previous B-02 repair `[0,56] → [0,65]` remains the correct historical repair. Current chapter-range metadata separately advances to `[0,66]`.

| Existing claim IDs | Standard-physics prediction | Additional operational assumptions | Observable, data, and statistical responsibility | Current status and failure condition |
|---|---|---|---|---|
| P-FCOND-01–04 | Backward acceptance effects and support-transformed complete instruments reproduce the accepted original CQ leaf law. | Fixed finite original tree/event, complete instruments, correct support, positive acceptance probability and transformed initialization. | Full visible records and terminal states, including all failures in the original experiment; no acquired data. Calibration must bound joint-output error. | Conditional proof/witnesses. Failure of a calibrated device to match the declared CQ law rejects that realization; marginal agreement alone is insufficient. |
| P-FCOND-05–06 | Labelled Choi convex combinations characterize a specified randomization class; linear separators exclude it. | Finite allowed library, declared input restriction and shared weights under the actual observation permission. | Instrument tomography and chosen randomization weights; no acquired data. A noisy exclusion needs a confidence region for the separating functional. | Exact model certificates, with distinct floating LP diagnostics. Adding new actions, postselection or observation access changes the tested class. |
| P-FCOND-07 | Normalized filtering is generally nonaffine; scalar and rank-one system-marginal cases are exceptional. | Same deterministic map for all unknown inputs; external-reference preservation is a separate task. | Mixture consistency and retained-reference correlations. Exact finite controls exist; no hardware implementation has been certified. | Paper classification. One known-input demonstration cannot certify a universal channel; local rank-one replacement does not reproduce the filtered reference joint state. |
| P-FCOND-08 | A legal scaled filter gives success `p_G/c` with the specified posterior. | Admissible scaling, available complete filtering instrument and fresh independent preparation for retries. | Pass/fail frequency, posterior tomography and preparation/reset accounting; no data. | Conditional realization. The scale optimum is confined to the stated one-Kraus family, not all possible algorithms or resources. |
| P-FCOND-09 | Independent reset yields expected total cost `mu/p`, including early stopping. | Repeated fresh independent trials, nonnegative consistent cost units and actual failure/reset charges. | Ordered success/failure records with measured operation, preparation, randomization and calibration costs. A real advantage requires uncertainty-aware comparison of complete budgets. | Finite recurrence and paper expectation argument. Drift, correlated failed resets or omitted costs invalidate a claimed resource comparison. |
| P-FCOND-10 | Same-event postselection amplifies complete-output error by the stated sharp factor. | Same acceptance extractor, positive probabilities and a bound on the full output law. | Unselected complete records are required to establish the source error; no measured dataset. | Conditional theorem/exact examples. Good selected samples do not establish the required full-output error bound. |
| P-FCOND-11 | Legal Kraus approximation bounds local labelled distance and its protocol propagation. | Complete action families, common controller, compatible labels and certified operator errors. | Independent action and norm error certificates; a retained modeled reference may be included. | Paper sufficient bound. Floating residuals do not automatically give strict upper bounds; unmodeled couplings are excluded. |
| C-FCOND-01 | Small positive eigenvalues can make support inverse roots unstable. | Exact spectral/support interpretation. | Conditioning diagnostics; this is not a new natural-effect prediction. | Exact counterexample and recorded numerical controls. A small positive mode cannot silently become a zero mode. |

The Pauli example has original acceptance `1/8`, early-stop cost `7/4` per attempt and `14` per accepted output under its declared action-only units. The allowed implementation uses three actions plus `3r` randomization overhead; preparation, reset, readout and calibration can remove the model advantage. The non-scalar example has acceptance `117/4096`, costs `701/512` and `5608/117`, and scaled-filter probability `39/(39+sqrt(565))`; its original-only action library is explicitly excluded. These values agree with the inspected exact receipt. They are not measured hardware results.

Carollo et al., [PRA 98, 010103(R), 2018](https://doi.org/10.1103/PhysRevA.98.010103), already supply a finite-time, time-dependent quantum Doob construction. The original manuscript's relevant sections and Eq. (11) were read; its finite-time examples are numerical trajectories. Chapter 66 should explicitly retain this precedent. The present chapter's added finite-tree, support, allowed-library, and resource responsibilities are separately argued, without asserting worldwide priority from a single-source comparison.

The v31.10 research executions have their own identities: 19 semantic runtime tests, 95 exact finite symbolic checks, and 1285 named Lean axiom-audit reports. The latter accompany 959 explicit theorems in 49 public modules; 1285 is not a theorem or new-law count. Committed PR run `42966223125` and main run `42967294067` records report success. Agent B read those records and directly matched all nine runtime source hashes, without making a new live API query or rerunning the scientific gates. This edition-3.7 publication reuses that identified evidence; it does not relabel the v31.10 runs as new publication executions. The previous 757 checks retain their edition-3.0 identity.

## Edition3.8 / chapter67 empirical increment

No new real device data were obtained. The 80000 calibration flags and two 4096-record holdouts are explicitly synthetic; chronological order is logical shot order, not measured hardware timestamps. Flag frequency identifies q only within the fixed source relation and iid assumptions. It does not certify source/action gate identity or complete terminal quantum states. A correlated-shot negative control invalidates the iid confidence statement while preserving the single-shot marginal. The full-record bound 3673/102400 is a model-conditional guarantee, not a measured apparatus error. Exact missing inputs, readout failures/leakage and cost fields are in [DATA_AND_COST_CONTRACT](../../operational_micro_robust/DATA_AND_COST_CONTRACT.json). One-time calibration cost is amortized per delivered output, outside the per-attempt retry numerator. Standard environment realization already covers the shared microscopic model, so it does not identify objective actualization.
