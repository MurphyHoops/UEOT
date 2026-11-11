# Physical Derivation Audit / 物理推导审查

**Review identity:** internal theoretical and mathematical-physics review by subagent A; this is not external peer review. **Reviewed source:** `MurphyHoops/UEOT` main `3d443ec29eb17af1fc00699a74e2d42d73516d81`; Chinese manuscript SHA-256 `b726e3b9033d79ef949b8e83469901fe728aa28ab204b2e4d55bf36a18b412f0`. The publication editor must attach the final revised manuscript identity separately. This report reviews the inherited scientific contract; it does not replace the existing claim ledger or execution receipts.

## 1. Outcome and review limits

The scientific content of all 66 chapters and Appendices A–F was reviewed. All 161 stable result IDs were inventoried against `CHAPTER_DOSSIER.json`. No reviewed argument requires withdrawing a stable theorem or changing its identifier. Several precise editorial corrections are necessary: the commutant of a permutation representation was called a commutative algebra; an implication direction in the purity discussion was reversed verbally; a chapter range is stale; historical executions were sometimes described as executions of the present edition; and an earlier description of missing trace-distance formalization was not updated after Chapters 60 and 63 closed it.

This finding is narrower than a new machine verification of the whole kernel. We did not re-run the 8,805-job build, all 1,123 axiom queries, or 757 inherited numerical checks. We statically checked every source binding attached to the numbered results: **111 bindings, no missing files, no hash mismatches**. Five initially unmatched lexical names were resolved as one generated structure constructor and four uses of dotted theorem declarations. The **1,123 unique names in Appendix F match `scripts/AxiomAudit.lean` exactly and in order**. Important public theorem types and the relevant proof interfaces were inspected directly. Existing compiled acceptance receipts retain their original identities.

An intact formal proof establishes the theorem expressed by its actual types under its declared axioms. It does not establish that the chosen states, effects, dynamics, apparatus, or finite spectral template describe a physical system. Numerical regressions check finite computations and implementation agreement; they do not certify a universal theorem or natural law. The full empirical audit is supplied independently by reviewer B.

## 2. Required seven-level dependency chain

| Level | What the book actually uses | What follows and what does not |
|---|---|---|
| L1: established mathematics and physics | Complex linear algebra; standard finite quantum states, POVMs, instruments, CPTP maps; spectral and reconstruction theorems; conventional QFT/EFT calculations | These are inputs or prior results. Re-expression or Lean formalization is not a priority claim for the underlying physics. |
| L2: UEOT Core | Conditional predictive equivalence, response quotients, transport, finite protocol and selected QSD/Doob interfaces | They support conditional interfaces. The classical countermodels prevent inferring complex quantum theory from generic Core alone. |
| L3: physical sector choice | Complete complex density/effect spaces, tensor products, allowed instruments; OPT background plus independent selection principles; relativistic and gauge assumptions; finite particle representations and effective windows | These are explicit additional assumptions, even when the same abstract objects occur in Core. |
| L4: conditional derivation | Quantum representation within the selected sector; finite purification and local tomography; actual response and error theorems; specified anomaly and spectral arithmetic | Valid within the stated quantifiers. Neither an unlimited continuum theory nor a uniquely selected natural theory follows. |
| L5: model and computation | Exact rational witnesses, numerical regression, fixed-seed synthetic sampling, finite lattice and field-theory benchmarks | They test model calculation and software contracts; no new hardware observations are supplied. |
| L6: additional testable hypotheses | Candidate actualization channel, activation rule, noise law, 331 matter/threshold assumptions, selected framing completion | A hypothesis must fix observables and parameters sufficiently to differ from calibrated alternatives. Presently several mechanism-selection obligations remain open. |
| L7: empirical standing | Existing observations interpreted through explicit measurement and nuisance models; proposed QDRR and related tests | Agreement with ordinary quantum theory cannot uniquely confirm UEOT. Excluding classical random phases does not exclude a quantum environment or establish objective collapse. |

A complete chapter/result view is in `PHYSICS_CLAIM_SOURCE_MATRIX.md`, derived from the existing dossier. It introduces no independent truth database.

## 3. Priority findings and exact remedies

| ID | Location | Finding | Required remedy |
|---|---|---|---|
| A-01 | §1.2 | “复杂 Hilbert” is a mistranslation of complex Hilbert. | Use “复 Hilbert”. |
| A-02 | §15.1 | The algebra commuting with a permutation representation is generally noncommutative. Calling it “交换代数” obscures the multiplicity spaces. | Use “交换子代数” and explicitly state the form `⊕λ I_{Vλ}⊗Aλ`, with generally noncommuting operators on `Mλ`. The displayed representation decomposition itself need not change. |
| A-03 | §35.3; §47.14; Appendix F.2 and inherited “本轮” statements | Historical acceptance can be mistaken for a new publication-time execution. | Bind execution statements to their historical version and actual receipt. Reuse is legitimate only after exact source/dependency identity is checked. Do not claim the publication turn re-executed them. |
| A-04 | §48.2 YAML | `chapter_range: [0, 56]` conflicts with Chapters 0–65. | Change to `[0, 65]`; this is publication metadata, not a mathematical migration. |
| A-05 | §50.3 | The assertion that trace-distance identification and zero-distance separation remain unformalized is superseded by Chapters 60 and 63. | Describe the original §50 interface historically; point to `effectDistance_eq_zero_iff_density_eq` and `effectDistance_eq_half_traceAbsolute`. Distinguish these mathematical facts from whether a Lean `MetricSpace` instance is registered. |
| A-06 | Appendix A.5 | The distance-symbol summary points only to the earlier §50 limitations. | Add Chapters 60 and 63 as the actual separation and half-trace-absolute-value identification. Preserve the distinction from diamond distance. |
| A-07 | §64.1 | “反向定理” is the wrong direction for obtaining a vector from full convex purity; §61.3 explicitly uses “反向” for vector ⇒ pure. | State “由 P-PUC-01 从完整凸极点到归一向量表示的方向”. |
| A-08 | §§57, 58, 61, 62 and other historical scope descriptions | A responsibility closed by a later chapter must not remain presented as a current open obligation. | Use “本章原有范围” plus the precise later chapter; retain historical receipts. Do not rewrite earlier theorem quantifiers. |

Exact old/replacement snippets are supplied separately in `THEORY_EDITORIAL_CORRECTIONS.md`. Findings A-02 and A-07 are mathematical wording corrections; none changes a formula, stable ID, kernel theorem or experimental datum.

## 4. High-risk mathematical and physical checks

### 4.1 Complex quantum structure and Born probabilities

The generic Core-to-quantum implication is not established. Chapter 1 gives a classical realization, Chapters 54–55 strengthen the separation with complete classical state spaces and real-local-tomography counterexamples, and Chapters 57, 60–64 verify properties inside an already selected complex quantum model. Those internal results do not reverse the dependency chain.

Chapter 2 cites Kenji Nakahira’s *Two Operational Principles Single Out Quantum Theory*, arXiv:2605.23217, as an external preprint theorem. The original abstract, main theorem and Appendix A framework were checked. The result uses the complete finite causal OPT background and its precise channel-identification and equivalent-system-purification principles. It is not a two-line derivation from generic UEOT Core, is not a theorem newly established by this kernel, and does not require physical systems of every positive integer dimension. The earlier CDP reconstruction uses its own complete axiom package. Purification existence alone does not substitute for essential uniqueness and the remaining background.

Born probabilities arise through explicitly selected effects and density states, or through the hypotheses of the cited representation/reconstruction theorem. Gleason’s original result is dimension-sensitive and does not by itself choose complex over real Hilbert space; effect-based results use an enlarged measurement domain. Finite phase tomography reconstructs entries in a selected model, not the Born rule for every possible state and effect. The martingale argument in Chapter 3 yields Born weights only with bounded martingale dynamics and an eventual one-hot limit. Chapter 40 supplies such a limit for its specified finite QND stochastic model, without deriving the noise mechanism or activation rule from Core.

Primary sources checked for this scope: [Nakahira v1](https://arxiv.org/abs/2605.23217), [full theorem background](https://arxiv.org/html/2605.23217v1), [Chiribella–D’Ariano–Perinotti 2011](https://arxiv.org/abs/1011.6451), [Busch 2003](https://arxiv.org/abs/quant-ph/9909073), and [Gleason bibliographic record](https://iumj.org/article/1128/cite/). These sources support attribution and theorem scope, not experimental confirmation of UEOT.

### 4.2 States, instruments, channels, and metrics

The input-first, unnormalized Choi convention in Chapter 4 is coherent with the reconstruction and partial-trace formulas. Complete positivity has its actual ancillary quantifier; positivity on a single tested state is insufficient. The text correctly distinguishes a POVM’s outcome probabilities from an instrument’s postmeasurement action. Branch-wise intertwining is required for conditional protocol transport; equality of the unlabelled channel or POVM alone is insufficient.

Chapters 50 and 60 construct and separate the original full-effect distance. Chapter 63 proves the equality with half the trace of the matrix absolute value and constructs an actual positive-spectral effect attaining it. The zero-trace step is essential; its one-dimensional counterexample correctly rejects the same factor for an arbitrary unnormalized Hermitian difference. The PSD support certificate checks positivity, an actual difference decomposition and support identities, rather than accepting the final bound as an input. Equal-prior binary discrimination is the exact proved scope; an unequal-prior extension needs its nonzero-trace argument.

Channels in Chapters 58, 61–62 and 65 are genuinely rectangular, not falsely square unitaries. Arbitrary finite ancillary complete positivity does not turn the unstabilized channel defect into the diamond norm. Full labelled joint states are necessary for record error; the equal-unlabelled-channel counterexamples preserve quantum memory while changing records.

### 4.3 Purification and tensor-product responsibility

The manuscript distinguishes full convex purity from an ad hoc restriction to vector states. Chapter 57 proves normalized vectors are extreme points and derives a Gram purification from positivity. Chapter 61 obtains the converse using a positive-mass Gram column and treats zero residual mass separately. Same-ancilla purification equivalence uses an actual support isometry extended in finite dimension; both unitary identities are concluded, not assumed. With vectorization `ψ(i,a)=Aia`, the correct auxiliary action is `B=A Uᵀ`. The negative controls compare joint densities and therefore do not mistake a global phase for a physical difference.

Chapter 64 derives the minimum auxiliary dimension from the actual complex matrix rank, proves attainment through exact nonzero spectral support, and requires the correct dimension direction for a full-space isometry. A one-dimensional auxiliary space is not an empty, zero-dimensional carrier. Tiny nonzero eigenvalues cannot be discarded without an additional approximation contract. These are standard finite-dimensional quantum structures verified in the project’s chosen interface, not new physical principles.

Complex local tomography in Chapter 60 covers arbitrary joint matrices/densities through the real and imaginary matrix units; it does not assume that the state is separable. The real two-rebit counterexample uses all real local effects and is valid; allowing a complex Pauli-Y effect removes that restricted-model blindness.

### 4.4 Measurement, reversibility, and candidate actualization

A coherent write is an isometry with a specified environment. Recovering global coherence requires access to and reversal of the relevant degrees of freedom. A public algebra restricted to branch-diagonal observables is blind to certain coherences; it is not generally a commutative algebra, nor does blindness establish physical destruction of coherence.

The SRN classification by correlation/Gram matrices correctly requires every state within each branch to be unchanged. The exponential generator cone applies to continuous, time-homogeneous Schur semigroups. It does not justify a universal exponential collapse law in arbitrary non-Markov dynamics or deliberate coherence recovery. The three-branch cycle witness admits a classical Poisson counterexample. The four-branch witness excludes the specified classical random-phase class, yet has an ordinary quantum-environment dilation. Even a successful implementation therefore would not establish objective collapse.

The finite QND stochastic equation in Chapter 40 has a norm-preserving trajectory and a linear CPTP average. Absorption is asymptotic; finite-time posteriors remain positive under the stated filtering model. Its law is also a standard continuous-measurement law. Extending to position noise and heating introduces unbounded-operator/domain duties and cannot silently retain the finite QND absorption conclusion. The mechanism `K01`, actualization strength and record activation remain separate physical selection responsibilities.

### 4.5 Infinite-dimensional analysis, open systems, and field theory

The manuscript distinguishes finite matrices from normal trace-class states, algebraic QFT states, and type-III local algebras. Stone’s theorem requires a strongly continuous unitary group and self-adjoint generator; formal differential expressions do not settle domains. The Madelung calculation is local away from nodes and uses boundary conditions; the ring model exposes global phase and self-adjoint-boundary choices. Finite truncations cannot satisfy the exact canonical commutator, and a small initial-state tail does not by itself control a long-time dynamical error.

GKSL claims remain inside their semigroup and continuity assumptions. Davies limits require weak-coupling and reservoir hypotheses. CP divisibility is not the operational multi-time Markov condition; interventions and retained environmental memory matter. Gibbs stationarity or relative-entropy monotonicity is not a proof of thermalization, uniqueness or mixing. The finite Cesàro result proves a stationary subsequence/point, with an explicit nonmixing counterexample.

The QFT chapters display relativistic fields, gauge representations, interaction terms, regularization, renormalization scheme and effective-domain inputs. Their loop, Ward, optical-theorem and EFT calculations reproduce standard conditional results. A finite lattice Haar measure is a genuine finite model; a smooth-field plaquette expansion is not a nonperturbative four-dimensional continuum construction. Euclidean integration-out is not automatically a CPTP process map. Wilsonian RG, parameter beta functions and UEOT Object-RG have distinct domains and cannot be identified by shared terminology.

### 4.6 Generations, spectra, anomaly arithmetic, and finite windows

The conditional three-generation selector relies on its complete representation template, local anomaly equation, color restriction, family nonemptiness and declared effective weak-screening window. The selection is not an unconditional prediction from Core. The full SU(3)L ultraviolet classification explicitly admits the five-color/five-family alternative in the stated scalar range; this prevents replacing one window with another after the calculation. Local anomaly cancellation is not the same as global anomaly cancellation or a unique gauge group. A framing completion response is an additional specified mechanism, not a Betti-number derivation of the observed generations.

The FCNC identity and aggregate lower bound follow from the specified rank-one flavor structure. They do not fix individual meson observables without masses, mixing, matching, running and matrix elements. Illustrative CKM angles in the inherited program are frozen example inputs rather than a fresh fit. Quantum gravity and complete natural-theory selection remain research programs.

### 4.7 Finite adaptive and stopped protocols

Chapters 49, 58, 62 and 65 correctly distinguish all finite words, all finite adaptive trees, fixed depth, and bounded variable stopping. The history-reading channel physically dephases its history register. Its ability to accept any history–memory density as a mathematical input does not make it a coherent quantum controller.

In the per-action triangle decomposition, all block weights belong to the same chosen reference prefix state. No equality between the two implementations’ history distributions is assumed. The stopped extension uses actual identity Kraus operators, an injective leaf encoding, zero illegal branches and an isometric equality of joint states; idle costs vanish by an actual defect theorem. The survival-weighted budget needs a shared stopping rule and a uniform finite height bound. Almost-sure stopping alone does not discharge the unbounded-process responsibility.

## 5. Units and numerical certificates

The following dimensional conventions were inspected across their uses: `ℏ` has units of action; Hamiltonians have energy units; Lindblad generators have inverse-time units and their jump operators inverse-square-root-time units; position Fisher information has inverse-length-squared units; four-dimensional natural-unit fields have dimensions 1 for scalars/vectors and 3/2 for spinors; cross sections have inverse-energy-squared units. The bilinear heavy/light coupling and cubic heavy/light coupling carry different dimensions and are not interchangeable. Thermal beta, discount factors and the 331 charge-embedding parameter have separate names.

The inherited Python programs explicitly identify exact-rational identities, floating-point tolerances and synthetic sampling. The computed sample counts (such as 762 or ideal 188) follow their stated statistical models; they are not hardware guarantees. Sampled positive matrices and random phases are regression checks in addition to, not substitutes for, the analytic arguments. The original code should remain byte-for-byte stable in translation. This publication review does not report it as freshly executed.

## 6. Remaining OPEN obligations

1. A noncircular derivation of the complete complex quantum sector from generic frozen Core and independently justified physical selection conditions.
2. A full field-by-field connection to a cited reconstruction theorem if a stronger reconstruction claim is proposed; the seven-law presentation alone is insufficient.
3. A physical actualization kernel, its strength and its activation criterion, with independently constrained apparatus/environment nuisance terms and distinguishable predictions.
4. Continuum, unbounded-operator, infinite-rank and infinite-stopping extensions with their own analytic limits; current finite results cannot supply these by analogy.
5. General stabilized channel-error and coherent-control contracts beyond the current classical-history model.
6. Independent natural selection of particle content, gauge structure, family template, thresholds, EFT windows and any framing completion.
7. Certified numerical spectral algorithms and approximate-rank/purification resource bounds, if required; noncomputable exact existence theorems do not provide them.
8. Real experimental implementation, source data and appropriate model-comparison statistics. Existing finite examples supply no new empirical confirmation.

These are scientific obligations, not publication defects to conceal. The book can be released as a rigorous conditional and reconstructive framework while they remain open.

## 7. Acceptance recommendation

Proceed with the bilingual scientific edition after the listed wording/metadata corrections, exact formula and stable-ID checks, source-bound execution reuse, complete English coverage and integrated red-team review. Keep the scientific claim ledger and historical receipts authoritative. Attribute standard results explicitly; describe the project’s contributions in organization, conditional bridges, exact interfaces, counterexamples and formal verification at their actual scope. Do not label this review external peer review, do not infer completion from version numbers, and do not equate successful publication/build/CI with validation of nature.

## Publication-revision closure

The initial source-bound findings in this report were applied and re-read in the bilingual publication. `FINAL_THEORETICAL_RED_TEAM_REVIEW.md` and `theory_review_closure.json` record the complete extended English reading, the final precision repairs, and the frozen Chinese/English SHA-256 identities. All reported theoretical editorial findings are closed; the scientific OPEN obligations remain. No new heavy proof execution, PDF acceptance, remote publication or external peer review is claimed by this report.


## v31.10 / 双语出版3.7的最终增量

原66章审查保留为初始检查点。新增第66章全部16节、12结果及8个新Lean模块已独立读审；完整结论、推导与前提见 `CH66_THEORY_REVIEW.md`，新增ID来源见 `CH66_CLAIM_SOURCE_MATRIX.md`。总主张矩阵已扩至67章/173结果，原161行逐字不改。最终双稿中文 SHA256 `fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060`、英文 SHA256 `437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91`；理论红队最终闭环 PASS，范围及所有身份检查见 `FINAL_THEORETICAL_RED_TEAM_REVIEW.md` §9 和 `theory_review_closure.json`。无新的正文科学阻断；未验证物理机制及真实设备责任继续OPEN。此PASS不包含PDF、外部同行评议或GitHub新发布的验收。

## Edition3.8 / chapter67 increment

The source-to-output arrows are now specified in the same probe–oscillator model. P-OPT-02 has actual-map/statistics/Choi endpoints; P-OPT-03's complete finite-OPT/tree argument remains partly paper-level. CP composition assumes all persistent memory is in the state carrier or independently reset auxiliaries. P-MICRO-01 derives branch preservation from microscopic conservation, then full adaptive-CQ contraction; it does not assume the sought intertwining field. Normal trace-class postselection and selfadjoint block-direct-sum dynamics remain paper proofs. P-ROB-01 is a bound for a given legal simplex candidate, not an existence theorem for a low-residual policy. The exact design-region adaptive certificate is bound separately from a realized narrower calibration set. See the [nine-result bindings](../../audits/OPERATIONAL_MICRO_ROBUST_v31.11/chapter67_formal_bindings.json) and current source-matched receipts. Core is unchanged.
