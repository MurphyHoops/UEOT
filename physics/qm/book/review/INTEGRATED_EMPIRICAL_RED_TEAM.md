# Integrated bilingual empirical red-team review

## 1. Identity and decision boundary

**Reviewer:** agent B, empirical science, competing explanations, original literature, and falsifiability. **Review date:** 2026-11-11 UTC. This is an internal specialist review, not external peer review.

This review supplements `EMPIRICAL_AND_FALSIFIABILITY_AUDIT.md` and `PRIOR_ART_AND_EXPERIMENTAL_STATUS.md`; it does not replace the existing chapter dossier or create a new scientific claim ledger. The first-round review covered all 66 Chinese chapters and appendices A–F at main commit `3d443ec29eb17af1fc00699a74e2d42d73516d81`, book SHA-256 `b726e3b9033d79ef949b8e83469901fe728aa28ab204b2e4d55bf36a18b412f0`.

The integrated manuscripts supplied for this second review were read and hashed, then copied to the reviewer's isolated directory:

| Manuscript | SHA-256 | Bytes |
|---|---|---:|
| `physics/qm/book/UEOT_PHYSICS.md` | `6f78236da15f2669b9dad529aa2f873ae039ab63ca41dca108a2758034280837` | 666792 |
| `physics/qm/book/UEOT_PHYSICS.en.md` | `e8f8f18dc43c7b4c9e60dbc2c8c20809ab2caaff4f07e95fffc19b794816fb91` | 807184 |

**Decision at initial review:** the integrated empirical treatment is scientifically suitable subject to three narrow editorial clarifications below. No new defect was found in the reviewed experimental estimators, null-model boundaries, or primary-source additions. **All three clarifications were subsequently observed in the actual revised manuscripts and closed; see the hash-bound final decision in §6.** This report does not grant acceptance to unseen future edits. Mathematical completeness, full-book equation/ID matching, typeset PDF quality, and the publication PR are separate checks owned by the principal editor and the other reviewers.

## 2. Checks actually performed

The reviewer read the new bilingual §0.10–0.12 exposition, all 66 Chinese/English chapter opening guides, the integrated chapters 6, 8, 28, and 41, and the source-status additions C.7 and F.2. The bibliography C.3–C.6 was reread against the first-round source review. A full-book English search for claims of experimental confirmation, objective-collapse discovery, new laws, raw data, priority, and hardware execution was followed by contextual reading of the hits. This search is a supplementary check, not a substitute for the first-round whole-book audit.

For chapters 36–48, the integrated English text was compared directly with the reviewer's completed translations. The differences consist of the 13 new guides, the supplied §41.3 addition, chapter-anchor boundaries, and edition/bilingual metadata in chapter 48. The stochastic-integrand correction is present in the integrated chapter 40. No estimator, hypothesis, numerical threshold, counterexample, or empirical disclaimer disappeared during integration. The earlier translation receipt records 542 matched mathematical spans for these 13 chapters after three documented natural-language label translations; the final whole-book identity check remains the principal editor's responsibility.

| Area | Integrated finding |
|---|---|
| Seven evidence levels, §0.10 | Standard physics, Core, sector selection, conditional inference, computation, additional mechanism, and empirical standing are separated. Common mathematical objects do not become a proof across all levels. |
| Bell illustration, §0.11 | The ideal unitary inverse is correct. The operational distinction between reading a record into an external apparatus and reversing the closed two-qubit circuit needs the explicit clarification B-RT-01. |
| Record objectivity, ch.6 | A mutual-information plateau is not treated as sufficient accessible classical evidence. The strong-QD/SBS discussion retains full conditional factorization and cites the 2021 correction and reply. |
| QDRR, ch.8 | Tomography is restricted to a finite CPTP-SRN class. Completeness does not extend to leakage, population transfer, within-branch disturbance, or arbitrary history dependence. Controls, unstable division by near-zero hardware coherence, and the lack of new hardware data are stated. |
| Five laboratory studies, §8.5 | Physical quantum simulators are distinguished from Appendix D's synthetic computer output. Zhu's logical postselection does not certify an unconditional channel. Zheng's measured-window revival suppression does not imply fundamental irreversibility. Raw counts have not been jointly reanalyzed. |
| QED, ch.28 | The fixed inverse fine-structure constant is correctly attributed to CODATA 2018. The cross section retains approximation, units, perturbative order, and exclusions. No current precision prediction or independent UEOT constant is claimed. |
| Three-generation and flavor arguments, ch.36–37 | Model and threshold premises remain explicit, including the five-color counterexample. Rank-one flavor relations are possible candidate tests, not observed new particles or parameter-free discoveries. |
| Cycle phase and four-level witnesses, ch.38–39 | Different excluded noise classes remain distinct. Poisson classical phase noise survives the three-cycle test; a quantum environment realizes the four-level channel itself. Neither witness identifies fundamental collapse. |
| Stochastic model, ch.40 | The chosen SSE, finite QND absorption conditions, strength/activation obligations, and energy-cost relation remain separate. Boundedness is assigned to the stochastic integrand, not to the stochastic integral. |
| Collapse constraints, §41.3 | Three actual primary sources support model-specific limits. Conservative total-noise bounds are distinguished from residual-based limits and positive discovery. CSL parameters are not equated with undefined UEOT actualization strength. |
| Correlated-trial statistics, ch.46 | Conditional lower bounds apply at every history; a marginal average is insufficient. Calibration error is added, optional stopping is controlled by the stated process, and the ideal 188 trials are not advertised as a hardware guarantee. |
| Remote verification, C.7/F.2 | Historical local/reused proof receipts, later GitHub job metadata, source identity, and a new publication build are distinct events. The old remote-pending label is not promoted to present status. The principal editor verified the GitHub facts; agent B has not independently re-audited those remote runs. |
| Full set of chapter guides | The guides consistently identify selected models, approximation domains, conditional results, known theory, and open physical selection. The finite-kernel proofs are not presented as new experiments. |

## 3. Narrow revisions requested

### B-RT-01 — Make the Bell readout/reversal protocols distinct

**Location:** §0.11. **Priority:** required operational clarification. **Initial status:** sent to the principal editor; closure is recorded below only after observing the changed files.

The paragraph first mentions observers reading records and then inversely applies the two-qubit gates to return to the initial state. The equation is correct for the closed unitary circuit. A reader could otherwise infer that an actual measurement outcome has already been retained by an unmodeled external apparatus. In that experiment, reversing only the original two qubits does not erase the external branch information.

Insert after the inverse-return sentence:

**Chinese:** “这个反演协议没有先测量并把结果保留在外部装置中；若标签已经复制给外部读出器，该读出器也必须纳入逆操作，只控制 S、R 不再足够。”

**English:** “This reversal protocol does not first measure the record and retain the outcome in an external apparatus. If the label has been copied to an external reader, that reader must also be included in the inverse; control of S and R alone is no longer sufficient.”

For the following Chinese phrase about subtracting errors and omitted environments, prefer “独立校准、控制或保守界定普通门误差、泄漏与未受控环境”. An unknown omitted environment is not a known scalar correction that may simply be subtracted. The integrated English “account for” already avoids the strongest reading.

### B-RT-02 — Do not imply that hardware-experiment receipts already exist

**Location:** §0.5, historical-evidence paragraph. **Priority:** evidence wording. **Initial status:** sent to the principal editor.

Replace the sentence “Subsequent kernel results, exact certificates, and actual experiments have their own source manifests, execution logs, and audit receipts.” The Chinese source similarly groups “实际实验” with established project receipts. Elsewhere the book correctly states that no new project hardware experiment has been executed.

**Chinese replacement:** “后续内核与精确证书的状态，由对应版本的源清单、执行日志和审计回执给出。外部实验证据须追溯到原始论文与数据说明；本项目未来硬件实验另需真实采集与校准记录。”

**English replacement:** “Subsequent kernel results and exact certificates have their own source manifests, execution logs, and audit receipts. External experimental evidence must be traced to its original papers and data descriptions; any future hardware experiment by the project will require its own acquisition and calibration records.”

### B-RT-03 — Label the energy/decoherence work as a model and protocol

**Location:** §0.4 status table, identification-of-new-physics row. **Priority:** evidence wording. **Initial status:** sent to the principal editor.

Change “能量与退相干联测” to “能量与退相干联测的模型关系与方案”, and “joint energy/decoherence measurements” to “model relations and protocols for joint energy/decoherence tests”. The same row already says there is no new real experiment; the revised cell makes the established-position field consistent with that statement.

### Publication-only dependency

C.7 says that both PDF builds have receipts under `evidence/v3.6/`. At the time this review began, the principal editor stated that PDF construction had not yet run. This sentence can be accepted in the released book only after both builds actually complete and their receipts exist. It is not evidence that the reviewer has inspected PDFs. This review neither substitutes for visual inspection nor asks for an unnecessary rerun of unchanged heavy Lean work.

## 4. Primary-source and numerical evidence retained

The source-review depth, data-access limits, dates, and further references are in `PRIOR_ART_AND_EXPERIMENTAL_STATUS.md`. In particular:

- The objectivity discussion uses [Le and Olaya-Castro 2018](https://doi.org/10.1103/PhysRevA.98.032103), the [2019 strong-QD paper](https://doi.org/10.1103/PhysRevLett.122.010403), and the [2021 comment](https://doi.org/10.1103/PhysRevLett.126.188901) and [reply](https://doi.org/10.1103/PhysRevLett.126.188902). These sources support the distinction between total correlations, accessible records, and the necessary independence condition.
- The five cited laboratory studies are [Ciampini 2018](https://doi.org/10.1103/PhysRevA.98.020101), [Chen 2019](https://doi.org/10.1016/j.scib.2019.03.032), [Unden 2019](https://doi.org/10.1103/PhysRevLett.123.140402), [Zhu 2025](https://doi.org/10.1126/sciadv.adx6857), and [Zheng 2026](https://doi.org/10.1103/t2yx-9bqh). The book does not extract a new actualization-rate limit from these papers.
- The collapse-constraint paragraph uses exactly [Vinante 2016](https://doi.org/10.1103/PhysRevLett.116.090402), [Donadi 2021](https://doi.org/10.1038/s41567-020-1008-4), and [Altamura 2025](https://doi.org/10.1103/PhysRevA.111.L020203). No numerical limit is imported without model conversion. The separate Majorana result's erratum is identified in the source audit; no uncorrected bound from that paper is inserted.
- Pollock's process-tensor framework title and DOI are correctly repaired, and remain distinct from the operational-Markov paper. The CODATA citation preserves the benchmark's 2018 identity.

The locally executed arithmetic check is reproducible with `empirical_number_check.py`. The receipt `EMPIRICAL_NUMBER_CHECK.json` records eight passing checks at `2026-11-11T05:28:42.744455+00:00`. Script SHA-256: `b9b958b9f94cd23543567732e78f8ddd73195fe60c31ce5086135792d21ba953`. Receipt SHA-256: `5edfb0f65cfcfc125e6cb43461e5d7a25999ef9ee819a9c15878bb953541389f`.

These checks confirm 762 samples per setting for the stated simultaneous Hoeffding bound and the ideal lower bound `p*=0.0158446719248555…`. Zero accepted events in 187 ideal trials do not reach 5%, whereas zero accepted events in 188 trials do. The strict conservative pointer-error threshold is `ell < p*²/8 = 0.000031381703550788…` when the SPAM allowance is zero. This is a sufficiency threshold for the bound, not a universal impossibility limit for hardware. The count 188 excludes calibration and is not a valid guarantee when the required conditional null or calibration contract fails. No experimental observation follows from this arithmetic.

## 5. Scientific questions that remain OPEN

The publication revision cannot resolve the physical origin of an actualization generator, its strength, `K_01`, or an objective-record activation law. A freely fitted loss coefficient is not a mechanism. The expression `q=exp(-xi Lambda)` is absent from the bound book and is not certified as a universal law; future use would need its own generator, units, and domain, particularly when coherence revives.

The edition contains no new UEOT hardware dataset, no completed QDRR detection, and no new particle discovery. Full environmental dilation remains a competing standard-QM explanation for unrestricted finite CPTP system statistics. A hypothesis may be falsifiable only after its model family, independently constrained nuisance processes, protocol, shared parameters, estimator, and failure conditions are fixed. If the family permits zero additional strength without a positive lower bound, a null result constrains parameters without rejecting the whole family.

The conditional generation result does not establish general uniqueness of the observed spectrum; the five-color countermodel remains. The finite kernel does not uniquely select complex quantum theory from generic Core. Known QFT/RG/EFT calculations and finite-lattice consistency do not supply new independent physical constants, construct general continuum interacting QFT, or close quantum gravity. These OPEN states are scientific conclusions of the audit, not publication defects to be hidden by stronger wording.

## 6. Closure record

**Observed closure:** 2026-11-11T05:39:29.987724+00:00. The reviewer independently reread the changed manuscript bytes and the substantive differences from the initial reviewed snapshots. The files were copied into the isolated review directory before computing this closure identity:

| Revised manuscript | SHA-256 | Bytes |
|---|---|---:|
| `physics/qm/book/UEOT_PHYSICS.md` | `23a1f13750ca4f7fb69eaec3cab8cc541ea69b23e339413ece06f737817811fd` | 667316 |
| `physics/qm/book/UEOT_PHYSICS.en.md` | `bf9f4c75541360d73809d269e122a925745de8e0caaf5dd36c7da9e5d337b0b1` | 807971 |

| Finding | Observed resolution | Status |
|---|---|---|
| B-RT-01 | Both languages now state the actual gate order and explain that a retained external record must also be reversed. The Chinese paragraph now requires independent calibration, control, or conservative bounds for ordinary errors and uncontrolled environments. | CLOSED |
| B-RT-02 | Both languages separate kernel/certificate receipts from cited external evidence and any future project hardware-acquisition records. | CLOSED |
| B-RT-03 | Both languages label joint energy/decoherence work as model relations and test protocols. | CLOSED |

Concurrent theory/language repairs were also inspected in the actual text differences: the finite-error reference trajectory is defined; SRN pointer projectors are complete and nonzero; the ring gauge statement retains its constant-potential representation; the English beta-coefficient wording names `b_2`; a joint effect's positivity is not called channel complete positivity; the tensor-unit ancilla is distinguished from a zero-dimensional carrier; 188 is stated as trials with zero accepted events; and the audit paragraph explains rejection of an assertion that a checker returned true rather than speaking ambiguously of a “false proof”. These changes introduce no strengthened empirical claim. Heading case and usage changes do not affect the evidence interpretation.

**Final empirical red-team decision: PASS within the recorded scope.** All three requested evidence/operation clarifications are closed on the above identities. No unresolved empirical wording blocker was found in the reviewed integrated manuscript. The OPEN physical questions in §5 remain OPEN. This decision does not certify new experimental data, external peer review, unseen subsequent edits, PDF appearance, or completion of a GitHub publication. The principal editor must separately bind actual publication-build and delivery receipts; the empirical reviewer has not inspected PDFs or rerun the heavy proof suite.

### 6.1 Final text delta and refreshed closure identity

At `2026-11-11T05:44:08.996399+00:00`, the reviewer read and copied the final text supplied by the principal editor, independently verified both requested hashes, and reviewed the changes from the preceding closure snapshots. **The empirical PASS and all three CLOSED findings extend to these final text identities:**

| Final manuscript | SHA-256 | Bytes |
|---|---|---:|
| `physics/qm/book/UEOT_PHYSICS.md` | `8e8183c9e10df1d36b303182a10cfdb515a74c95e8c04709445f0145b9b7a5dd` | 667720 |
| `physics/qm/book/UEOT_PHYSICS.en.md` | `30f025eeeff0aa3cea0e87dca3b04eb8f3e90d17b4ae42efcca7e154371b1dfb` | 808503 |

The final delta clarifies equal-mode versus unequal-mode symplectic forms in Gaussian-channel complete positivity, replaces an unintended process-tensor “CP separability” label with complete positivity, names the low-energy coefficient `b_2`, correctly describes the three classical/real/complex operational presentations and the horizontal representation `R`, distinguishes probability mixtures from long-time averages, and limits the many-body computational statement to the guarantee this book actually supplies. English spelling changes retain the same content. The complete/nonzero projector, constant-potential gauge, and tensor-unit qualifications were already inspected in the preceding closure. None of these changes adds an experimental result, changes an empirical estimator, removes a competing explanation, or closes an unresolved mechanism. This text-delta acceptance remains separate from the subsequent PDF visual review.
