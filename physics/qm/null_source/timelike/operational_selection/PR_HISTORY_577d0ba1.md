## Current result — exact nonlinear histories and remaining physical selection

The preceding full spectrum and exact incoming state construction still lacked a compatible nonlinear RSET map. This increment closes that gap and constructs an **exact nonlinear mean-SCE history family**, with an explicit contraction domain and same-amplitude error bound. It then uses the actual family to resolve the next selection questions.

- Current HEAD: **577d0ba1df5b70ebfe3b14aee361223dd0ab46b8**
- Main research commit: **a20df9b74a75c02c11164da9368d483e59efd62f**
- Branch: codex/physics-source-response-20261119
- PR remains **OPEN DRAFT**. No merge. Core read-only; GI excluded.
- [Research entry](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/README.md)
- [All-order kernels and complete fixed-AE nonlinear map](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/KERNELS.md)
- [Exact existence, positive window, and error theorem](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/EXISTENCE.md)
- [Exact nonuniqueness, source obstruction, and record contract](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/SELECTION.md)
- [Review and evidence boundaries](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/REVIEW.md)

### What is now closed

1. **Complete same-radius nonlinear map.** The exact product W=F+F− obeys a third-order covariance equation. Its first two Born orders yield explicit renormalized linear and bilinear kernels; all higher orders form an absolutely summable tail, including the previously easy-to-miss h*W2 term. The required frequency growth is four derivatives plus a logarithm. The old seven-derivative WKB bound is not imported into an incompatible inverse domain.
2. **Original physical prescription preserved.** The temporary omega=sqrt(k²−1) subtraction is converted exactly back to the original AE k subtraction by finite local constants. All k=1 subtraction terms, dynamic logarithms, fixed contacts, actual canonical zero modes, original M2/U0, and both complete thermal shells remain. The new full DS(0) is symbolically identical to the frozen P(lambda) at every positive frequency, including the reference-zero correction K1=Z+1.
3. **Full E4 inverse.** The frozen positive factor supplies an all-frequency logarithmic lower bound, while the prior all-combination inverse handles the remaining finite range. The inverse from the degree-at-least-two Wiener algebra to E4 has norm below 2e20. The original graph domain and E4 correction space are proved equivalent; both linear amplitudes remain in the solution.
4. **Exact same-incoming-state histories.** A quantified Banach contraction constructs a real analytic two-amplitude family. The full Ward identity and the fixed static past give every homogeneous mean Einstein constraint. On the selected strictly interior positive window, all mean equation defects and actual normal derivatives vanish identically. The construction preserves the original Q/P, eta_ref, full S0 law and thermal occupations; finite-slice covariance is transported with each geometry.
5. **Actual error control.** For the same two amplitudes within the certified ball, the E4 distance from a trial history to the exact history is bounded by 2.3e20 times its full coefficient-space spatial residual. A convergent all-order Picard construction has an explicit geometric error bound.
6. **Reflection followed by further closure.** Fixing the nonzero slow amplitude and the entire incoming contract still leaves distinct exact fast-amplitude histories. They share the first 468087 integer slow-growth orders. Randomizing these amplitudes alone cannot absorb a nondegenerate sampled zero-mode source while retaining the same static A. A new exact purity counterexample also makes explicit why arbitrary nonlinear symmetry-invariant selection is outside the established linear-CP record-equivalence theorem.

### Certified quantitative exit

Let E4 have weight (1+lambda)^4 log(e+lambda), on the bidisc coefficient algebra.

| Quantity | Certified bound / enclosure |
|---|---|
| Same-radius holomorphic geometry ball | norm(u)_E4 <= 0.1 |
| Actual full spatial equation ball bound | <2.733711604346733; chosen majorant 4 |
| Complete E4 coefficient inverse | <2e20 |
| D²S bound on the half ball | 6400 |
| Exact construction total radius rho | 1e−25 |
| Linear-seed / correction budget | rho/2 each |
| Contraction factor | <=0.128 |
| Self-map bound | <=0.064 rho |
| Picard error after j steps, from zero | <=(2 rho/109)*(0.128)^j |
| Normalized bidisc radii (Rz,Rw) | (1e−28,1e−51) |
| Normalized seed E4 norm | <2.312802292403160e−26 |
| Exact correction E4 norm | <3.925911518345183e−28 |
| Same-amplitude residual-to-solution gain | <2.293577981651377e20 |
| Positive conformal window T=1/sigma_F | [1.068176718681417e−6,1.068177225049064e−6] |
| Proper duration | [0.08729645277351678,0.08729645285527776], model units |

The example sets epsilon=Rz/(2 exp(s/sigma_F)) and delta=Rw/(2e); the endpoint lies at half of each radius. Both past and positive window therefore lie strictly inside the analytic bidisc. These very small amplitudes are conservative sufficient conditions, not physical amplitude limits or experimental sensitivity. They **do not cover the old z<=1e−4 seed window**.

### Exact-HEAD verification

- Local: **5/5 new checks PASS**.
- Reused **80 predecessor results**, with **293 inherited scientific files byte-identical**.
- Old scientific checker executions: **0**. Mode/geometry ODE integrations: **0**.
- Final science CI [44704352616 — SUCCESS](https://github.com/MurphyHoops/UEOT/actions/runs/44704352616), exactly bound to **577d0ba1df5b70ebfe3b14aee361223dd0ab46b8**.
- Decoded job [136180116890](https://github.com/MurphyHoops/UEOT/actions/runs/44704352616/job/136180116890) independently confirms final checkout, all five PASS lines, and the 80/293 reuse gate.
- Artifact nonlinear-history-research: ID **14614182168**, 24561 bytes.
- Artifact SHA-256: **e10152ac112ffa88c3fd0abe2a2fead0314d8376f1e998201ece97c7a3bc697c**; matches the decoded upload log.
- [Local receipt](https://github.com/MurphyHoops/UEOT/blob/577d0ba1df5b70ebfe3b14aee361223dd0ab46b8/physics/qm/null_source/timelike/nonlinear_history/verification.json) records the actual precommit a20df9b7 HEAD and dirty state. It does not pretend to have run locally on the future final commit; exact-final-HEAD CI is separate evidence.
- Main research commit a20df9b7 also passed science CI [44703678670](https://github.com/MurphyHoops/UEOT/actions/runs/44703678670).
- Final publication [44704352540 — SUCCESS](https://github.com/MurphyHoops/UEOT/actions/runs/44704352540) is now fully complete on the exact final HEAD: manuscript, Chinese PDF, and English PDF all PASS. This final observation supersedes the earlier in-progress status.
- Frozen baseline a01fd663 science **44693131877** and publication **44693131858** both succeeded; the formerly pending Chinese PDF is now confirmed successful.
- Read-only GitHub compare confirms **19 new research files plus four route/workflow updates** across the two commits, without changing any inherited scientific file. The existing worktree/branch is clean.

### Independent native-agent review

All three native agents independently reviewed the actual main research commit a20df9b7 through read-only GitHub. They then read the complete nine-file clarification delta to final HEAD **577d0ba1df5b70ebfe3b14aee361223dd0ab46b8** and confirmed **no remaining blocking issue**.

- A: exact product map, high-Born summability, full AE norm bound, explicit contraction and strictly interior same-state window.
- B: low-Born kernels, exact finite subtraction conversion, full response-symbol match, logarithmic inverse, and the immutable 80-result/293-file proof chain.
- C: red-team review of graph/analytic domains, Ward constraints, Q/P and eta_ref transport, exact nonuniqueness, sampled-source scope and the complete record contract.

The final clarification implements A's normal-derivative terminology correction and the root/C record-scope finding. The new exact matrix witness confirms that diag(1,0) and I/2 have the same O(2) twirl but purities 1 and 1/2. Thus delta(rho)=c Tr(rho²) is group invariant but is not a common affine record rule or a function only of twirled data. This witness is not identified with the current matter preparations.

Root alone wrote and executed the authorized Mac worktree. Agents used only read-only GitHub/literature and mathematical reasoning. This is AI-assisted research review, not external human peer review or a new machine-formalized proof.

### Physical scope and next gate

The result is an exact local **mean-SCE** theorem for the fixed two-field closed-S3 model and incoming contract. It does not select a fluctuating gravity law or claim physical unification.

- Same incoming preparation is not the same finite-slice density operator on different geometries. The latter is synchronized with each geometry by exact transport.
- Full Hadamard control is on strictly interior bidiscs; the E4 boundary is not automatically smooth to every order.
- Uniqueness is for fixed two amplitudes within the certified analytic ball. The exact family now proves that the currently supplied past/slow conditions do not select the remaining fast amplitude.
- A sampled source shift delta_M produces past defects C=-delta_M/(3A²), S=delta_M/(2A⁴). Growing amplitudes that vanish in the past cannot remove these constants. This excludes that explicit fixed-A sampling proposal, not every possible quantum geometry.
- Full-record equivalence retains its original **linear CP, outcome-by-outcome covariance and common-record control** contract. Nonlinear mean selection separately requires common closed quotient data and the same selection rule; covariance alone is insufficient.
- Next: supply an independently justified physical preparation/selection rule, construct source–geometry joint constrained data for the complete source law in a specified fluctuation model, then include actual controller/probe/clock total stress, cross noise, all records and calibration.
- Old/new preparations may not be assigned different fast amplitudes and have that extra input counted as the original noise-reduction effect. Core-derived physical selection, complete fluctuations, a realizable gravity instrument, and empirical discrimination remain OPEN.

---

<details>
<summary>Archived predecessor record — exact earlier HEADs and observations retained</summary>

## Current result — full spectrum, legal state family, and retained-mode inverses

The preceding controlled same-state window left a precise gap: a small residual did not establish a nearby exact nonlinear common history. This increment closes the missing **full linear spectrum and inverse/state construction** gates, and identifies the remaining nonlinear mapping problem without changing the matter, incoming state, or fixed AE prescription.

- Current HEAD: **a01fd663eba988029cb6193c176489ad5bcab539**
- Branch: codex/physics-source-response-20261119
- PR remains **OPEN DRAFT**. No merge. Core read-only; GI excluded.
- [Current research entry](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/README.md)
- [Complete spectrum and certified fast root](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/SPECTRUM.md)
- [Canonical state matching and exact incoming state family](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/STATE_MATCHING.md)
- [Causal inverse and two-amplitude coefficient inverse](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/INVERSE.md)
- [Reflection, scope, and next gate](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/REVIEW.md)

### What this increment closes

1. **Complete spectrum.** Positive pole residues and a second divided difference prove that the full meromorphic response has exactly two simple positive roots in the open right half s-plane, with no nonreal right-half-plane roots. Negative y roots interlace the negative real poles. An independent finite-truncation/Hurwitz proof agrees.
2. **Certified fast root and residue.** Positive Laplace-weight tail bounds and exact cancellation of correlated log(x) terms enclose the fast root for the entire inherited parameter box. Every fixed AE contact and the actual thermal response is retained.
3. **Actual state and constraints.** The fast mode transports the same incoming state, has zero complete linear Hamiltonian defect, and changes curvature. It is not a gauge mode. Freezing actual slice covariance while changing geometric jets generally violates the new geometry's UV contract. In the current pure-high-mode/finite-thermal-shell class, the frozen covariance remains Hadamard iff all V=a''/a jets match.
4. **Strictly causal finite-start inverse.** A positive-real factor produces a C1 Green function retaining both growing poles, with explicit short-window gains. Smooth zero-past forcing yields a smooth geometry response and synchronized legal state transport.
5. **All nonlinear combination frequencies.** The fast/slow ratio is noninteger throughout its certified box. Every frequency n*s_*+m*sigma_F with n,m>=0 and n+m>=2 has a uniform nonzero divisor. A bounded coefficient inverse in a bidisc graph domain retains both free linear amplitudes and controls four time derivatives.
6. **Exact incoming state construction.** For u_00=0 and Theta^2*u in the bidisc Wiener algebra, V has zero constant coefficient and finite norm. Each Jost iteration increases positive frequency; the operator powers have a 1/j! bound. Exact modes therefore exist uniquely for arbitrary finite norm(V), without a small-potential assumption. Wronskian, original Q/P, unchanged eta_ref, full source spectrum, and thermal occupations are preserved. Hadamard control is proved on strictly interior bidiscs.

### New certified quantitative exit

| Quantity | Certified enclosure / bound |
|---|---|
| Fast proper growth rate sigma_F/A | [11.45521916747093, 11.45521917819977], model units |
| Fast conformal rate sigma_F | [936174.2382721817, 936174.6820642408] |
| sigma_F/s_* | [468087.11913820513, 468087.34103423485] |
| P'(sigma_F)/A | [-29.25644683084921, -29.256405137459613] |
| A times residue of 1/P at sigma_F | [-0.03418054936351732, -0.034180500652784614] |
| Finite-start conformal window T=1/(24A) | [5.098416013977445e-7, 5.098418426099144e-7] |
| sup(w) / sup(test residual) on that window | <4.20e-14 |
| sup(w') / sup(test residual) | <1.30e-7 |
| Every total-degree >=2 pure/mixed response divisor | abs(P)>11.99 |
| Corresponding four-time-derivative coefficient inverse norm | <1.73e18 |
| Example exact off-shell Jost family u=z+w | norm(V)<0.051; norm(F)<1.007302 |

The proper duration 1/24 belongs to the static background. Perturbed proper duration has the explicit exp(±norm(u)) bounds. These are model units, not seconds or experimental sensitivity.

### Exact-HEAD verification

- Local: **6/6 new checks PASS**.
- Reused **74 predecessor results** with **272 inherited scientific files byte-identical**.
- Old scientific checker executions: **0**. Mode/geometry ODE integrations: **0**.
- Final science CI [44693131877 — SUCCESS](https://github.com/MurphyHoops/UEOT/actions/runs/44693131877).
- Decoded job [136143466953](https://github.com/MurphyHoops/UEOT/actions/runs/44693131877/job/136143466953) independently confirms final HEAD, all six PASS lines, and the 74/272 reuse gate.
- Artifact dynamic-inverse-research: ID **14609088446**, 23967 bytes.
- Artifact SHA-256: **09084ff6506dc6262d5734a5cc537b28f72c520853b3597525f91ae50e0e3068**; matches the decoded upload log.
- [Local receipt](https://github.com/MurphyHoops/UEOT/blob/a01fd663eba988029cb6193c176489ad5bcab539/physics/qm/null_source/timelike/dynamic_inverse/verification.json) keeps the actual precommit 46f8f53b HEAD and dirty status. Final-HEAD CI is separate committed evidence.
- The main research commit 46f8f53b also passed science CI [44692650083](https://github.com/MurphyHoops/UEOT/actions/runs/44692650083).
- Final publication [44693131858](https://github.com/MurphyHoops/UEOT/actions/runs/44693131858): **IN PROGRESS** at the final observation; manuscript and English PDF PASS, Chinese PDF still running. This is not reported as completed publication success.
- Frozen baseline 119387a3 science **44679853647** and publication **44679853680** both succeeded.
- Read-only GitHub compare confirms two commits, **21 new research files plus four route/workflow updates**, and no inherited scientific file changes. The existing branch/worktree is clean; no merge.

### Review and limitations

All three native research agents independently read the main research commit **46f8f53b9b269129f40923ff72681aa9474c57e2** and found no blocking issue. They then reviewed the final five-file clarification/receipt delta to **a01fd663eba988029cb6193c176489ad5bcab539** and confirmed the prior conclusions carry forward. The two nonblocking wording suggestions were implemented: the witness explicitly has J!=0, and the complete Jost Wiener algebra is distinguished from the total-degree>=2 correction space.

A reviewed the full spectrum, Bromwich and analytic graph domains, mixed-frequency inverse, and exact state construction. B reviewed interval directions, stable response formulas, all-frequency bounds, and the immutable source/CI/hash chain. C reviewed canonical covariance identification, UV matching, factorial state construction, zero-mode reference, and constraints.

Root alone wrote and executed the authorized Mac worktree; the three agents used only read-only GitHub/literature/mathematical review. This is AI-assisted review, not external human peer review or a new machine-formalized theorem.

The counterexample a_new=A*exp(J*eta^3/6) uses **J nonzero**. Finite stress sums at its initial slice do not make the frozen state Hadamard.

The two inverse domains are explicit:

- The causal Green function solves a finite-start, smooth zero-past problem. From minus infinity it generally cannot be convolved directly with the old slow residual, because the retained fast pole grows faster. It does not certify an exact correction on the old eta in [0,1] window.
- The bidisc inverse is an isomorphism on the **graph domain**, not on the entire bare four-derivative Wiener space. The symbol also has logarithmic high-frequency growth.
- Exact incoming modes and interior Hadamard control do not yet bound the fully renormalized nonlinear RSET at the same radius.
- The nonlinear exact common-history family, its error control, and independent physical selection of geometric amplitudes remain OPEN. No nonlinear no-solution or nonuniqueness theorem is asserted.

### Reflection completed and next scientific gate

The next construction retains **both** slow and fast amplitudes. It does not silently impose single-variable analyticity, future boundedness, or order reduction to remove the fast mode.

Prove that the complete AE local terms and the exact same-state infinite-mode RSET form a closed nonlinear map in a compatible graph/weighted/analytic-radius domain, with quadratic or Lipschitz remainder bounds. The old WKB tail estimates use higher geometric derivatives; they cannot simply be paired with the present four-derivative inverse. A concrete route is to bound renormalized multi-input kernels using the exact positive-frequency Jost resolvents, with any radius loss explicit.

Only after that gate can the inverse support an exact common-history existence/error theorem. Then address full source fluctuations, joint constrained data, local preparation and probes/clocks with total device stress, cross correlations, all CP records, and calibration.

The inherited O(2) full-record equivalence remains in force for the same full joint twirl and a common covariant selection/instrument. Giving old/new preparations different fast-mode amplitudes changes the geometric input and cannot be counted as a consequence of the original noise reduction. The overall physical-unification goal and empirical status remain OPEN.

---

<details>
<summary>Archived predecessor record — exact prior HEAD and observations retained below</summary>

## Current result — controlled same-state dynamic window

The previous exact static histories and correlated static residual bounds left a concrete gap: a geometry perturbation must transport the **same actual quantum state**, retain every fixed AE term, and control the full equations on a positive time window.

This increment closes that gap at the level of a **controlled approximate mean-SCE history**. It does not claim a nearby exact nonlinear SCE solution, fluctuating quantum-gravity constraints, or a physical gravity instrument.

- Current HEAD: **119387a389ddc6aa1f1c7badf75c3673850e1155**
- Branch: `codex/physics-source-response-20261119`
- PR remains **OPEN DRAFT**. No merge. Core read-only; GI excluded.
- [Research entry](https://github.com/MurphyHoops/UEOT/blob/119387a389ddc6aa1f1c7badf75c3673850e1155/physics/qm/null_source/timelike/dynamic_seed/README.md)
- [Dynamic proof](https://github.com/MurphyHoops/UEOT/blob/119387a389ddc6aa1f1c7badf75c3673850e1155/physics/qm/null_source/timelike/dynamic_seed/DYNAMICS.md)
- [Full records / ensemble / clock](https://github.com/MurphyHoops/UEOT/blob/119387a389ddc6aa1f1c7badf75c3673850e1155/physics/qm/null_source/timelike/dynamic_seed/RECORDS.md)
- [Reflection and next exit](https://github.com/MurphyHoops/UEOT/blob/119387a389ddc6aa1f1c7badf75c3673850e1155/physics/qm/null_source/timelike/dynamic_seed/REVIEW.md)

### What changed

1. Fixed the predecessor's exact, correlated **unfiltered** base parameters and state: original M2/U0, two complete fields, canonical zero modes, the full thermal k=2 shells, and the fixed AE prescription. High modes are exact incoming Jost solutions; zero-mode Q/P and the entire S0 spectrum are transported without resets.
2. Reconstructed the actual normal derivative, KG second jet, all AE local contacts and log derivatives. Certified a unique growth root in (1,3), a nonzero D_new(2s)>11, and beta=-Q2/D_new(2s) near -1/3.
3. Went beyond the jet: real-frequency Volterra comparison with WKB5, followed by Cauchy estimates on its **finite local** delta expression, gives exact bare-minus-AE tails <1100/k^5. The k²-weighted full sums are uniformly analytic in |z|≤1/16. Exact modes are never assumed analytic at delta=1/k²=0.
4. Certified a full spatial residual disk majorant <3.171, hence M=4. With one exact s/beta choice, epsilon=10^-4 exp(-s) and eta in [0,1], Cauchy and the exact full-AE Ward identities give the actual window and normal derivative bounds below.
5. Proved the conditional full dynamic O(2) record equivalence, checked a rational ensemble/flag counterexample, and separated conformal time from two proper-time calibrations.

### Certified new numerical exit

Let x=A²; E_rho and E_p denote **orthonormal** Einstein-minus-2T defects.

| Quantity | Certified enclosure / upper bound |
|---|---|
| s | [1.9999999999909654, 1.9999999999909663] |
| beta | [-0.3333333332868799, -0.33333333328687836] |
| D_new(2s) | [12.000000001357268, 12.000000001357309] |
| Positive conformal-time window | [0,1], fixed epsilon=10^-4 exp(-s) |
| Spatial equation absolute residual | <1.642e-8 |
| x times absolute E_rho | <2.465e-12 |
| x times absolute E_p | <3.284e-8 |
| a³ times absolute normal derivative of E_rho | <3.0e-11 |
| a³ times absolute normal derivative of E_p | <3.0e-7 |

The intervals enclose exact jointly defined parameters, not independent floating-point selections. These are equation residuals in model units, not errors relative to an established exact SCE solution or experimental sensitivity.

### Exact-HEAD verification

- Local: **5/5 new checks PASS**.
- Reused **69 predecessor results**, with **254 inherited scientific files unchanged**.
- Old scientific checker reruns: **0**. Old/new mode or geometry ODE integrations: **0**.
- Current science CI: [44679853647 — SUCCESS](https://github.com/MurphyHoops/UEOT/actions/runs/44679853647).
- Job [136100355948](https://github.com/MurphyHoops/UEOT/actions/runs/44679853647/job/136100355948): exact HEAD and all five PASS lines verified in decoded logs.
- Artifact: `dynamic-seed-research`, ID **14604160314**, 21879 bytes.
- Artifact SHA-256: `b000e68115a710cb58b2c712352ba36c004d07e6e3dfd80cb8cfd5a1950d3422`.
- [Local source/hash receipt](https://github.com/MurphyHoops/UEOT/blob/119387a389ddc6aa1f1c7badf75c3673850e1155/physics/qm/null_source/timelike/dynamic_seed/verification.json) is explicitly a precommit local receipt; current-HEAD CI supplies the committed reproduction.
- Current publication run [44679853680](https://github.com/MurphyHoops/UEOT/actions/runs/44679853680): **IN PROGRESS** at this observation; manuscript PASS, English/Chinese PDF jobs in progress. This is not represented as publication success.
- Predecessor c8c9e7fa science **44673273555** and publication **44673273718** both completed successfully.

### Review and exact scope

All three native agents independently reread exact HEAD **119387a389ddc6aa1f1c7badf75c3673850e1155** after push and reported **no blocking issues** in their assigned scopes: A (state/Ward/UV), B (KG/AE/response/UV), C (dynamic records/ensemble/clock). The nonblocking clarifications below are recorded explicitly. Root alone wrote and executed on the authorized Mac. This is not external human peer review.

Review clarifications for future use:

- The 124/omega^5 derivative estimate is for the original v' difference after removing the plane-wave phase, obtained by differentiating the original sine Volterra kernel to cosine. It is not a bound on F_z.
- The finite 3×3 O(2) witness uses U_R=diag(1,R). Its scalar-block Kraus operators are separately covariant.
- The predecessor CQ twirl statement concerns its explicitly listed source/thermal states and classical geometry labels. An arbitrary constrained gravity/device correlated extension requires a new **full joint** twirl check.
- A nonlinear quotient-system common selection must depend only on the common (g,q) data.

### Next scientific gate after this closure

**Small residual does not establish a nearby exact solution.** The next exit is a bounded inverse/existence or exclusion result for the full nonlinear fixed-AE SCE with the same incoming contract, including its higher-derivative and constraint conditions.

Then specify a fluctuation law and joint constrained initial data capable of carrying the full source distribution. The homogeneous fixed-state seed cannot absorb extra random incoming zero-mode energy. Actual local preparation, probes/clocks, total device stress and complete calibrated records remain open.

The dynamic O(2) theorem closes the current identification branch under its stated contract: same full joint twirl plus a common covariant causal physical instrument implies identical full records, regardless of duration, adaptive outcomes or stopping. Any new distinguishability claim must identify and account for the physical input that changes this contract.

The earlier static >7% result remains a bound for its explicitly specified strong second-moment criterion. It is neither a geometry RMS bound nor a failure of the mean-SCE. No empirical status or whole-unification claim is upgraded.

---

<details>
<summary>Archived predecessor record — superseded by the current HEAD and status above</summary>

## Latest closure: correlated static-source residuals

Current head: **c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea**. The PR remains **OPEN DRAFT** on the same base. This increment freezes the complete preceding joint-history directory and continues the reflection after its all-time mean-SCE closure.

### Why another increment was needed

The preceding greater-than-10% record-weighted residual bound assumed that the conditional zero-mode and high-mode states factorized. Negative covariance or entanglement was therefore a concrete remaining route that required analysis.

This increment removes that factorization assumption. It also allows arbitrary stationary high-mode excitation rather than only thermal k=2 shells. It proves a strict **record-weighted relative source/constraint RMS greater than 7%**, with the certified lower expression approximately **0.0712220292813295**.

The previous product-state bound remains >10%. The new theorem does not extend 10% to correlated states, does not exclude improvement within 7%–10%, and does not claim a sharp optimum.

### Proof and resulting behavior

For each actual static branch, retain all AE/Casimir and U0 constants in Ec and use the exact operator decomposition:

H = Ec + Es*S0 + H_high_exc, with H_high_exc >= 0.

S0 and the high-mode Hamiltonian strongly commute even when the state is entangled. Consequently:

Var(H) >= Es^2 * E[(S0-tau)_+^2], where tau=(E H-Ec)/Es.

The positive part is essential. The code includes a negative control rejecting the false untruncated square replacement.

The spatially averaged necessary equations of a full static mean-SCE state still give G(x)=M2*mu>0 and N(x)>=0. Harmonic orthogonality removes the integrated zero/high cross operator term without deleting local noise. Stationarity of the high marginal supplies its averaged radiation relation. New exact identities give:

- M2*tau'(x)=2*N(x).
- M2*tau(x)=G(x)+2*x*N(x).

The entire allowed positive branch therefore has x<=x0 and tau<=mu_old. Preserving the full input S0 law across all records and applying Jensen to its actual high-radius component gives:

E_input[(S0-mu_old)_+^2] >= 0.5*(d/2-1/nu0)^2.

Thus the complete-record relative RMS is strictly greater than:

(d/2-1/nu0)/(3*sqrt(2)*L) > 0.07.

Classical anticorrelation, quantum entanglement, and additional stationary positive-energy shells cannot eliminate the residual within this fixed static matter contract.

### Scope

- Full static mean-SCE is an assumption of this necessary bound, not a newly constructed family of arbitrary entangled solutions.
- The high marginal must be stationary, Hadamard, and have finite mean excitation energy; the joint state need not be stationary.
- Conditional factorization, a thermal distribution, and restriction to k=2 are not required.
- The same U0/M2/AE and complete input S0 law are retained; all records are included.
- This is a record-weighted source/constraint RMS, not a universal individual-branch statement or a geometric RMS measurement.
- Nonstatic geometry, different matter interactions, changed U0, or changed input spectra require new analysis. Mean-SCE itself is not disproved.

The roadmap now gives priority to a dynamically constraint-compatible joint initial state and positive-time fluctuation feedback. Increasing static source correlations alone is no longer a candidate way to remove the residual.

### Verification and independent review

- **2 new local checks PASS; 67 predecessor results reused; 246 inherited scientific files byte-identical.**
- The entire preceding joint_history directory is frozen. There are zero old checker reruns and zero new mode/geometry ODE integrations.
- Together with the preceding six-check joint-history increment, this turn added eight distinct scientific checks.
- All three native research agents independently reviewed the derivation and then the actual committed files at c8c9e7fa. A checked the strong-commutation/positive-part proof, B checked the averaged equations and global threshold, and C checked Jensen, normalization, and the 7%/10% scope. All reported no required correction.
- [Exact-head scientific CI 44673273555](https://github.com/MurphyHoops/UEOT/actions/runs/44673273555): **SUCCESS**. Decoded job 136078991217 confirms checkout c8c9e7fa, both new PASS results, and the 67-result/246-file reuse gate.
- Artifact correlated-static-research: ID **14600504043**, 19,290 bytes, SHA256 **5e061022b80aff01c90fb5cbba6f23a52c41da05f837453a1559bb9ea7a81aa5**.
- [Publication compatibility 44673273718](https://github.com/MurphyHoops/UEOT/actions/runs/44673273718): manuscript consistency (136078992964) and the complete English PDF (136079231080) have passed; the Chinese PDF (136079231108) is still running at the latest observation. This is not reported as a completed publication pass.
- The local receipt keeps its actual precommit parent 74a5fea8 and dirty-state identity. Exact-head CI is separate evidence.
- Core is read-only, GI is excluded, and formal manuscript/empirical claims remain unchanged. Physical unification remains an open goal.

### Current reading entry points

- [Correlated-state proof and scope](https://github.com/MurphyHoops/UEOT/blob/c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea/physics/qm/null_source/timelike/correlated_static/README.md)
- [Directed and symbolic certificate](https://github.com/MurphyHoops/UEOT/blob/c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea/physics/qm/null_source/timelike/correlated_static/correlations.json)
- [Independent review](https://github.com/MurphyHoops/UEOT/blob/c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea/physics/qm/null_source/timelike/correlated_static/review.json)
- [Execution receipt](https://github.com/MurphyHoops/UEOT/blob/c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea/physics/qm/null_source/timelike/correlated_static/verification.json)
- [Updated research roadmap](https://github.com/MurphyHoops/UEOT/blob/c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea/physics/qm/ROADMAP.md)

<details>
<summary>Closed joint histories and preceding exact-commit evidence</summary>

## Current scientific increment: joint mean histories and full-record residuals

Current head: **74a5fea8d853809671cac2e170dc0b656c80fee7**. This remains an **open draft research PR** on the existing base. Core is read-only; GI, the formal manuscript claims, Lean claims, and empirical status remain outside this increment.

### Problem and resulting behavior

The predecessor constructed a complete static mean source but found that a fixed-incoming-state linear FLRW constraint cannot carry its actual nonzero energy noise. This increment constructs a genuinely joint state/geometry preparation and then tests the remaining fluctuation responsibility.

With the same two minimally coupled massless fields, fixed original calibration M2, fixed matter potential U0, and the same complete AE prescription, halve the centered canonical zero-mode momentum variance and add equal thermal occupation to both complete k=2 shells (eight real oscillators). A smooth two-outcome CP filter of S0, with q=1/2 and t=10^-12, produces actual positive and negative conditional energy shifts. The conditional state and its geometry are selected together once.

For each record, both complete static Einstein equations reduce exactly to:

- M2*mu = 4*U0*x^3 - 3*x^2 - x/(16*pi^2).
- J*n = 3*x - 3*U0*x^2 - 2*B(x) + 3*D0, with J=4*sqrt(3)/pi^2.

The positive radius root is unique. Correlated shifted equations avoid cancellation of the inherited wide x0 and U0 intervals. Actual success and failure branches both have 0.004 < x0-x < 0.0045 and 0.017 < n < 0.020. Their positive normal Hadamard states satisfy the complete mean equations for all real time; all normal derivatives of the mean residual vanish. No timewise parameter-root splicing occurs.

### Closed results

1. Smooth success **and failure** states, complete conditional Laplace laws, canonical Q/P backreaction and retained phase memory.
2. Explicit all-time conditional mean-SCE histories at fixed U0/M2. The new preparation changes the actual conditional source M2*mu_i and the first-field quantum marginal; M2 is the retained calibration.
3. Complete global energy is the convolution of the conditional zero-mode law with an eight-oscillator negative-binomial thermal law. Thermal energy variance and zero/high local stress cross noise are retained.
4. Old/new preparations still have identical complete O(2)-invariant records, including the classical geometry label, under the stated common radial preparation.
5. The actual thermal pressure response has been added to the full AE characteristic expression. Its bracket correction is below 0.01801; the positive homogeneous growth root persists with |s-2| < 3.992659e-10 for the actual branches.

### Reflection completed as a second result

All positive-energy static branches of this fixed-U0, nonnegative-thermal model obey x_i <= x0 and mu_i <= L+2/nu0. Therefore **any** decomposition preserving the complete input S0 law and retaining all records, even continuously many records, satisfies:

E_i Var(S0|i) >= 3/16 + L/nu0.

For the stated conditional zero/high product preparation:

E_i[Var(rho_i)/E(rho_i)^2] > 1/(48*L^2) > 1/100.

This is a strict **record-weighted relative source/constraint RMS greater than 10%**. It is an additional second-moment acceptance result, fully compatible with the new mean-SCE histories. It is neither a universal per-branch statement nor a geometric fluctuation measurement. Finer static records cannot remove the original common radial source noise within this model.

Additional bounds quantify finite-record residuals and mean-preserving rare-event filtering: success probability is at most 2*exp(-2*nu_preparation/625) under the stated mean/variance target.

### Scope and next scientific gate

The CQ preparation is explicit; a causal local controller producing the correlated geometry and thermal state has not been constructed. Full nonhomogeneous gravitational fluctuation feedback, a calibrated local probe, stability beyond the positive linear mode, and independent physical selection of U0/state/matter inputs remain open.

The next gate is a dynamically constraint-compatible joint initial state and positive-time history carrying the full source distribution. The roadmap no longer proposes finer static filtering as a route around the proved residual floor.

### Independent review and reproducibility

- Three native research agents independently reviewed the mathematics and the actual committed files. A and C found no substantive errors. B requested that O(2) invariance be restricted to the centered reference state, because the full coherent preparation can have a directed mean; this was corrected in 74a5fea8 and independently reread.
- Six new local checks: **PASS**. The final local receipt truthfully records execution on parent 95c2fb45 with the documentation corrections still uncommitted.
- **61 predecessor results reused; 225 inherited scientific files byte-for-byte unchanged.**
- Old scientific checkers rerun: **0**. New mode or geometry ODE integrations: **0**.
- Science CI on the first reviewed implementation 95c2fb45: [success, run 44671429960](https://github.com/MurphyHoops/UEOT/actions/runs/44671429960), with all six new checks and the 61/225 reuse line verified in decoded logs.
- Exact-head science CI at 74a5fea8: [run 44671834606](https://github.com/MurphyHoops/UEOT/actions/runs/44671834606), **SUCCESS**. Decoded job 136074352602 confirms the exact checkout, all six PASS results, and 61 reused checks / 225 unchanged files. Artifact 14600172110 has SHA256 883de29e7464a41d9ff295d1bec47125f53677f1d2a9b5efa09cbfb7e50aeefe.
- Final-head publication compatibility: [run 44671834625](https://github.com/MurphyHoops/UEOT/actions/runs/44671834625), awaiting final observation.

### Reading entry points

- [Current research report](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/README.md)
- [Full state/geometry histories](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/HISTORY.md)
- [Complete records and actual response](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/RECORDS.md)
- [Global cap and residual bounds](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/BOUNDS.md)
- [Independent review](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/REVIEW.md)
- [Local execution receipt](https://github.com/MurphyHoops/UEOT/blob/74a5fea8d853809671cac2e170dc0b656c80fee7/physics/qm/null_source/timelike/joint_history/verification.json)

<details>
<summary>Predecessor scientific history and exact-commit evidence</summary>

## Purpose

The preceding later-release theorem still used a prescribed mathematical preparation driver. Completing the physical account requires a realizable past, the entire reservoir/reference stress, one common state–geometry history, and a constraint-compatible fluctuation response.

This increment closes three connected model questions, then uses the new results to reject the most direct fixed-state linear stochastic completion. It preserves the previous scientific files and their original scopes. This PR remains **OPEN DRAFT**, stacked on #467.

## Current increment: a40f7333a3100978674ae33892a409bfaa9aa7ff

[Complete result](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/README.md) · [Preparation obstruction](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/PREPARATION.md) · [Complete records and budget frontier](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/RECORDS.md) · [Actual response and stochastic constraint](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/RESPONSE.md) · [Independent review](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/REVIEW.md) · [Local execution receipt](https://github.com/MurphyHoops/UEOT/blob/a40f7333a3100978674ae33892a409bfaa9aa7ff/physics/qm/null_source/timelike/physical_source/verification.json)

### Physical changes and resulting behavior

- **Old physical-past completion excluded, with a precise scope.** If the entire old static auxiliary S3 past is promoted to the physical spacetime, retaining A=sqrt(3)*lambda and the original M2, one extra independent free minimal massless scalar cannot supply the required stress. A fixed regular Hadamard state, including squeezed, mixed and non-Gaussian states, obeys an absolute long-time spatially averaged NEC bound. The normalized gap is >1.999997. This does not extrapolate to the unknown exterior of the original finite inner ball.
- **A complete replacement mean history exists.** Two actual quantum fields, both complete regular zero modes, the unchanged numerical M2, and an explicitly added constant matter potential U admit an all-time Einstein-static mean solution. For each fixed M2 and budget b, solve one strictly monotone radius equation and choose U once. Both Einstein components hold with all reference RSET terms. This changes the geometry and prepared state; U is a new physical input, not a Core-derived result or an implementation of the original driver.
- **A sharp lower average reservoir budget, with its noise cost.** Finite randomized coherent completion lowers the exact invariant-record equality threshold from the earlier fixed-radius requirement sqrt(3)/2 to sqrt(3)/4. The earlier theorem remains valid under its stronger hypothesis. At the new minimum, the common radial variance is necessarily 3/16 and its relative RMS is about 30.217%. The sharp equal-law frontier is Var(R)=(d-b)_+^2, d=sqrt(3)/2; 1% radial RMS requires b>=0.8475499047370678.
- **Complete quantum records and noise.** The proof includes both reference fields, the reservoir and label cross correlations. The full source noise is 2*N0+(1+b)*N1+Var(R)*C⊗C. The actual global energy distribution is an explicit noncentral chi-square mixture, and equality of its law is equivalent to equality of the radial law. Finite-quantum-noise TV bounds and an abstract CP energy instrument are given; no local gravitational detector is claimed.
- **Actual same-state stability audit.** The complete retarded KG response, regular zero mode, infinite tail, and all fixed AE contacts yield a positive homogeneous linear growth root with |s-2|<6.208818e-10. This is not a nonlinear instability theorem or an integrated nonlinear perturbation family.
- **The next direct gravity completion is ruled out.** With fixed incoming state and matter parameters, the homogeneous first-order Hamiltonian variation cancels the induced density variation. It would require zero homogeneous energy noise, whereas the complete regular-zero-mode energy variance is strictly positive, even when classical radial noise is removed. Changing a Green function, lapse, or first-order H0 cannot fix this. The next gate is lawful constraint-compatible joint state/geometry initial data and its propagation, including the required correlations or nonlinear response.

### Validation and boundaries

- Local: **6/6 new checks PASS**, 5.44 seconds; **55 predecessor results reused**, **204 inherited scientific files byte-identical**.
- No predecessor checker execution, no new mode ODE or geometry ODE integration.
- The new response-symbol evaluation is an algebraic series with a proved infinite-tail bound; it does not rerun archived mode propagation.
- Three native research agents cross-reviewed the derivations; root performed all project writes and execution on the authorized Mac. No external-model or human-peer-review claim.
- The archived local receipt truthfully records its precommit HEAD and dirty worktree. Exact-head CI is recorded separately below.
- Core, GI, formal manuscript claims, empirical status, and previous scientific bytes retain their roles. Stable nonlinear quantum-gravity feedback, a real local preparation/probe, and the physical-unification goal remain **OPEN**.

### Exact-head CI

- Scientific workflow [44661229850](https://github.com/MurphyHoops/UEOT/actions/runs/44661229850): **SUCCESS**, job [136039694171](https://github.com/MurphyHoops/UEOT/actions/runs/44661229850/job/136039694171).
  Decoded logs confirm checkout of a40f7333a3100978674ae33892a409bfaa9aa7ff, all six new checks PASS, and reuse of 55 results with 204 unchanged scientific files.
- Artifact physical-source-research: ID 14596285093, 21,583 bytes, SHA256 45db9eabad5c780c21adbcfbdc7fb58b11e8d228fc96abde6589eb5c70425b00.
- Publication workflow [44661229826](https://github.com/MurphyHoops/UEOT/actions/runs/44661229826): **SUCCESS** at the same exact head. Manuscript consistency (136039694314), complete English PDF (136040222908), and complete Chinese PDF (136040222927) all succeeded.
- All three native reviewers have re-read the committed proofs/certificates at this exact head and reported no material transcription or scope errors.


---

<details>
<summary>Preceding increment and inherited evidence</summary>

## Purpose

The previous increment ruled out a smooth **immediate undriven** extension of the actual prepared past. A principal inverse alone did not establish a compatible state space, a complete nonlinear solution, smoothness, or the Hamiltonian constraint.

This increment constructs a **later-release common mean history** with the same complete initial quantum state, one fixed M2, and the same AE prescription. It then audits what the construction requires physically: its mathematical preparation driver must violate NEC somewhere, and a fully quantum two-field completion can erase the entire invariant total-source record difference. The PR remains OPEN DRAFT, stacked on #467.

## Latest increment: a0fdc3ab0622f21f03cafe52944740d9132b122c

[Complete result and reflection](https://github.com/MurphyHoops/UEOT/blob/a0fdc3ab0622f21f03cafe52944740d9132b122c/physics/qm/null_source/timelike/compatible_evolution/README.md) · [Full regularity proof](https://github.com/MurphyHoops/UEOT/blob/a0fdc3ab0622f21f03cafe52944740d9132b122c/physics/qm/null_source/timelike/compatible_evolution/REGULARITY.md) · [Actual existence certificate](https://github.com/MurphyHoops/UEOT/blob/a0fdc3ab0622f21f03cafe52944740d9132b122c/physics/qm/null_source/timelike/compatible_evolution/history.json) · [Independent physical review](https://github.com/MurphyHoops/UEOT/blob/a0fdc3ab0622f21f03cafe52944740d9132b122c/physics/qm/null_source/timelike/compatible_evolution/REVIEW.md) · [Execution receipt](https://github.com/MurphyHoops/UEOT/blob/a0fdc3ab0622f21f03cafe52944740d9132b122c/physics/qm/null_source/timelike/compatible_evolution/verification.json)

### Common-history result

- Certify the actual centered-state norms over **every preceding initial-slice root**, including the transported regular zero mode, the existing mode boxes 2–512, all-root parameter transport, and the complete infinite tail:
  N0 < 0.060969289, S1 < 42.841740, S < 43.026175, S2 < 13697.978605.
  The coherent source M2 is separate and remains fixed along each history.
- Close the **entire** difference budget: regular quantum response, synchronized a/h, 2hP, all fixed AE local terms, Einstein/source/anomaly integrals, and driver geometry dependence. At T=2^-21 the full difference factor is <0.164799; self-mapping is established separately.
- Use T=2^-40 and a closed C0 ball of radius 1/16 in which every candidate equals the actual reference history on the same interval [0,T/4]. This preserves an entire buffer under the causal fixed point, not merely jets under a C0 limit.
- Let R_ref be the actual integrated trace defect, H_alpha=chi*R_ref+alpha*Psi, and predefine F_alpha=H_alpha'/(6*a_ref). The actual candidate source is 6*integral(a*F_alpha)=r*H_alpha-integral(r'*H_alpha), with r=a/a_ref. The calculation does not silently replace a by a_ref.
- Certify D=||R_ref|| < 3.735471570e-6 from existing actual mode boxes and the infinite tail, retaining the exact initial Einstein/source cancellation. The complete contraction factor is <6.494552e-12 and the self-map margin is >0.0613793585.
- Prove same-window C-infinity regularity from the **original static seed**, using a high-mode cutoff, exact finite-mode principal cancellation, diagonal Volterra derivatives, the second-phase A^2*log term, on-shell Wick-square regularity, and a genuine weighted C^m Banach inverse theorem. No unverified Gevrey or weighted-moment assumption is imported.
- Propagate the same full initial quantum state along the resulting smooth geometry; positivity, CCR and Hadamard legality hold on the final common history.
- Shoot one constant alpha, at fixed M2, to C(3T/4)=0. The endpoint sign margin is >1.35895664e-18 and the strict monotonicity margin >2.72848410e-13. Thus each chosen initial root has a unique alpha_star with |alpha_star| <1.120641471e-5.
- F vanishes identically on [3T/4,T]. Conservation C'=2*a'*B gives **both mean SCE equations throughout that positive-length release window**.

This is an analytic existence construction with directed numerical inequalities, not a sampled numerical trajectory or a computed approximation to alpha_star. The post-release proper duration is about 1.29e-8 **model units**, not seconds.

### Reflection after closure: a necessary device obstruction

The conserved mathematical driver has rho_D=3*C/(2*a^4) and p_D=C/(2*a^4)-F/a^3. Throughout the preparation window h<0, and the initial and release driver densities are zero.

The retained actual buffer and the previous all-root pressure derivative certificate give
(rho_D+p_D)'(0)=-p_q'(0)>0. Conservation then forces

integral(-h)*(rho_D+p_D)_+ = integral(-h)*(rho_D+p_D)_- > 0.

Consequently **some nonempty open interval must have rho_D+p_D<0**. A separately conserved homogeneous apparatus satisfying NEC throughout cannot implement this protocol. No common numerical length of the initial positive-NEC interval is asserted.

This does not exclude a quantum implementation, but one must construct its actual state, dynamics and complete stress. The review specifies the correct next necessary QNEI: null-contracted stress sampled along a timelike proper-time curve, with the actual device reference RSET retained. Passing such an inequality would not prove device realizability.

### Next loop: complete total-source statistics

- Construct two identical free scalar fields in an O(2)-invariant reference state. For each original label y, choose reservoir displacement sqrt(ell-y^2), with ell>=1+sqrt(3)/2.
- The first field marginal is exactly the original preparation. Branch states are symmetry rotations of a single state; the complete total stress is invariant.
- Therefore every bounded invariant record effect has the **same full probability law** for old and new preparation: TV=0, equal-prior Bayes error=1/2. This follows directly from effects, not an unjustified moment-determinacy argument.
- Include the reservoir's genuine quantum fluctuations and the second reference RSET. The sharp extra coherent displacement budget is at least sqrt(3)/2 of the original field budget.
- On the original single-field initial geometry the complete added source gives normalized Hamiltonian mismatch >0.866025. The completion is not a repair of that geometry and is not a universal lower bound on renormalized energy.
- A symmetry unitary is not yet a local controller/CP instrument. A vanishing mean driver does not make device or cross noise vanish.

## Validation

- Local Mac runner PID 69826: **all 6 new checks PASS**, exit 0, wall time 4.90 s.
- **49 predecessor results reused; 186 inherited scientific files verified byte-identical; 0 old scientific checkers rerun.**
- No new or repeated mode ODE or geometry ODE integrations. New work consists of directed bounds, exact identities and analytic proofs.
- 18 new research files and four route/workflow updates; the execution manifest binds 21 files excluding its own receipt. New code syntax, report file links and staged whitespace checks passed.
- Three native collaborators reviewed common history/shooting, full response/regularity, and total-source/device scope. Root alone executed and wrote the existing Mac worktree. This is AI-assisted review, not external human peer review or new Lean formalization.
- The committed local receipt retains the actual precommit HEAD and dirty-worktree identity. Exact-head remote CI is recorded separately below.
- Normal commit and push completed on the existing research branch. Core, formal book, Lean and empirical status were not changed.
- [Exact-head scientific CI](https://github.com/MurphyHoops/UEOT/actions/runs/44656710402): **PASS** on a0fdc3ab0622f21f03cafe52944740d9132b122c. Decoded job logs confirm the checkout, all six new PASS results, and the 49-result/186-file reuse gate.
- [Remote execution receipt and logs](https://github.com/MurphyHoops/UEOT/actions/runs/44656710402/artifacts/14593148274) uploaded successfully, 18,145 bytes, SHA256 `6d3a6d3c58589d1f687d20b5f3da4fcb4aab7ee6b99bcce906abc4205f9d21f4`.
- [Same-head publication compatibility](https://github.com/MurphyHoops/UEOT/actions/runs/44656710504): **PASS**. Manuscript, complete Chinese PDF, and complete English PDF jobs all succeeded.
- The worktree is clean, the pushed research head is a0fdc3ab0622f21f03cafe52944740d9132b122c, and the PR remains OPEN DRAFT. A fresh comparison found no main-branch commits missing from the research history.

## Scope and next acceptance

The preceding immediate-release obstruction is preserved. The new result is local, later-release mean SCE existence under a specified mathematical driver; it does not establish a physical apparatus, global/long-time stability, EFT validity, complete nonhomogeneous gravitational feedback, or an experimental gravity record.

Next acceptance is a specified realizable quantum preparation system (or an explicitly redesigned preparation), its total mean stress and all field/device/control cross correlations, then full feedback and a calibrated instrument on the **same new history**. Archived fixed-background probabilities are not transferred to this tiny release window. Independent physical selection and empirical discrimination remain required for the unified-physics goal.

## Preserved earlier evidence

- [Prepared-history obstruction at 741209b3](https://github.com/MurphyHoops/UEOT/blob/741209b3c010bc6dcfe695d8d3b71cba4448fe3f/physics/qm/null_source/timelike/prepared_dynamics/README.md), [exact-head science CI](https://github.com/MurphyHoops/UEOT/actions/runs/44611365712), and [publication CI](https://github.com/MurphyHoops/UEOT/actions/runs/44611365615).
- [Prepared initial-slice existence at d62c9ff](https://github.com/MurphyHoops/UEOT/blob/d62c9ff9525ebf314f5aae5f674c38c9761de1fa/physics/qm/null_source/timelike/prepared_initial/README.md), [science CI](https://github.com/MurphyHoops/UEOT/actions/runs/44594485919), and [publication CI](https://github.com/MurphyHoops/UEOT/actions/runs/44594485732).
- [Overlap-response report at 6401950](https://github.com/MurphyHoops/UEOT/blob/6401950ba154f1be763655ca7f68aeb842628922/physics/qm/null_source/timelike/overlap_response/README.md) and [science CI](https://github.com/MurphyHoops/UEOT/actions/runs/44583117834).
- Earlier compatibility/noise/metric/operational evidence is transitively frozen by the new runner. GI remains excluded; unified physics remains an open scientific goal.


</details>


</details>


</details>


</details>


</details>


</details>
