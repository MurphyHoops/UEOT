# UEOT Core Compression Coverage

This file is the human-readable counted-status view for the post-106
compression mission. It is **not** the Core v3 source-proof ledger and never
changes the completed **106/106 FULL-GREEN** source status.

## Frozen baseline

- Core v3 source P-IDs: **106**
- Core v3 source proofs: **106/106 FULL-GREEN**
- mission-start main: `29d946422f02bb025bd5d450acc434486ecdb422`
- canonical source SHA-256:
  `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

## Compression evidence state

| metric | count |
|---|---:|
| source P-IDs analyzed | 106 / 106 |
| schema-classified P-IDs | 106 / 106 |
| fully Lean-rederived P-IDs | 11 / 106 |
| counted compressed P-IDs | 11 / 106 |
| final dispositions assigned | 106 / 106 |
| generated final dispositions | 11 / 106 |
| retained domain adapters | 89 / 106 |
| retained boundary/no-go results | 6 / 106 |
| unresolved final dispositions | 0 / 106 |
| counted meta-generators | 4 |

Mission state: **READY_FOR_FINALIZATION (POST-GATE-D REOPEN)**. Minimal core:
**FROZEN = {M-QD-01, M-TC-01, M-PE-01, M-OI-01}**. Ablation:
**COMPLETE**. Scoped minimality claim:
**NONREDUNDANT_UNDER_DECLARED_DERIVATION_SYSTEM**.

The frozen Core v3 source baseline remains **106/106 FULL-GREEN**. This
post-Gate-D reopening changes compression accounting only; it does not reopen,
renumber, or weaken any frozen source P-ID theorem.

The live 106-row accounting is now **11 generated + 89 retained_adapter + 6
retained_boundary = 106**, with zero unresolved. The historical nine generated
P-IDs remain counted, and two exact mappings are added under M-OI-01:

- **P-PER-02** via
  `UEOT.V3.Compression.OccupationLimitInvariance.p_per_02_via_occupationLimit`;
- **P-GOA-01** via
  `UEOT.V3.Compression.OccupationLimitInvariance.p_goa_01_via_occupationLimit`.

The post-Gate-D Gate-C rerun freezes the enlarged core
**{M-QD-01, M-TC-01, M-PE-01, M-OI-01}**. Historical deletion witnesses remain
P-PRED-01, P-DYN-03, and P-EVO-04 for M-QD/M-TC/M-PE. M-OI-01 uses P-GOA-01 as
its deletion witness. `POST_GATE_D_EXPANDED_CORE_ABLATION.md` admits the entire
retained M-OI public theorem/definition surface while rechecking all three
historical witnesses; independent Codex review returned CLEAR/no-major-issues.

The derivation system remains the same scoped registered-theorem-surface DAG
notion used by historical Gate C, extended only by formally integrated theorem
surfaces and explicitly frozen post-Gate-D witness adapters. The claim is
architectural nonredundancy, not absolute logical independence or uniqueness.

### Historical Gate-D checkpoint — preserved

The original FINAL result remains immutable historical evidence:

- canonical final main: `8d0fce85ee6b7a5cfd002894d4d08b82e2bfefb2`;
- counted generators: **3**;
- generated mappings: **9/106**;
- minimal core: **{M-QD-01, M-TC-01, M-PE-01}**;
- final closure PR: **#172**;
- candidate-main Core Lean `36541120296`: SUCCESS;
- candidate-main Compression Guard `36541120239`: SUCCESS;
- resulting-main Core Lean `36543948382`: SUCCESS;
- resulting-main Compression Guard `36543948315`: SUCCESS.

The M-OI result does not rewrite that checkpoint as though M-OI had existed
then. It is a later formalized route on an enlarged theorem surface.

### Re-finalization status

M-OI feature/audit PR #173 merged to
`main@4a20ad6829eaa2afd46ad39f3cddab6b36341332`; resulting-main Core Lean
`36573837548` and Compression Guard `36573837433` are both SUCCESS. Because the
live counted core changed after FINAL, the ledger is deliberately reopened to
`ready_for_finalization`. The counted-promotion PR #174 then merged to exact
candidate scientific main
`bf1d01a0f7bf658f8c205ddcc1a2832a4bb3638b`; candidate-main push Core Lean
`36578717005` and Compression Guard `36578717533` are both SUCCESS. This branch
is the dedicated post-Gate-D re-finalization closure lane. The fresh closure PR
number is intentionally recorded only after that PR exists, before the live
ledger transitions from `ready_for_finalization` back to `final`.
Until that lifecycle completes, **11/106 is live candidate-main accounting, not
a new FINAL announcement**.

The final-disposition counts are derived from per-P-ID entries in
`COMPRESSION_LEDGER.yaml`; they are not free-standing progress estimates.
Counted compression evidence is distinct from final per-P-ID dispositions and
from the scoped minimal-core/nonredundancy claim. Audit-only candidate schemas are likewise
not counted until they acquire generic Lean theorems and complete the normal
promotion lifecycle.

## Current generator evidence

### M-QD-01 — Quotient Descent

State: **COUNTED_GENERATOR**

The generator satisfies the scientific cross-family exact-mapping gate:
P-PRED-01 and P-INT-02 are exact source-facing mappings in distinct P-ID
families. P-INT-02 and M-QD-01 have completed the normal feature →
integration → PR → resulting-main lifecycle and are promoted through this
ledger checkpoint.

- generic surjective fibre-compatible descent and uniqueness: Lean proved;
- generic countable a.e. measurable family descent: Lean proved;
- P-PRED-01: **counted mapping** — full source-facing canonical minimality +
  sufficiency rederivation under genuinely weaker post-kernel-existence
  assumptions;
- P-INT-02: **counted mapping** — full source-facing two-sided canonical
  quotient factorization + minimal-refinement rederivation through the
  generic two-sided quotient universal property;
- P-DYN-01: partial specialization only;
- P-QUO-01: audited, but **not** generated by bare quotient descent — exact
  control preservation additionally uses Bellman fixed-point uniqueness and
  policy lifting;
- P-ALG-01: audited, but **not** generated by bare quotient descent — finite
  termination, coarsest stable refinement, stochastic quotient normalization,
  and finite-horizon preservation are additional algorithmic structure;
- preserved boundary: set-level descent does not establish measurable kernel
  descent.

### M-TC-01 — Transport Certificate Calculus

State: **COUNTED_GENERATOR**

- generic exact two-stage composition: Lean proved;
- generic exact commuting-factor transport: Lean proved;
- generic approximate two-stage defect bound: Lean proved;
- heterogeneous additive finite-chain accumulation: Lean proved;
- heterogeneous weighted finite-chain / discrete-Gronwall accumulation: Lean
  proved;
- generic multiplicative certificate/product recurrence: Lean proved;
- P-API-01: **counted** full exact + approximate source-facing rederivation;
- P-ID-01: **counted** full source-facing supremum rederivation;
- P-ID-02: **counted** exact finite-horizon development-pipeline product/sum
  bound reconstructed through the weighted chain calculus after the completed
  feature → integration → PR → resulting-main → ledger lifecycle;
- P-DYN-04: **counted** full reachable-image approximate + exact source-facing
  rederivation;
- P-DYN-03: **counted** — the full sharp `1 - ∏(1-ε_t)` path-TV bound and
  additive union-bound corollary are reconstructed through the generic
  multiplicative certificate recurrence; finite-PMF common-mass/TV coupling
  remains an explicit source adapter, and the full feature → PR → resulting-main
  lifecycle is green;
- P-STAT-09: audited, but **not** fully generated — its TV half is transport
  shaped while its Radon--Nikodym density-ratio half uses a distinct
  multiplicative order mechanism.


### M-BU-01 — Bayesian Recursive Closure

State: **FORMALIZED BRIDGE / UNCOUNTED**

Post-Gate-D research now provides a generic Lean Bayes/update surface and an
exact P-PRED-03 rederivation. The finite positive-evidence P-REF-02 posterior
coordinate is an instance of the same Bayes coordinate, while P-REF-02's
zero-evidence `modelConflict` boundary remains explicit.

M-BU-01 is not promoted to the minimal core: full P-REF-02 also contains
Standard-Borel disintegration/reconstruction, posterior averaging,
normalization, conflict semantics, and one-step control reduction; moreover,
pre-existing P-PRED/P-REF helper surfaces make the present route redundant
under the declared deletion system. M-BU therefore remains a useful
cross-family bridge rather than a hidden fifth generator.

### P-PRED-02 split-schema audit

P-PRED-02 is fully source/Lean audited but is **not assigned to one M-ID**:

- target transformation is response-kernel pushforward functoriality;
- protocol inclusion is sigma-factor monotonicity;
- countable protocol union is sigma-factor join continuity.

These are separate reusable mechanisms. They should only receive generator IDs
after broader cross-family reuse is established; no M-QD claim is made.


### Transport / covariance adapter audit

Three additional source theorems are now audited without creating another
meta-generator:

- P-MET-01: exact TV data processing under measurable readouts and common
  Markov kernels, with bimeasurable equivalences giving exact isometry. This is
  a **metric adapter** supplying contraction/isometry hypotheses used by generic
  transport certificates rather than a theorem generated by M-TC-01.
- P-FAC-01: exact representation covariance of dynamics, predictive
  factorization, finite path records, and transported control value under a
  bimeasurable microscopic reparameterization. This remains a
  **representation/domain adapter family**.
- P-STAT-07: exact MMD covariance when laws, feature representation, and kernel
  are transported synchronously through a bimeasurable equivalence. This is a
  **statistical metric adapter**.

P-FAC-01 and P-STAT-07 do share a real bimeasurable-change-of-variables
substrate, and P-PRED-02 has a related target-pushforward clause. The current
common core, however, is standard pushforward/change-of-variables
infrastructure plus domain-specific adapters. No new M-ID is introduced until
a nontrivial reusable theorem beyond that infrastructure is identified.

### Foundational information / interface audit

The remaining Chapters 1–6 foundation rows are now source↔Lean↔schema audited:

- P-MET-02: TV span duality / observable-sensitivity adapter;
- P-PROC-01: complete-history state augmentation / Markovization adapter;
- P-INFO-01: deterministic-statistic information chain rule and entropy memory
  bound;
- P-INFO-02: conditional-KL/Pinsker bridge from information residual to average
  predictive TV;
- P-INFO-03: zero-distortion predictive rate equals canonical-core conditional
  entropy;
- P-INFO-04: sharp Fano and conditional-binary decoder information lower
  bounds;
- P-INFO-05: TV packing obstruction, representation cardinality, and uniform
  entropy lower bound;
- P-INT-01: conditional-independence ↔ common-version factorization for
  structured interfaces;
- P-INT-02: canonical two-sided internal/environment quotient and minimal
  refinement;
- P-INT-03: minimal Markov-boundary uniqueness under intersection/graphoid
  axioms.

No counted status changes in this audit batch. Most rows expose standard
mathematical or domain-adapter infrastructure rather than new meta-generators.

**M-QD frontier:** P-INT-02 is now the strongest honest second-family candidate
for M-QD-01. Unlike P-QUO-01 and P-ALG-01, it adds no Bellman/control or
finite-algorithm machinery: it is pure two-sided quotient factorization plus
minimal refinement. The next Lean-design step is to test a generic two-sided
quotient-descent theorem and a source-facing P-INT-02 wrapper before changing
M-QD's generator state.

P-INT-01 also shares M-QD's factorization substrate, but its full iff retains a
distinct conditional-independence/disintegration adapter and is therefore not
claimed generated yet.


### M-OI-01 — Occupation-Limit Invariance

State: **COUNTED_GENERATOR / POST-GATE-D PROMOTION**

Canonical common theorem:

`UEOT.V3.Compression.OccupationLimitInvariance.invariant_of_continuous_observable_residual`

The shared architecture is a convergent long-run state sequence plus continuous
separating observables, continuous evolved observables, and an asymptotically
vanishing evolution residual, yielding an invariant limiting state.

- **P-PER-02: counted exact mapping.** Tightness/Prokhorov, Feller action
  continuity, occupation-shift control, probability-measure realization, and
  Portmanteau closed-support inheritance remain explicit adapters.
- **P-GOA-01: counted exact mapping.** Finite-simplex compactness, subsequence
  extraction, and the discrete Cesaro telescope remain explicit adapters.

The M-OI deletion audit uses P-GOA-01 as its broken witness. The expanded-core
audit rechecks all historical generator witnesses while admitting the complete
retained M-OI surface. Independent review returned CLEAR/no-major-issues.

Explicit nonclaims: the primitive residual-limit mathematics is standard
analysis/topology; P-PER-01, P-QSD-01, and P-GOA-02..04 are not generated; and
the four-generator minimality claim remains scoped to the declared theorem DAG.

### Dynamics / persistence / recovery adapter audit

Ten additional source rows are now source↔Lean↔schema audited:

- P-DYN-02: finite CTMC generator/block-sum criterion and nonnegative-time
  semigroup intertwining; continuous-time quotient adapter, not bare M-QD;
- P-PER-01: precompact omega-limit persistence and exact semiflow invariance;
- P-PER-02: now **generated by M-OI-01**; Feller/tightness/support machinery
  remains explicit domain adapters inside the exact wrapper;
- P-PER-03: finite viability deletion, winning-set equality, stationary
  selector, and probability-one path safety;
- P-PER-04: positive contingent-cone tangency necessity;
- P-REC-01: discrete affine conditional drift → geometric mean + Markov tail;
- P-REC-02: Dynkin/Gronwall Lyapunov drift → exponential mean-square recovery;
- P-REC-03: expected hitting-time potential → canonical Poisson identity;
- P-REC-04: stopped negative drift → expected hitting-time bound;
- P-GOA-01: now **generated by M-OI-01**; finite-simplex compactness and Cesaro
  telescoping remain explicit domain adapters.

Finite monotone stabilization is visible in both P-PER-03 and P-ALG-01, and
affine dissipation appears in several REC theorems. Those are recorded as
shared proof patterns only: their source theorems carry different strategy,
path, control, or stopping-time semantics, so no extra M-ID is created merely
to rename a common proof idiom.


### M-PE-01 — Positive Eigenstructure Calculus

State: **COUNTED_GENERATOR**

Cross-family evidence now spans quasi-stationarity and evolutionary positive
operators:

- P-QSD-02: positive left/right Perron data give exact QSD propagation, survival
  scaling, a stochastic Doob h-transform, and invariant law q*h;
- P-QSD-04: a positive principal mode plus controlled spectral remainder gives
  conditional-law attraction and the principal survival scale;
- P-EVO-03: Perron rank-one asymptotics give normalized mean composition and
  uniqueness of positive reproductive-value weights;
- P-EVO-04: the positive right Perron eigendirection turns conditional mean
  reproduction into a normalized reproductive-value martingale.

A generic Lean generator is now formalized for the common positive-eigenstructure
calculus and exactly reconstructs P-QSD-02 and P-EVO-04 through explicit
source-facing wrappers. Perron existence/simplicity, primitive-matrix rank-one
power asymptotics, and reversible compact-resolvent spectral remainders remain
explicit adapters; therefore P-EVO-03 and P-QSD-04 are not claimed Lean-rederived by M-PE-01.
The stochastic adaptedness/integrability premises of P-EVO-04 also remain
explicit source adapter assumptions. In particular, a QSD q is not identified
with the Doob stationary law q*h.

### QSD / Perron audit

Six further source rows are now source↔Lean↔schema audited:

- P-QSD-01: conditioned TV limit -> QSD eigenmeasure and exponential survival
  law; retained as a projective normalized-limit adapter rather than forced into
  occupation-limit invariance;
- P-QSD-02: finite Perron/Doob algebra;
- P-QSD-03: same-initial mixing/survival duration-window intersection;
- P-QSD-04: reversible spectral-gap QSD attraction + survival lower bound;
- P-EVO-03: Perron mean growth, normalized composition, and reproductive-value
  uniqueness;
- P-EVO-04: reproductive-value martingale from conditional mean dynamics.

The Perron/eigenstructure overlap is now Lean-realized and ledger-promoted as
**M-PE-01 / counted_generator** for exact mappings P-QSD-02 and P-EVO-04.
P-EVO-03 and P-QSD-04 remain explicit nonclaims; final per-P-ID dispositions
remain a separate Gate-B resolution step.


### OMG / carrier / resolution audit

Twelve further source rows are source↔Lean↔schema audited without inventing a
new counted meta-generator:

- P-OMG-01: finite monotone failure reconstructed from inclusion-minimal
  failures;
- P-OMG-02: distance-to-failure-set margin is 1-Lipschitz;
- P-CAR-01: measurable access sufficiency is upward and finitely generated by
  minimal sufficient carriers;
- P-CAR-02: access erasure failure is blocker hitting and minimal erasures are
  the blocker;
- P-CAR-03: finite clutter blocker involution, including degenerate families;
- P-CAR-04: exact diameter/decoder-radius bounds in a generic pseudometric
  response space;
- P-RES-01/02: closure-based minimal-family coarse-graining and composition;
- P-RES-03: blocker naturality under Boolean coarse pushforward;
- P-RES-04: the Ext^- ⊣ Res ⊣ Ext^+ adjunctions for upward families;
- P-RES-05: exact microscopic realization interval for a coarse clutter;
- P-RES-06: endpoint collapse iff all active coarse fibers are singleton.

The audit deliberately keeps three proof strata separate: finite
minimal-generator reconstruction, blocker duality, and order/closure resolution.
They share infrastructure, but no new M-ID is counted merely by renaming
standard finite-poset, hypergraph, or Galois-connection theorems. A later
cross-family compression may combine them only after a genuinely smaller
generic Lean interface is demonstrated.


### Composition / statistics / identifiability / telescoping audit

Twenty additional frozen rows are now source↔Lean↔schema audited without
changing counted generator or mapping status:

- P-COMP-01..07: conditional path-factorization information, intervention JS,
  composition-margin stability, parent conditional-information monotonicity,
  Boolean overlap atoms, physical-carrier coalition lifting, and compact
  monotone composition windows;
- P-STAT-01..06 and P-STAT-08: finite-alphabet TV concentration, deterministic
  carrier-defect stability, threshold/minimal-family recovery, predictive-class
  recovery, Hilbert/RKHS embedding concentration, and finite-candidate ERM
  validation;
- P-INV-01..05: TV binary-testing limits, Fisher gauge directions, Fisher-kernel
  intersection across interventions, Gram identifiability, and predictable-design
  OLS confidence;
- P-TEL-01: discounted potential telescoping and positive-affine policy-value
  invariance.

The batch intentionally introduces **no new M-ID**. The reusable mathematics is
real but is presently standard domain infrastructure (information geometry,
finite-sample concentration, finite Boolean/order structure, compact monotone
threshold geometry, linear inverse problems, and discounted telescoping) rather
than a demonstrated smaller cross-family UEOT generator. This advances Gate A
coverage while preserving the Mission Contract rule against cosmetic
relabeling.


### Gate A final audit — remaining control / long-run / information / geometry / evolution rows

The final **32** previously unaudited frozen rows are now source↔Lean↔schema
classified:

- P-CTL-01..03: finite discounted Bellman/causal optimality, compact-Feller
  measurable selection, and continuous-time diffusion HJB verification;
- P-QUO-02..05: approximate quotient value/regret, action-gap recovery,
  fixed-policy resolvent/discounted occupancy, and occupancy-weighted local
  regret;
- P-GOA-02..04: Dobrushin mixing/stationary perturbation, recurrent-decomposition
  stability, and symmetric killed-kernel spectral perturbation;
- P-KL-01..05: event data processing, event I-projection, history-dependent path
  KL chain rules, finite-CTMC clock-time path KL, and Girsanov control-energy KL
  with the observed-path inequality kept distinct;
- P-DDH-01..05: gauge non-identifiability, exponential-family
  gradient/covariance calculus, moment I-projection, common-bottleneck rank, and
  singular-value effective-dimension certification;
- P-ALI-01..03: global one-form exactness, parent-value gradient alignment, and
  the exact coordination threshold;
- P-EVO-01..02 and P-BRG-01..02: Price selection/transmission accounting,
  irrelevant shared-label information inflation, fixed-fitness concentration,
  and behavioral selection indistinguishability;
- P-REF-01, P-REF-03..05: reflexive-state path construction and controlled
  closure boundary, free-information value, uniform-objective regret, and
  feasible-set monotonicity;
- P-CORE-01: common-good-event operational assembly of the already certified
  finite modules.

That checkpoint closed **Mission Contract Gate A at 106/106 audited and 106/106
schema-classified P-IDs**. At the time, it deliberately did not assign final
dispositions or freeze a minimal core. Its scientific conclusion remains
operative: a cosmetic “single grand generator” is rejected because the frozen
rows require materially different Bellman/HJB, occupancy/resolvent,
Markov/spectral perturbation, path-information, exponential-family,
differential-geometric, evolutionary, decision, and assembly mechanisms.
The current Gate-B disposition matrix above resolves those audited rows while
preserving those genuine domain adapters and boundaries.


### M-PE-01 ledger-promotion evidence — Positive Eigenstructure Calculus

On this ledger-promotion head, M-PE-01 is marked **counted_generator** with two
source-faithful exact counted mappings:

- **P-QSD-02** is reconstructed exactly from positive left/right finite
  eigenstructure: normalized QSD propagation, survival mass, stochastic
  nonnegative Doob transform, the normalized \(q h\) invariant law, and the
  killed/substochastic \(\rho \le 1\) clause. Assumption relation: **exact**.
- **P-EVO-04** is reconstructed exactly from positive right eigenstructure plus
  the frozen stochastic adapter assumptions: the normalized reproductive-value
  process is a nonnegative integrable martingale with constant expectation.
  Assumption relation: **weaker only at the typeclass level**, because the
  wrapper internally supplies classical decidable equality on the finite type.

The generator deliberately does **not** claim P-EVO-03's primitive Perron
rank-one asymptotics or P-QSD-04's compact-resolvent spectral-gap convergence.
At that M-PE promotion checkpoint, P-EVO-03 and P-QSD-04 remained explicit
nonclaims; the checkpoint metrics were **8/106 Lean-rederived, 8 counted
mappings / 3 generators, and 0/106 final dispositions**. Those numbers are
historical lifecycle evidence only. The current summary table and Gate-B matrix
supersede them for present-state accounting.


## Counting rule

A generator or mapping is counted only after the complete compression
lifecycle:

`SCHEMA -> LEAN -> SOURCE MATCH -> ASSUMPTION AUDIT -> FEATURE CI ->
CLEAN INTEGRATION -> PR CI -> MAIN CI -> LEDGER PR -> LEDGER MAIN CI -> COUNTED`.

Hypotheses, partial mappings and local-only builds are never counted.
