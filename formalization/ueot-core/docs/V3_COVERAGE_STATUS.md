# UEOT Core v3.0 Lean Coverage Status

This document records the source-level P-ID coverage state separately from the
subset of Lean modules currently synchronized into this public repository.

The mathematical source of truth remains
`UEOT_Core_Mathematics_v3.0_Complete.md` with 106 P-IDs. Historical verification
documents and earlier package states are preserved; no P-ID is deleted or
downgraded merely to simplify the completion gate.

## Recovered baseline before remote synchronization

The verified 2026-09-06 baseline contained:

- 9 proved
- 7 partial
- 90 pending
- 106 total P-IDs
- 81 named Lean theorems
- no `sorry`, no `sorryAx`, no UEOT-specific proof axioms

The proved P-IDs were:

- P-CAR-01
- P-CAR-02
- P-CAR-03
- P-RES-03
- P-RES-04
- P-STAT-03
- P-STAT-04
- P-QUO-03
- P-REF-04

The partial P-IDs were:

- P-PRED-01
- P-PRED-02
- P-DYN-01
- P-RES-05
- P-TEL-01
- P-BRG-02
- P-REF-05

## 2026-09-09 advance: P-RES-05

P-RES-05 has been promoted from `partial` to `proved`.

The source statement is the exact microscopic-realization interval

[
\pi_*\mathcal C=\mathcal D
\iff
\uparrow J^-_\pi(\mathcal D)
\subseteq\uparrow\mathcal C
\subseteq\uparrow J^+_\pi(\mathcal D).
]

The resumed Lean track now contains:

- `UEOT.V3.Resolution.UpClosure`
- `UEOT.V3.Resolution.IsAntichain`
- `UEOT.V3.Resolution.PushMin`
- `UEOT.V3.Resolution.imageFamily`
- `UEOT.V3.Resolution.MinimalFamily`
- `UEOT.V3.Resolution.pushFamily`
- `UEOT.V3.Resolution.restrict_upClosure_iff_pushMin`
- `UEOT.V3.Resolution.pushFamily_eq_iff_pushMin`
- `UEOT.V3.Resolution.clutter_realization_interval`
- `UEOT.V3.Resolution.pushFamily_realization_interval`

Here `pushFamily π C` literally encodes the inclusion-minimal members of
`{π '' c | c ∈ C}`, i.e. the source definition of `π_* C`.  The proof uses
finiteness only to obtain a minimal image below each image, and antichain
minimality to force the exact coarse edge.

### Verification evidence

- finite-clutter interval bridge commit:
  `b65ad3e54397927f0aa563a246abf5766404a38b`
- literal `π_*` / minimal-image bridge commit:
  `fa3161688cb1248cee0d1cc1f938893c298ac206`
- GitHub Actions run for `fa316168...`:
  `34336212073`
- result: pinned Lean verified, dependencies resolved, `lake build UEOT` passed.

## Current source-level coverage

| Status | Count |
|---|---:|
| proved | 24 |
| partial | 0 |
| pending | 82 |
| total | 106 |

There are currently no partial P-IDs.

## 2026-09-10 advance: P-REC-01

P-REC-01 has been promoted from `pending` to `proved`.

The source hypothesis is a nonnegative conditional drift inequality

[
\mathbb E[R_{t+1}\mid \mathcal F_t] \le \kappa R_t + \eta,
\qquad 0\le \kappa <1,\; \eta\ge0,
]

with finite initial mean.  The source conclusions are the geometric mean bound

[
\mathbb E R_t
\le
\kappa^t \mathbb E R_0
+
\eta\frac{1-\kappa^t}{1-\kappa},
]

and the corresponding Markov tail bound obtained by dividing the same
right-hand side by a positive threshold.

The Lean implementation separates the algebraic and probabilistic layers:

- `UEOT.V3.RecoveryDiscrete.affine_recurrence_closed_bound` proves the exact
  scalar geometric recursion;
- `UEOT.V3.RecoveryProbability.ennMean_succ_le` derives total-expectation
  recursion from the conditional-Lebesgue inequality;
- `ennMean_lt_top` propagates finiteness from the initial mean rather than
  assuming future integrability in advance;
- `realMean_succ_le` converts the finite ENNReal recursion to the literal
  real affine recursion;
- `p_rec_01_mean_bound` proves the source mean formula;
- `p_rec_01_tail_bound` proves the source Markov tail formula.

Verification evidence:

- clean-rebased branch head:
  `8d6daa8590b209b50761a97d19b8924bfe633cd9`;
- clean branch full-target CI run `34388552652` (#227): success;
- main squash merge:
  `28d8a9a8e4e7a937567e7cf51185163cd0dae2b7`;
- post-merge full-target CI run `34388913585` (#232): success.

## 2026-09-10 advance: P-INT-03

P-INT-03 has been promoted from `pending` to `proved`.

The source theorem assumes a finite variable universe and conditional
independence satisfying the semigraphoid rules plus intersection.  The Lean
formalization isolates the exact proof laws used by the manuscript:

- `CIAxioms.decomposition`;
- `CIAxioms.weakUnion`;
- `CIAxioms.contraction`;
- `CIAxioms.intersection`.

It defines `IsBlanket CI B := CI Bᶜ B` and inclusion-minimal blankets via
`IsBoundary`.  The theorem `boundary_unique` proves uniqueness in a
slightly stronger arbitrary-universe setting once those laws are supplied, and
the wrapper `p_int_03_boundary_unique` restores the source's finite-universe
hypothesis literally through `[Fintype W]`.

Verification evidence:

- clean-rebased branch head:
  `36f6208979e9c69c09cb76b8b2c076564d78f55b`;
- pinned Lean branch push CI run `34384468119` (#191): success;
- main merge commit:
  `50390ebac91981a3d020868f21ed5c7838debeaa`;
- post-merge full-target CI run `34384869497` (#195): success.

## 2026-09-10 advance: P-DYN-01

P-DYN-01 has been promoted from `partial` to `proved`.

The formalization now matches both source clauses for a supplied measurable
candidate macro kernel:

- `StrongLumpability P Pbar f hf` is the one-step kernel intertwining
  statement, equivalent to the source event-preimage equality;
- `PathLawLumpability P Pbar f hf` states that for every microscopic
  probability initial law, the coordinatewise macro pushforward is exactly
  the trajectory law of the same macro Markov kernel;
- `strongLumpability_iff_pathLaw` proves the two formulations equivalent;
- `strongLumpability_iff_pathLaw_of_surjective` retains the source's
  measurable-surjection hypothesis literally.

The reverse implication follows the source proof: choose the Dirac initial law
at a microscopic state, recover the time-one marginal through
`homTrajMeasure_dirac_time_one`, and obtain the one-step pushed kernel.

Verification evidence:

- full iff branch commit:
  `6c8685f6ac7f453ea9ce57cb35f9bad89cbae032`;
- branch CI run `34380983198`: success;
- main merge commit:
  `697b0b1537295b999cb671106bf026866d49114a`;
- post-merge full-target CI run `34381567831`: success.

## 2026-09-10 advance: P-MET-01 and P-MET-02

P-MET-01 and P-MET-02 have been promoted from `pending` to `proved`.

P-MET-01 now matches all three source clauses:

- measurable readout contraction:
  `UEOT.V3.TotalVariation.tvDist_map_le`;
- common Markov-kernel contraction:
  `UEOT.V3.TVKernel.tvDist_comp_le`;
- equality under a bimeasurable bijection:
  `UEOT.V3.TotalVariation.tvDist_map_measurableEquiv`.

P-MET-02 now uses the literal source span
`sSup (Set.range g) - sInf (Set.range g)` for a bounded measurable real
observable and proves the source expectation-gap inequality through
`UEOT.V3.TVSpan.abs_integral_sub_le_span`.

Verification evidence:

- P-MET-01 branch CI: run `34379217252` success;
- P-MET-01 main merge: `dfd55b52629ea0c6d4435ece2b17cb84abc5b705`;
- post-merge full-target CI: run `34379654659` success;
- P-MET-02 exact-span branch CI: run `34379825486` success;
- P-MET-02 main merge: `0a6ead35c9abc9e2ef47005b3120c5c8a84b9c6c`;
- post-merge full-target CI: run `34380492671` success.


The newly proved set is the previous nine plus **P-RES-05**, **P-RES-06**, **P-CAR-04**, **P-RES-02**, and **P-RES-01**.

## 2026-09-09 advance: P-REF-05

P-REF-05 has been promoted from `partial` to `proved`.

The source claim is policy-set monotonicity under a fixed real-valued
evaluation `J` and feasible-set inclusion.

The formalization now provides two aligned forms:

- `feasibleValue_mono`: a total `EReal` formulation requiring no hidden
  nonempty/boundedness assumptions;
- `feasibleValueReal_mono`: the ordinary real-`sSup` formulation under the
  standard conditions that the smaller feasible set is nonempty and the
  enlarged image is bounded above.

It also packages the source's “same evaluation, larger implementable policy
set” condition as `FeasibleDecision.Extends`.

Key declarations:

- `UEOT.V3.Agency.feasibleValue`
- `feasibleValue_mono`
- `feasibleValueReal`
- `feasibleValueReal_mono`
- `FeasibleDecision`
- `Extends`
- `extension_optimalValue_mono`

Verification evidence:

- source-aligned module:
  `0a1242ec2b4b92ebfec9f9d79e1134f8ac2f5631`
- evaluation rewrite repair:
  `bce7615e4342bf7fe5cfd5855019202b0642ff9e`
- direct real-supremum theorem:
  `c64b8983e36990c9f9d7730aff55a40b673f446c`
- successful full-repository CI:
  `34350690356`

## 2026-09-09 advance: P-TEL-01

P-TEL-01 has been promoted from `partial` to `proved`.

The final proof chain now matches the source's infinite-horizon discounted
potential-shaping statement rather than only the finite deterministic
telescoping identity.

Key declarations:

- `UEOT.Reward.potential_telescope`
- `UEOT.Reward.shaping_finite`
- `UEOT.Reward.shaping_terminal_corrected`
- `UEOT.V3.RewardInfinite.bounded_potential_integrable`
- `bounded_expected_potential`
- `expectedPotential_bounded`
- `bounded_potential_tail`
- `discounted_one_tendsto`
- `shaping_tendsto`
- `policy_values_affine`
- `policy_values_affine_from_bounded_state_potential`

The final wrapper starts from a common bounded state potential
`ψ : X → ℝ`, policy-induced probability marginals, and a common initial
state. It derives the uniformly bounded expected potential sequence, the
vanishing discounted terminal term, the value identity

`V' p = a * V p - ψ x + c * (1 - β)⁻¹`

and preservation of maximizers for `a > 0`.

Verification evidence:

- analytic infinite-horizon core:
  `d8653802cf2f8a35b332e29b6372c14e73f86ec8`,
  run `34349445220` success
- state-potential expectation bridge:
  `174077e2d1868800c88a16b0b28ae8915aabbcee`
- final source-level wrapper:
  `03aaf987efc74635bba5e4b35fcdaf191f132639`,
  full-repository run `34350610211` success

## 2026-09-09 advance: P-BRG-02

P-BRG-02 has been promoted from `partial` to `proved`.

Source-matched bridge:

- controller/type response `Q_θ^e` is represented by `ReplicationBridge.response`;
- the common reproduction functional `ℛ_e` is represented by
  `ReplicationBridge.replicate`;
- fitness is exactly the composition
  `replicate (response θ)`.

Key declarations:

- `UEOT.V3.SelectionBridge.ReplicationBridge.fitness`
- `BehaviorEquivalent`
- `behavior_equiv_fitness_eq`
- `behavior_equiv_same_multiplier`
- `behavior_equiv_selection_cross_eq`
- `behavior_equiv_positive_ratio_preserved`

Thus equal behavioral/path-law responses cannot be differentially selected by
this bridge alone. Type-dependent mutation, costs, or extra replication
channels remain explicitly outside the theorem, matching the source caveat.

Verification evidence:

- source-matched module commit:
  `fe42139899423c09491ab6fc26d3d54473864b0f`
- tactic repair:
  `70261610de6efc206b1d635661598893b499fc32`
- final repair:
  `e78367705edd19a986df6cd97e666766e5ca556c`
- successful full-repository CI run:
  `34350490496`

## 2026-09-09 advance: P-PRED-02

P-PRED-02 has been promoted from `partial` to `proved`.

Source clauses:

1. measurable deterministic target transformation pushes the predictive kernels;
2. enlarging the protocol family refines the generated sigma-factor;
3. for a countable increasing protocol family, the union sigma-factor equals
   the supremum of the individual factors.

Lean module:

- `UEOT.V3.PredictionRefinement`

Key declarations:

- `pushTarget`, `pushTarget_apply`,
  `canonical_target_pushforward`
- `sigmaCanonical`, `protocol_refinement_sigma_le`,
  `sigmaCanonical_iUnion`
- `pushTargetDependent`,
  `sigmaCanonicalDependent`,
  `protocol_refinement_sigma_le_dependent`,
  `sigmaCanonicalDependent_iUnion`

The sigma-union theorem is slightly stronger than the written source statement:
the identity holds for an arbitrary countable family, so the source's
monotonicity assumption is unnecessary for this equality.

Verification evidence:

- initial theorem commit: `8760dce625550e38aec30beee81bb0f2c0f69618`
- map/iSup elaboration repair: `599ed0201be7cba0d1e91535c6a16fb780b8b9c9`
- noncomputable map repair: `165aa3cb86cfb93938e8f9782457af43147255ac`,
  run `34343887865` success
- dependent-future-space closure:
  `da33abaf7c079472a1d95c15d1b91c3b2b35361c`,
  run `34344159704` success

The two failed intermediate runs are retained as audit evidence.

## 2026-09-09 advance: P-PRED-01

P-PRED-01 has been promoted from `partial` to `proved`.

The exact source permits a countable protocol family with protocol-dependent
future spaces. The current formalization therefore includes both the original
common-codomain layer and the stronger source-matched dependent layer.

Key declarations:

- `UEOT.V3.PredictionAE.common_factorization`
- `UEOT.V3.PredictionAE.canonical_ae_minimal`
- `UEOT.V3.PredictionAE.canonical_ae_sigma_minimal`
- `UEOT.V3.PredictionAE.canonical_kernel_sufficient`
- `UEOT.V3.PredictionAE.canonical_event_condExp`
- `UEOT.V3.PredictionDependent.common_factorization`
- `UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal`
- `UEOT.V3.PredictionDependent.canonical_kernel_sufficient`
- `UEOT.V3.PredictionDependent.canonical_event_condExp`

The source assumes standard-Borel statistic/future spaces. Once the measurable
response kernels are supplied, the Lean factorization theorem only uses the
measurable-space structure, so the formal result is more general at this stage;
it does not claim existence of regular conditional probabilities without the
source hypotheses.

Verification evidence:

- AE factor/minimality work: `b3f7faea...`, `794d1aeb...`
- measurable-space repair: `eb4b6440...`, CI run `34341861473` success
- canonical coordinate kernel: `860193ba...`, run `34342312233` success
- conditional-expectation layer: `986babdd...`
- sigma-notation repair: `9d7b118a...`, run `34342707993` success
- dependent-future-space closure: `d6ac5874...`, run `34343117149`,
  full `lake build UEOT` success (8724 jobs)

The two failed intermediate runs are retained as audit history and were not used
as proof evidence.

## 2026-09-09 advance: P-RES-01

P-RES-01 has been promoted from `pending` to `proved`.

Source statement:

[
\mathcal M_r=
\min_{\subseteq}\{\operatorname{cl}_r(M):M\in\mathcal M_s\}.
]

Lean theorem:

- `UEOT.V3.ClosureResolution.minimal_property_coarse_graining`

Definitions:

- `admissibleMin L A = min(A ∩ L)`
- `resolutionMap L M = min{closure L M | M ∈ M}`

The proof assumes upward closure of the admissible property and explicit
finiteness of the fine admissible family. The source works over a finite carrier,
so this is the source-relevant minimal-existence assumption rather than a new
physical/mathematical restriction.

Verification evidence:

- theorem commit: `09196536122e5976161dbfc5db04f3d0c86731fa`
- successful official-target CI run: `34339206795`

With this promotion, P-RES-01 through P-RES-06 are all source-matched as
`proved`.

## 2026-09-09 advance: P-RES-02

P-RES-02 has been promoted from `pending` to `proved`.

The source has two composition statements:

[
\operatorname{cl}_r\operatorname{cl}_s=\operatorname{cl}_r
]

for nested closure systems, and

[
\mathcal R_{r\leftarrow t}
=
\mathcal R_{r\leftarrow s}\mathcal R_{s\leftarrow t}
]

for minimal families.

Lean module `UEOT.V3.ClosureResolution` now contains:

- `ClosureSystem`
- `closure`
- `closure_comp_of_nested`
- `imageClosure`
- `resolutionMap`
- `minimalFamily_cofinal`
- `resolutionMap_comp`

The formal closure system is represented as a Moore family. On the finite
carrier of the source specification this is equivalent to closure under finite
intersections. The minimal-family theorem assumes the source-relevant finiteness
of the input family and is stronger than the written three-scale form because
the top-scale family need not be separately declared closed.

Verification evidence:

- operator theorem commit: `703bd7972318e440d9c23230729cbde5dba09846`
- syntax repair: `849ca9d470197cedf9a8fd1adedb8b141a8568a7`
- minimal-family theorem commit: `386086c234aeb2adedd8ef0b2083c977e88cdbf2`
- successful CI run for the complete module: `34338838686`

The failed intermediate run is retained and was caused by using the
`Set.mem_sInter` equivalence as a tactic without first unfolding `closure`.

## 2026-09-09 advance: P-CAR-04

P-CAR-04 has been promoted from `pending` to `proved`.

Source statement:

[
\tfrac12 e(S) \le r(S) \le e(S).
]

The Lean module `UEOT.V3.DecoderRadius` proves the metric theorem in a more
general pseudometric setting. `FiberDistances` is the set of all response
distances inside one readout fiber and `DecoderBounds` is the set of all
uniform decoder error bounds. If `e` is their least upper bound and `r` is
the greatest lower bound of decoder bounds, Lean proves

- `diameter_half_le_decoder_radius`
- `decoder_radius_le_diameter`
- `decoder_radius_bounds`

The source TV-distance result is the direct specialization of this metric
argument. No attainment assumption for the decoder infimum is added.

Verification evidence:

- theorem commit: `8115eb3f38c71d9f5b7027e1939448c9d88f408f`
- official-target import commit: `ac5b6db04924db2d52b521ad97c60fba2351f8aa`
- successful CI run after official import: `34337696868`

The earlier green run for `8115eb3f...` is not used as proof evidence because
the new module had not yet been imported by the default `UEOT` target. This
verification gap was detected and repaired before status promotion.

## 2026-09-09 advance: P-RES-06

P-RES-06 has been promoted from `pending` to `proved`.

Lean theorem:

- `UEOT.V3.Resolution.endpoint_equality_iff_unique_active_fibers`

The source fiber-cardinality condition `|π⁻¹(w)| = 1` is represented by
`UniqueFiber π w`: an inhabitant of the fiber exists and every other
inhabitant is equal to it. `Active D w` means that `w` occurs in some coarse
minimal edge. Under surjectivity of `π` and antichain minimality of `D`, Lean
proves that the lower and upper realization endpoints coincide exactly when
every active fiber is unique.

Verification evidence:

- theorem commit: `430202b81bedae8bfb10a0778f9e6071c2080fb5`
- equality-transport repair: `9baa0b95892293167cf212d4875138da4f665a46`
- successful locked/cache CI run: `34337047643`

The failed intermediate run is intentionally retained in Git history; it
reported three equality-transport type errors and led to the repair commit.

## Synchronization note

Only a subset of the earlier 16-module Lean package has been restored to the
public repository so far. Therefore the source-level coverage table above must
not be confused with “number of modules currently present on GitHub.” The
remaining verified historical modules and their documentation will be restored
incrementally without replacing the UEOT manuscript/research materials already
in the repository.

## Completion rule

The complete v3.0 formalization is not finished until all 106 source P-IDs have
been semantically matched and machine-checked. A green build proves the Lean
statements currently imported; it does not by itself prove that every natural
language source statement has been covered.
