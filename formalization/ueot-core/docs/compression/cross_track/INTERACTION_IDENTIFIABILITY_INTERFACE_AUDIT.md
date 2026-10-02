# Interaction-Generated Parent Identifiability — Interface Audit

Status: **LOCAL RESEARCH / IMPLEMENTATION 7ca7e678 / REMOTE FROZEN**

## 1. Provenance and scope

This local mission starts from the previously closed Dual-Isolation / P-MET
branch:

- pushed remote predecessor:
  `origin/compression/cross-track-dual-isolation-local@5968e93bc90e941af27828a89396e76b302b768a`;
- local mission base:
  `5968e93bc90e941af27828a89396e76b302b768a`;
- exact Interaction-Identifiability implementation:
  `7ca7e67803f84d5e703ef12bf6df7479a2b66dac`;
- current research branch:
  `compression/cross-track-interaction-identifiability-local`.

The new branch is local only.  No push, PR, Issue mutation, merge, frozen
ledger mutation, or counted-generator mutation belongs to this mission.

The counted compression core remains

`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 2. Residual inherited from H / X / Parent Binding / Dual Isolation

Track H proves that child/coarse evidence need not determine a unique richer
parent completion.  Dual Isolation introduced an abstract binding lower gain

`beta_bind`

for a supplied diagnostic map.  The P-MET continuation then removed the
forward realization constant for the common-Markov class, yielding the
conditional form

`semantic error <= 2 eta / (beta_bind * kappa_sem)`.

The remaining identification question was therefore:

> Can the diagnostic and its positive lower gain be generated from an actual
> finite family of lower-level interactions/probes, instead of assuming an
> injective diagnostic map?

This mission answers that question for finite candidate assembly spaces.

It does **not** answer the earlier formation question:

> How does the candidate assembly space itself arise from children,
> environment, and lower-level interaction laws?

That H2 candidate-generation obligation remains separate.

## 3. Interaction response family

`InteractionResponseFamily A I Y` contains only

- a candidate assembly type `A`;
- a probe/intervention index type `I`;
- probability response laws `response a i` on observation space `Y`.

No parent kernel, invariant law, semantic metric, objective, viability set, or
Objecthood predicate is stored in this structure.

For one finite nonempty selected probe family `E`, define

`d_E(a,b) = max_{e in E} TV(R(a,e), R(b,e))`.

Lean implementation:

`interactionFingerprintDist`.

Machine-checked properties include:

- nonnegativity;
- symmetry;
- zero iff every selected probe has identical response laws;
- positivity iff at least one selected probe distinguishes the pair.

Thus the diagnostic is no longer a free map: it is generated directly by the
declared interaction-response laws.

## 4. Canonical interaction isolation margin

For a finite nontrivial metric assembly space the implementation defines

`interactionIsolationConorm(F,E)`

as

`min_{a != b} d_E(a,b) / dist(a,b)`.

The central theorem is

`interactionIsolationConorm_pos_iff_pairwiseSeparating`:

`interactionIsolationConorm(F,E) > 0`

iff

`for every a != b, some selected probe e has R(a,e) != R(b,e)`.

This is the finite interaction-generated replacement for an assumed
diagnostic-injectivity premise.

The theorem uses finiteness, nontriviality, and genuine metric separation of
the assembly space.  No infinite-space equivalence is claimed.

## 5. Quantitative inverse identification

`interactionObservationError` is the maximum TV discrepancy between one
candidate's predicted response family and one observed response family on the
selected probes.

The triangle inequality gives

`d_E(a,b) <= err(a) + err(b)`.

Hence if two candidates both fit the same observations to radius `eta`, then

`dist(a,b) <= 2 eta / beta_E`,

where

`beta_E = interactionIsolationConorm(F,E)`.

Public theorem:

`assemblyDist_le_two_observationError_div_interactionConorm`.

The factor two is explicit and comes only from comparing two candidates
through one common observed fingerprint.

## 6. P-MET + Track-S end-to-end composition

For a `CommonMarkovParentRealization`, the previously proved P-MET bridge gives
the forward realization constant exactly as `L_bind = 1`.

The new theorem

`interactionGenerated_commonMarkov_fiberSemanticDiameter`

therefore proves

`fiberSemanticDiameter <= 2 eta / (beta_E * kappaMin)`.

The denominator contains two independent inverse margins:

- `beta_E`: interaction/assembly identifiability;
- `kappaMin`: long-run semantic isolation.

The middle assembly -> parent-row step is supplied by the explicit
common-Markov realization mechanism and P-MET data processing, not by a free
Lipschitz constant.

## 7. P-COMP-02 source-facing bridge

The frozen P-COMP-02 theorem proves

`JS(P,Q) = 0 <-> P = Q`.

The new predicate `PairwiseJSSeparating` requires every distinct assembly pair
to have at least one selected probe with strictly positive JS divergence.

Lean proves:

- `pairwiseInteractionSeparating_of_pairwiseJS`;
- `interactionIsolationConorm_pos_of_pairwiseJS`.

Therefore P-COMP-02 supplies a real source-facing sufficient condition for
positive interaction binding isolation.

This does **not** identify P-COMP-03's scalar composition margin with an
identity fingerprint.  The earlier no-go remains intact: forward stability of
one scalar diagnostic does not imply parent identifiability.

## 8. Probe-set structure

Lean proves two preliminary experiment-design facts.

First, adding probes cannot reduce either pairwise fingerprint separation or
the canonical interaction isolation margin:

- `interactionFingerprintDist_mono_probes`;
- `interactionIsolationConorm_mono_probes`.

Second, every finite separating probe family contains an inclusion-minimal
separating subfamily:

- `exists_minimal_pairwiseSeparating_probeFamily`;
- `minimalSeparatingProbeFamily_positiveIsolation`.

The word **minimal** here is inclusion-minimal only.  No claim is made about
minimum cardinality, minimum experiment cost, or globally optimal
`beta / cost` design.

Those remain later active-experiment-design questions.

## 9. Dynamic observational exactification

The dynamic module proves

- `interactionGenerated_timeSliceSemanticBound`;
- `interactionGenerated_semanticTracking_tendsto_zero`.

Under a fixed finite separating interaction family, common-Markov parent
realization, invariant-law witnesses, and a uniform positive semantic-isolation
floor,

`eta_n -> 0`

implies

`TV(mu(thetaBar_n), mu(theta_n)) -> 0`.

The theorem consumes `eta_n -> 0`; it does not derive a statistical estimator,
sample-complexity bound, learning algorithm, or concentration theorem.

## 10. Identification versus persistence

Two explicit finite witnesses enforce the separation required by the UEOT
Objecthood program.

### Identifiable but not viable

`identifiableResponseFamily` uses one probe whose response is the
assembly-labelled point mass, hence it separates the two Bool assemblies.

`interactionDoomedDynamics` immediately exits the proposed viability domain
`{false}`.  Lean proves

`identifiable_but_not_oneStepViable`.

Therefore interaction identifiability does not imply even one-step viability.

### Viable but not identifiable

`collapsedResponseFamily` assigns the same response law to both assemblies,
so it is not separating.

`interactionSelfLoopDynamics` preserves every state, and Lean proves

`viable_but_not_interactionIdentifiable`.

Therefore viability does not imply interaction identifiability.

These are separation witnesses only.  They do not yet formalize the stronger
distinction between externally controlled viability and endogenous
self-maintenance / Omega-loop closure.

## 11. Candidate formation remains open

The new theory begins with a finite candidate assembly type `A`.

It therefore does not erase the Track-H result that child data alone need not
construct or select a unique richer parent.

Existing frozen interfaces retain their typed roles:

- P-COMP-01: path-integration / conditional nonfactorization;
- P-COMP-02: intervention-response separation;
- P-COMP-05: overlap Booleanization;
- P-COMP-06: physical-carrier -> child-coalition lift;
- P-COMP-07: feasibility window.

None of these, singly or collectively in the current source contracts,
constructs the full candidate assembly space from children/environment alone.

The correct current decomposition is therefore

`candidate formation != candidate identification != persistence`.

## 12. Architecture classification

Recommended classification:

- interaction response/fingerprint and canonical finite `beta_E`:
  **G1 uncounted identifiability bridge**;
- P-COMP-02 -> interaction isolation:
  **G2 retained-adapter synthesis**;
- P-MET + interaction isolation + Track S:
  **G2 cross-track synthesis**;
- probe monotonicity/minimality:
  **G2 experiment-interface support**;
- identifiability/persistence nonimplications:
  **G3 boundaries**.

There is no evidence for a fifth counted generator.

## 13. Residual after this mission

The remaining parent-formation program is now more sharply localized:

1. derive a concrete admissible candidate family from lower-level
   children/environment/interactions rather than supplying `A`;
2. in a real domain, construct the response family and quantitatively compute
   or bound `beta_E`;
3. derive finite-sample bounds for the observational error `eta_N`;
4. optimize probe selection under cost/resource constraints if desired;
5. in parallel, connect the identified parent to P-PER / P-OMG through a
   genuinely endogenous self-maintenance mechanism rather than renaming
   external viability as Objecthood.
