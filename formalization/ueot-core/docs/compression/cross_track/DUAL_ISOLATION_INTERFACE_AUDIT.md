# Dual Isolation Theory — Interface Audit

Status: **LOCAL RESEARCH / IMPLEMENTATION 648a9b65 / REMOTE FROZEN**

Baseline:

- canonical remote source base:
  `origin/main@5c62f2f1db479b9f0f8e725ced6588b59d0fe42d`;
- local Parent-Binding closure base:
  `2a69536ea48d296e77922ca8a16057f971e85980`;
- exact Dual-Isolation Lean implementation:
  `648a9b65ce006d8717d559383010105a749a30f8`;
- counted Core remains frozen at
  `{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

No push, remote branch, PR, Issue mutation, ledger mutation, or counted-core
mutation belongs to this local mission.

## 1. Scientific residual inherited from S / H / X / Parent Binding

Track H established that child/coarse evidence does not in general determine a
unique richer parent completion. Track S established a canonical finite-state
long-run semantic isolation margin

`kappa_sem = l1ResidualConorm(P)`

whose positivity is equivalent to unique invariant probability semantics.
Track X then proved the finite parent-semantic stability form

`semantic defect <= kernel defect / kappa_sem`.

Parent Binding pushed the remaining kernel defect down one level:

`kernel defect <= L_bind * assembly defect`.

The remaining inverse problem was therefore:

> when does lower-level diagnostic evidence identify the richer parent
> assembly, and with what quantitative inverse stability?

## 2. Binding isolation

The new structure

`BindingIsolation diagnostic beta`

contains only

`beta > 0`

and

`beta * dist(a,b) <= dist(diagnostic a, diagnostic b)`.

It contains no parent kernel, invariant law, GOA, objective, Objecthood,
selection, or final semantic conclusion.

It is therefore a lower-gain / anti-collapse certificate for the diagnostic
map, not a circular restatement of parent-semantic stability.

Lean proves:

- `BindingIsolation.injective`;
- `assemblyDist_le_two_mul_error_div_bindingIsolation`.

If two candidate assemblies both lie in one diagnostic ball of radius `eta`,
then

`dist(a,b) <= 2 * eta / beta`.

The factor two is the ordinary triangle-inequality cost for comparing two
candidates through one observed diagnostic centre.

## 3. Dual-isolation theorem

Combining:

1. binding isolation `beta`;
2. Parent-Binding realization regularity `L_bind`;
3. Track-S residual isolation `kappa_min`;

gives the pairwise and fibre-wide theorem

`semantic diameter <= 2 * L_bind * eta / (beta * kappa_min)`.

Public theorem:

- `dualIsolation_fiberSemanticDiameter_normalized`.

This exposes two mathematically distinct inverse margins in one denominator:

- `beta_bind` controls whether lower-level evidence can distinguish parent
  assemblies;
- `kappa_sem` controls whether the parent dynamics determine stable long-run
  invariant semantics.

`L_bind` remains the forward sensitivity connecting assembly realization to
parent dynamics.

## 4. Canonical finite binding conorm

For a finite nontrivial metric assembly space the implementation defines

`bindingIsolationConorm diagnostic`

as the minimum, over distinct assembly pairs, of

`dist(D a, D b) / dist(a,b)`.

Lean proves:

- nonnegativity;
- the canonical lower-gain inequality;
- `bindingIsolationConorm_pos_iff_injective`;
- `canonicalBindingIsolation_of_injective`;
- `bindingIsolation_le_bindingIsolationConorm`.

Hence, in the finite metric setting,

`bindingIsolationConorm(D) > 0 <-> D is injective`,

and the canonical conorm is the greatest admissible binding-isolation
constant.

This is deliberately parallel to Track S's use of a canonical residual
conorm, but the operators and semantic roles are different.

## 5. Two isolation margins are not interchangeable

`semanticIsolation_does_not_imply_bindingIsolation` reuses the Track-X X1
reset-kernel witness.

The witness has:

- two distinct assembly realizations;
- a constant lower-level diagnostic, so all evidence collapses;
- no positive `BindingIsolation` certificate for any `beta`;
- positive semantic residual conorm for both parent kernels;
- invariant semantics separated by TV distance exactly one.

Therefore

`kappa_sem > 0`

does not imply

`beta_bind > 0`.

Stable semantics conditional on a chosen completion cannot solve parent
identification from collapsed evidence.

## 6. P-RES-06 exact specialization

P-RES-06 already contains a real exact realization-identifiability theorem:
equality of the lower and upper realization endpoints is equivalent to every
active coarse atom having a unique microscopic preimage.

The Dual-Isolation module uses that theorem directly in

- `resolutionEndpointCollapse_exactActiveRealization`;
- `resolutionEndpointCollapse_parentSemanticDiameter_zero`.

If all richer parent completions in the relevant child fibre realize the same
active coarse atom, endpoint collapse forces exact microscopic realization
equality. Parent Binding then yields

`fiberSemanticDiameter <= 0`.

This is a genuine exact domain branch. It does not claim that arbitrary
P-COMP parent completions are automatically P-RES resolution fibres.

## 7. P-CAR-04 quantitative specialization

P-CAR-04 gives the exact radius/diameter relation between within-readout-fibre
response ambiguity and optimal decoder radius.

The new theorem

`assemblyDist_le_two_decoderRadius`

specializes this to

`assembly distance <= 2 * decoder radius`.

Then

`decoderRadius_parentSemanticDiameter`

gives

`semantic diameter <= L_bind * (2 r) / kappa_min`.

Thus the abstract assembly diameter can already be replaced, in this domain,
by an existing frozen source-facing quantity.

## 8. Dynamic observational exactification

Parent Binding already supplied a distinct dynamic route through the M-TC
weighted development envelope.

Dual Isolation adds the complementary observational route:

- `dualIsolation_timeSliceSemanticBound`;
- `dualIsolation_semanticTracking_tendsto_zero`.

If the diagnostic error radius `eta_n` tends to zero while `beta_bind` remains
positive, `L_bind` remains fixed, and the semantic residual conorm has a
uniform positive lower bound, then parent invariant semantics converge in TV.

No theorem claims that observations automatically become more accurate. The
assumption `eta_n -> 0` is explicit.

## 9. Sharp finite benchmark

`DualIsolationBenchmark.lean` supplies a concrete two-completion benchmark.

Machine-checked constants:

- canonical binding conorm `beta_bind = 1`;
- parent realization Lipschitz constant `L_bind = 1`;
- semantic residual conorm `kappa_sem = 1` for each completion;
- midpoint diagnostic radius `eta = 1/2`;
- actual invariant-law TV distance `= 1`.

The dual-isolation theorem therefore returns the bound

`2 * 1 * (1/2) / (1 * 1) = 1`,

which is attained exactly by the benchmark. The constant chain is therefore
sharp on this finite witness.

## 10. P-MET-01 realization bridge

P-MET-01 supplies genuine TV data processing:

- measurable readout pushforward is nonexpansive;
- composition with one common Markov kernel is nonexpansive;
- bimeasurable equivalence is an isometry.

The generic Parent-Binding interface alone still does **not** imply
`L_bind <= 1`.  However the local continuation now supplies an explicit
mechanism-level guard:

`CommonMarkovParentRealization`.

It requires:

- an assembly-level probability law `baseLaw a`;
- an assembly metric that dominates base-law TV;
- for each parent state `x`, one common Markov channel `channel x`;
- an exact identity saying every realized parent row is that channel applied
  to `baseLaw (repr p)`.

P-MET-01 then proves

`crossRowTV <= assembly distance`

and therefore constructs a `ParentBindingLipschitz` certificate with

`L_bind = 1`.

The resulting supplied-beta and canonical-beta semantic bounds no longer
contain an externally supplied forward constant.

This is not a universal contraction theorem for arbitrary parent kernels. The
common-channel realization identity and metric-TV domination remain explicit
domain obligations.

The sharp two-completion benchmark has also been re-instantiated through this
mechanism using the identity Markov kernel.  Its `L_bind = 1` is therefore now
derived by P-MET data processing rather than only hand-certified.

## 11. Architecture classification

Recommended local classification:

- `BindingIsolation` / finite canonical binding conorm: **G1 uncounted
  identifiability bridge**;
- dual-isolation semantic bounds: **G2 cross-track synthesis**;
- P-RES-06 and P-CAR-04 routes: **G2 retained-adapter synthesis**;
- P-MET common-Markov realization: **G2 mechanism bridge**;
- `semanticIsolation_does_not_imply_bindingIsolation`: **G3 boundary**;
- sharp finite benchmark: **out-of-sample bridge stress test**.

There is no evidence here for a fifth counted generator. The canonical
four-generator core remains unchanged.

## 12. Remaining scientific residual

The next unresolved step is no longer another abstract `epsilon / kappa`
bound. It is to derive, in a concrete lower-level interaction model,

1. the diagnostic map itself;
2. a positive or computable `beta_bind`;
3. in each concrete domain, prove the common-channel (or another justified)
   assembly-to-parent-kernel realization identity; P-MET then supplies
   `L_bind = 1` for that mechanism;
4. eventually the constitutive persistence / Omega-loop certificate of the
   formed parent object.
