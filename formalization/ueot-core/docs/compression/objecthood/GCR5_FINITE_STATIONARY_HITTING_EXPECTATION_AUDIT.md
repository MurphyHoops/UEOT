# GCR5 — Finite Stationary A.S.-Hitting to Finite Expectation Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`, GCR3 `9c75f5c`, GCR4 `2aec086`
Counted-core impact: **NONE**

## Scope

GCR5 proves the exact quantitative implication frozen by #243:

> on a finite homogeneous Markov chain, almost-sure eventual hitting of `K`
> implies finite canonical expected hitting time.

It then specializes this theorem to the deterministic stationary controlled
kernel produced by GCR4.  No corresponding statement is asserted for arbitrary
nonstationary/history-dependent policies.

## Never-hit probability and restart semantics

`neverHitProb Q x K` is the exact mass of `neverHitSet K` under the homogeneous
Ionescu--Tulcea law started from `x`.

The file proves:

- `survivalProb_tendsto_neverHitProb`: finite survival probabilities decrease
  to the exact never-hit mass by continuity from above;
- `neverHitProb_first_step`: outside `K`, the never-hit probability is harmonic,
  `q(x) = ∫ q(y) dQ(x,y)`, derived from the existing homogeneous restart law;
- `neverHitProb_zero_support_closed`: zero never-hit mass is preserved by every
  positive-probability one-step successor;
- `neverHitProb_zero_ae_successor`: the stronger a.e. form needed under the
  kernel integral.

No recurrence-class theorem, irreducibility assumption, or spectral argument is
used.

## Finite-state uniformization

For every state `y` with zero never-hit mass,
`survivalProb Q y K n -> 0`.  Since `X` is finite,
`exists_uniform_half_survival_horizon` uses finite conjunction of eventual
properties to obtain one common horizon `N` such that

`survivalProb Q y K N <= 1/2`

for every zero-never-hit state `y`.

`survivalProb_add_uniform_horizon_le_half_mul` then combines this common block
with the exact first-step survival recurrence and the a.e. zero-never-hit
closure to prove the restart contraction

`survivalProb Q x K (m + N) <= (1/2) * survivalProb Q x K m`

for all `m` whenever `neverHitProb Q x K = 0`.

## Tail-sum bound

Rather than introducing a separate graph-distance or spectral-radius layer,
GCR5 works directly with the existing P-REC tail-sum representation.

- `truncatedExpectedHittingTime_add_horizon_le` proves

  `T_(M+N) <= N + (1/2) T_M`.

- `truncatedExpectedHittingTime_le_two_mul_horizon` uses strong induction to
  derive the uniform bound

  `T_M <= 2 N`

  for every finite truncation.

- `expectedHittingTime_ne_top_of_ae_eventually_hits_finite` combines
  a.s.-hitting -> zero never-hit mass, a positive common horizon for a
  non-target initial state, and the existing theorem
  `expectedHittingTime_eq_iSup_truncatedExpectedHittingTime` to conclude

  `expectedHittingTime Q x K != infinity`.

Thus the finite expectation conclusion comes from an explicit geometric block
tail bound, not from a hidden finite-expectation assumption.

## Public GCR5 stationary conclusion

`stationary_expectedHittingTime_ne_top_of_ae_eventually_hits` proves:

- finite controlled state/action spaces;
- deterministic stationary policy `pi : X -> A`;
- if the canonical `stationaryTrajMeasure P pi (PMF.pure x)` reaches `K`
  almost surely;
- then `expectedHittingTime (stationaryKernel P pi) x K != infinity`.

This is exactly the missing implication required after GCR4.  It does not yet
package the full arbitrary-causal-to-stationary completeness theorem; that is
GCR6.

## Assumption audit

GCR5 uses:

- finite `X` for uniformization across states;
- homogeneous Markov semantics;
- measurable-singleton state structure already present throughout AR/GCR;
- no compactness/Feller continuity;
- no irreducibility or recurrence assumption;
- no externally supplied positive transition lower bound;
- no spectral gap;
- no prior finite expected hitting assumption.

The finite action/measurable action assumptions occur only in the final
controlled stationary specialization and are not needed by the generic finite
Markov theorem.

## Boundary discipline

GCR5 does **not**:

- claim arbitrary nonstationary a.s.-hitting has finite expectation;
- yet state `GeneralCausalToStationaryCompleteness`;
- yet prove set-level equality of general-causal and stationary repairable
  classes;
- yet identify the maximal AR certificate basin with that class;
- mutate S/H, counted Core, ledger, coverage, or the four-generator core;
- enter RH/RLSR/EC/OC/AP;
- claim a fifth generator or complete autopoiesis.

## Local validation

The exact local candidate passed the full stage gate:

- focused Lean compile of `FiniteStationaryHittingExpectation.lean`: **PASS**;
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS** (`9109/9109` jobs);
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**;
- representative `#print axioms` for `neverHitProb_first_step`,
  `survivalProb_add_uniform_horizon_le_half_mul`,
  `expectedHittingTime_ne_top_of_ae_eventually_hits_finite`, and
  `stationary_expectedHittingTime_ne_top_of_ae_eventually_hits`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**;
- exact-candidate Track-O validation: **PASS — 3 changed paths**;
- final `git diff --check`: **PASS**.

No research branch is pushed during GCR5.  The first research push remains after
cumulative local closure of GCR0--GCR8.
