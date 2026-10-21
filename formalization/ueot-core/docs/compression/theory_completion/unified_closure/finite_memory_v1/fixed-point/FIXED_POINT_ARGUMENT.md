# Bounded greatest fixed point on observed supports

Status: **ACTUAL_LEAN_BUILD_AND_NATIVE_REVIEW_CLEAR**. The new
`FiniteSupportFixedPoint.lean` source passed the
[complete build](../actual-execution/full-build-01/FULL_BUILD_RECEIPT.json) and
[independent native execution review](../independent/ACTUAL_BUILD_NATIVE_REVIEW.md).
This mathematical note does not replace the raw receipts or canonical publication gates.

## Mathematical input and result

Fix a finite microscopic state type `X`, any observation type `Y`, a map
`q : X → Y`, a qualitative transition relation `R : X → A → X → Prop`, and
certification `C : X → A → Prop`. The fixed-point argument itself does not
require finiteness of `A`: the finite carrier of refinement is the set of
supports. Additional action finiteness needed by other production endpoints
is retained by those endpoints.

The arena contains exactly the nonempty sets contained in a single observation
fiber. Its cardinal `M = supportArenaCard q` counts supports, not microscopic
states. One successor is the union of all `R` successors of the current support
which have the next recorded observation. `supportPre` requires a single action
which certifies every current state and returns every nonempty observed
successor to the candidate family.

Starting at the arena, the family decreases under refinement. If no adjacent
iterates agree through index `M`, each refinement deletes at least one support,
and the `(M + 1)`st deletion contradicts the initial cardinal `M`. Equality of
adjacent iterates propagates under the same predecessor operator. Therefore
the iterate at `M` is fixed, without supplying fixed-point existence as a
hypothesis.

Every cutoff `K ≥ M` gives the same fixed point. This permits a computable
upper bound, such as `2 ^ Fintype.card X - 1`, to replace the classical arena
enumeration when invoking the existing executable finite-horizon checker.

Any postfixed family lies in every iterate by induction, so this fixed point is
greatest. A separate induction identifies the iterates with the existing
`viableWith` recursion for the fixed relation and certification at every
absolute starting time. Consequently membership at the single cutoff `M` is
equivalent to viability at every finite horizon.

## Total memory and source boundaries

`SupportMemory q` is the subtype of sets which are empty or are arena supports.
The empty value is needed for total behavior at impossible recorded observations.
The source proves that its cardinal is exactly `M + 1`, and its injection into
all subsets of `X` gives `M + 1 ≤ 2 ^ Fintype.card X`. This counts every value of
the total controller memory, including unreachable values.

These definitions alone do not identify `R` with any actual transition PMF or
prove occupancy for a controller. The source bridge must establish the actual
PMF support equivalence at each time, the certification equivalence, the same
initial support, and the controller's own support/history law. Qualitative
support homogeneity permits time-varying positive probability weights; it does
not identify them with a fixed numerical killed matrix. A fixed fallback is
needed for the complete policy to be finite memory, and zero uncertified-row
occupancy needs further physical assumptions before it implies physical safety.

## Reuse decisions

The new set successor is related extensionally to the existing computable
`finiteRelationSuccessor`. No second executable finite-horizon checker is
introduced. The existing relation checker remains the algorithmic entry point
once exact decidable source data have been supplied.

Existing `ViabilityKernelIntertwining.exists_finite_viability_fixedpoint` has a
finite cardinal-drop proof for a numerical exact control quotient on individual
physical states. Its state-operator assumptions cannot directly instantiate
the arbitrary qualitative support operator. The new private proof uses the
same general `Finset.card_lt_card` fact on a different finite carrier; the
public result supplies the observation-support cutoff and its exact viability
identification. Existing partition stabilization is also typed specifically for
setoids and is not used as an artificial representation of support families.

## Public endpoints imported by the production root

- `relationSuccessor_mem_arena` and `initialSupport_mem_arena`;
- `finiteRelationSuccessor_coe_eq_relationSuccessor`;
- `supportPre_mono`, `supportIterate_subset_arena`,
  `supportIterate_succ_subset`;
- `mem_supportIterate_iff_viableWith`;
- `supportWinning_fixed`, `supportWinning_subset_arena`,
  `supportWinning_step`, `supportWinning_greatest_of_postfixed`;
- `supportIterate_eq_winning_of_card_le`;
- `supportWinning_iff_all_horizons`;
- `supportMemory_card`, `supportArenaCard_add_one_le_pow`.

Compiler status and independent review must be recorded separately with their
actual source identities. This note deliberately makes no empirical claim.

## Focused execution checkpoint

The first Mac compilation reported four elaboration/simplification failures:
the cardinality induction base left reflexivity open; the memory instance
needed its subtype exposed; the empty-arena exclusion needed an explicit
contradiction; and the cardinality equivalence needed `Fintype.card_coe` before
unfolding its finite set. These were repaired without changing the mathematical
claim. The original failed attempt is retained by the root execution archive.

The root's second focused Mac run completed successfully with exit code zero
in 3.664 seconds and no warnings. The checked source SHA256 is
`f222dd852190edec16e90ab710db56a847e2820f1d2566a5a3b3df3f04fd31e2`.
The independent mathematical review found the bounded descent, exact cutoff,
arbitrary observation type, and whole-memory cardinal accounting clear.
Production import, full integration, native export, and release acceptance
remain separate gates; they are not inferred from this focused result.
