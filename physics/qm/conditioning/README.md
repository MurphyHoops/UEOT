# Finite quantum conditioning reference

This directory implements the registered finite experiment in `frozen_plan.json`
and the boundary witnesses of the 2026-11-11 physics closure contract. It is a
small scientific reference, not a new quantum simulator or a hardware driver.
`positive_chain_plan.json` registers a second complete source with its own
specified action library, so implementation and cost are demonstrated on the
same conditioned model rather than inferred from an unrelated convex example.

## Reproduce

From this directory, with Python, NumPy, SciPy and SymPy available:

```bash
python -m unittest -v test_finite_conditioning.py
python exact_witnesses.py --output exact_witnesses.json
python run_reference.py --output runtime_results.json
```

For one bounded execution with source hashes, dependency versions, actual logs
and failure details (including a distinct infrastructure-timeout status):

```bash
python verify_runtime.py --output-dir /absolute/path/to/receipts
```

Both scientific runners also accept `--output-dir` independently. The exact
certificate includes an additional noncommuting local source whose S, T and all
Kraus matrices are rational, and rational lower bounds for every T3 effect checked
by the two-dimensional principal-minor criterion.

The first and third commands check numerical and record-semantics behavior. The
second independently reads the rational registered model and checks exact
symbolic identities. Its certificate states the checked finite scope. None is
described as a replacement for the general Lean theorem.

## Mathematical and operational scope

- A visible outcome maps to a tuple of hidden Kraus matrices. Hidden indices are
  summed inside that branch and never become observable record labels.
- Every node has a complete original instrument and one child per visible
  outcome. An accepted leaf has effect I; a rejected leaf has effect 0. The
  backward recursion uses the actual frozen future tree.
- With positive source acceptance, the initial state is filtered by sqrt(H0).
  Transformed Kraus matrices are sqrt(Hchild) K Hparent^(-1/2), using the inverse
  only on support. A complement Kraus is inserted under an original visible
  label to complete the unused subspace. Two different completions are checked:
  they agree on the support task and need not agree on the full input space.
- Zero acceptance returns no conditional state. Small positive eigenvalues are
  not silently deleted. An ambiguous/ill-conditioned inverse raises an explicit
  numerical error; it needs an exact support certificate or higher precision.
- The endpoint comparison is the entire original visible-record and terminal
  quantum CQ state. Rejected original records remain present as zero blocks in
  the conditioned law and as actual failures in the source law.
- A new controller, acceptance event, or inserted intervention changes the
  experiment and requires new backward effects. Intermediate filtered states
  are not labelled as the original prefix-only posterior.

## Implementation and costs

`common_observation_mixture` compares labelled Choi families and one common
probability vector on the entire supplied observation fibre. LP output is only
a numerical result. Exact positive weights and exact negative separation
functionals are checked separately. The claim is one-step full-space instrument
randomization; it is not arbitrary-circuit controllability. Support and fixed
initial-state witnesses carry their own narrower scopes.

For independent repeatable preparation, the retry cost is the actual expected
cost of one attempt divided by its acceptance probability. Failed resets can be
charged separately. The T3 source may stop early on failure, so action cost is
`(1 + m1 + m2) / p`, not `3 / p`. All physical initialization, reset, ancilla,
calibration and transformed-action costs remain separate; no resource advantage
is asserted. The scaled filter has success probability `p/c`, with
`c >= ||H0||`. Normalized filtering of an unknown arbitrary state is generally
nonaffine. The scalar-effect exception is retained. A rank-one filter can also
be replaced deterministically for the system marginal on positive-probability
inputs; a Bell-state counterexample shows that this replacement fails when the
correlated external reference is retained. Those two tasks are not identified.

## Witnesses

The checks include noncommuting T3 with two visible successes and
`p = 117/4096`; hidden-Kraus splitting invariance; singular positive mass and zero
mass; diagonal classical degeneration; label swap with unchanged summed channel;
shared-observation infeasibility; a legal target outside a specified action
library with a fixed-input gap; variable stopping cost; scaled filtering;
unknown-input nonlinearity; and sharp rare-event conditional error amplification.

The exact T3 local square-root/inverse/intertwining identities imply the complete
visible path equality by telescoping and summing hidden indices. The numerical
runner also evaluates all fifteen original visible leaves, including all eight
accepted length-three records.

No hardware observations, physical model identification, stabilized/diamond
bound, unbounded stopping result, or unique quantum-sector selection is claimed.

## Two complete model scopes

The non-scalar T3 source has acceptance `117/4096`. Its singleton original-only
action library cannot realize the zero-failure conditional instrument: on I/2
the original failure probability is exactly `23/32`, and it is at least `5/8`
on every density. The separating observable is minus that labelled probability.
This excludes one-step randomization in that stated library, not added heralding
or arbitrary circuits. Scaled filtering still incurs the declared preparation
and retry responsibilities.

The positive chain has success Kraus `Z/2,X/2` and one visible failure branch
with two hidden Kraus `I/2,I/2`. Its three-step acceptance is `1/8`, and
`H_t = (1/2)^(3-t) I` leaves the initial state unchanged. Its own allowed library
contains the deterministic labelled Pauli actions; weights `1/2,1/2` realize
the actual labelled conditional instrument. All eight complete accepted CQ
blocks are checked. The source's expected action cost per accepted output is
`14`; the target uses `3` Pauli actions. With per-action randomization overhead
`r`, the action-only comparison is `3*(1+r)<14`. Unmeasured preparation, reset,
ancilla and calibration costs are not silently set to zero for a physical
advantage claim.

The two off-support completions of the singular fixture have record distance
one on a complement input, even though they agree exactly on supported inputs.
Approximate preparation with complement leakage therefore cannot discard that
part of the error model.
