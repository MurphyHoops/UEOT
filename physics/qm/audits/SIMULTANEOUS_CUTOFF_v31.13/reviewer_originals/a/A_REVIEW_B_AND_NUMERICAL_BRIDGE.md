# A independent review of B and the large finite numerical bridge

Date: 2026-11-12 (Asia/Shanghai). Reviewer: native research agent A.
Review type: internal AI scientific review, not external human peer review.
Baseline: `cb17211653fde30aa50e0e9848798a6a5b3b3f12`.

## 1. Strong claim: the source domain and energy estimate are legitimate

I reviewed B's `B_SIMULTANEOUS_GALERKIN.md`, particularly P-MICRO-06 and its
revised energy proof. The positive-frequency Hamiltonian has an explicitly
verified infinitesimally n-bounded symmetric perturbation. Its use of
Kato--Rellich is stated as an external standard theorem; the zero-frequency
quadrature example has its own canonical self-adjoint realization. No
positive-frequency domain theorem is silently evaluated at omega=0.

The original route from domain invariance to differentiating arbitrary
finite-energy expectations would have needed a careful form argument. The
delivered proof now avoids that possible gap. It first derives the commutator
and differential inequality for each finite matrix, where differentiation is
unproblematic. It then uses the independently proved finite-support Galerkin
convergence from P-MICRO-07. Positive G expectation is lower semicontinuous
under trace-norm convergence, transferring the same bound to the exact output.
A second limit from normalized low-spectral inputs covers arbitrary normal
finite-energy inputs, whose projected means are bounded by the original mean.

This is not circular: P-MICRO-07 uses finite support, self-adjoint unitary
suffixes, preservation by H0, and the algebraic bound B²<=G+I. It does not use
the energy-growth theorem that the subsequent limit establishes. The homogeneous
prefix formula retains its mass m; an aggregate level mean is not substituted
for every rare normalized branch.

**Verdict:** the source-domain and energy claims are sound with this explicit
dependency order. The forward reference from the energy section to the later
finite-support theorem must remain visible when condensed into the book.

## 2. Strong claim: the true compressed generator approximates the exact process

I attacked P-MICRO-07 by checking whether the proof confuses a state-projection
tail with a generator error, leaves an exact uncontrolled prefix inside a
norm estimate, loses the reference, or charges the initial projection at each
step. None of those substitutions is made in the current proof.

The generator is genuinely `J_K† H J_K`, with K=N+2L. At each finite Duhamel
iteration the true evolution remains on the left. To its right are only
finite-support B actions and G-preserving reference propagators. The first L
orders are the same in the exact and finite expansions, and both finite
remainders have the same product bound. This gives `2c_(L+1)` without an
unproved infinite Dyson expansion.

For finite piecewise source segments and phase insertions, the reference
propagators U0(t,s) still preserve every G carrier. The ordered scalar exposure
integrals, or the equivalent multinomial allocations among intervals, give
the same total-exposure coefficient. A physical phase kick is not replaced by
an unspecified energy-changing intervention. Every finite reference is
retained by tensoring the bounded restricted operator difference with identity.

The boundary residual also follows directly from the generator: only the two
outward blue edges remain, with weights K+1 and K. K=0 explicitly omits the
second edge. Its trace-distance version includes the essential sqrt(m) from
an unnormalized purification. This fits A's fixed-direction F-prefix/E-suffix
theorem for state-dependent instruments. The simpler Q-weighted path formula
is used only for the independently established scalar-labelled-unitary source.

The initial physical filtering is charged once and retains a separate failed
preparation block with the correct conditioned reference. All later quantum
dynamics on the projected input are covered by the new generator bound.

**Verdict:** P-MICRO-07 and the complete-record connection are sound in the
specified finite protocol and Hamiltonian families. No assertion about an
infinite horizon or arbitrary intervention family follows.

## 3. Independent finite B computations and the attribution correction

The B checker uses explicit displacement matrix elements for the exact force
oracle; a larger finite exponential is not silently promoted to an infinite
solution. For the more general Rabi stress cases, both finite carriers are
marked as finite diagnostics and their relation to the exact dynamics comes
from the analytic bound. The source-derived boundary residual and scalar
rational enclosures have the correct formulas. High precision is kept distinct
from an interval certificate of the numerical output.

I found one execution-attribution defect in the first reusable checker: it
fixed `actor = native research subagent B` in all reports. That identified B's
own run truthfully but would misidentify later root/CI runs. B changed it to
`checker_author`, added actual execution environment fields, preserved the
original script and receipt, and actually reran the affected checker. The final
57-check receipt remains scientifically unchanged. This resolves the defect
without rewriting the first execution identity.

## 4. Review of root's interval predictor

I read `physics/qm/simultaneous_cutoff/interval_predictor.py` independently of
its output. It uses the genuine finite force generator at K=4175, acting on the
stated entangled G=1 input, with phase pi/3 and a calibrated rational nominal x.

The operator-norm estimate is valid:
`||H_K|| <= |x|(sqrt(K)+sqrt(K+1)) <= 2|x|sqrt(K+1) <= 13`.
The 100th-degree Taylor remainder is therefore bounded by
`R=13^101/101!/(1-13/102)`. Each later ratio in the tail is at most 13/102.
Exact phase operations do not amplify the error. A word with k force calls has
polynomial-versus-exact finite vector error at most `(1+R)^k-1`, because each
polynomial has norm at most 1+R.

The integer interval arithmetic rounds every multiplication and rational
division outwards, including negative operands. Integer square roots enclose
the oscillator couplings and sqrt(2), sqrt(3). The complex `-i` operation and
the phase `(1-i sqrt(3))/2` preserve the stated interval enclosure. The recursive
division by j gives the correct factorial Taylor coefficients. Missing sparse
coordinates are exactly zero in the finite polynomial, with its whole
exponential tail bounded separately.

A Euclidean radius encloses the exact polynomial vector around its chosen
integer centre. Adding the operator Taylor bound yields distance at most e to
an exact unit vector. The centre is checked nonzero, and normalizing it adds at
most e again, so its joint pure-state trace distance is at most 2e. The output
stores integer amplitudes and their exact squared norm; it does not rely on a
floating normalization. Summing the per-word bounds with exact Q weights gives
a complete-CQ numerical bound. The source-failure and preparation-failure
records are retained with zero mass because this particular input already lies
below the physical filter.

This is an output certificate for the declared entangled input. The uniform
analytic theorem concerns the *exact finite predictor* on a larger input family.
It does not automatically confer this same arithmetic budget on every possible
input or every numerical algorithm.

## 5. Output readback and pending final identity binding

My independent integer readback verified the four encoded state normalizations,
support coordinates, exact Q weights, Taylor remainder and weighted numerical
error. The inspected development output had bound
approximately `7.8377916629e-48`, safely below the reserved `1e-8`.

It also caught a concrete input-identity mismatch: that numerical receipt had
consumed an earlier calibration certificate, while C subsequently updated the
holdout protocol and certificate file. The nominal x remained the same, so this
does not refute the numerical result. The final predictor receipt must still
bind the actual final consumed calibration, or retain the earlier consumed
snapshot at its original identity. Root was notified before integration.

`verify_interval_output.py` preserves this check independently of the producer.
The initial failed identity readback is retained under `development_attempts`.
The final accepted readback and its exact sources will be listed in the final
A source-review JSON. No unobserved rerun or remote status is asserted here.

## 6. Limits

These are analytic proofs, independent scientific source review, finite
diagnostics and exact arithmetic checks. They are not new Lean declarations,
device calibration, or empirical closure. Physical action implementability,
ideal detector/filter membership, unknown-input preparation costs, complete
OPT reconstruction, independent quantum selection and the broader long-term
physics tasks remain at their stated separate statuses.
