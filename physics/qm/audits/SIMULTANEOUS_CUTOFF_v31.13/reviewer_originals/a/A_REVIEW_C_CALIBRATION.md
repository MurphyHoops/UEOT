# A independent review — Joint calibration and nominal prediction

Research baseline: `cb17211653fde30aa50e0e9848798a6a5b3b3f12`,
v31.12 / Kernel 1.12 / book 3.9. Review author: native research agent A.
This is internal AI cross-review, not external human peer review.
The reviewed implementation and complete C proof are under
`iteration_v31_13/research_c`; root owns integration into the public repository.

## Verdict

**PASS within the explicit ideal-model, fixed-sample and finite-reference
contract.** No blocking mathematical defect remains in the reviewed C
calibration proof and nominal complete-output bound. This does not verify a
physical device, unknown detector offset, pulse drift, or an arbitrary
numerical evaluation of the finite channel. Final execution identities are
separate from this source/proof review and must bind the actual consumed bytes.

## Strong claim 1: calibrated nominal prediction without access to truth

The relevant quantifier is one data-selected nominal area and one lawful
policy, valid for every parameter in the admitted joint confidence set. The
physical policy Q is in fact fixed before calibration. The finite predictor
receives the rational nominal area, not the hidden generating value. The
same q determines both the success coefficient `s=1-q/2` and the complete
source record law; introducing a product confidence set for q and x does not
sever that physical relation.

I checked the Bernoulli scaling: a q half-width of 0.01 is a failure-frequency
half-width of 0.005, so 120000 trials give `2 exp(-6)`. One million drive shots
with probability half-width 0.002 give `2 exp(-8)`. Their union bound is valid
without independence between the two confidence events; independent trials
within each stream remain an essential assumption. The fixed-n proof bounds
unconditional coverage failure, and hence the probability of issuing a
certificate made invalid by that calibration failure. It does not establish
coverage conditional on the program issuing a certificate, and it cannot be
reused after sampling repeatedly until admission.

The signed force tester is derived from `|-i x>` and observes `P<=0`, giving
`Phi(2x)`. The rational inversion and deterministic grid representative include
the actual outward endpoint and grid errors in Delta_x. The implementation
rejects an interval not wholly contained in the frozen design window; it does
not trim adverse parameters to manufacture a precision pass. The confidence
set's natural intersection with physical probability domains is distinct from
such design-window trimming.

The independent code review covered the Gaussian integral variable, its
negative-argument symmetry, alternating-series remainder, Machin identity,
integer radical bounds, monotone inverse enclosures and grid displacement.
No raw calibration branch or unexpected outcome is silently discarded. The
analyzer reads the declared streams and plan, rather than synthetic provenance.

The resulting parameter estimate is used in the correct comparison order:
true infinite process, nominal infinite process, then the true compressed
Hamiltonian predictor. Exact infinite words preserve `D(X)` and `||X psi||`,
and `Tr X^2 rho<=6` on the filtered input. The mean force-call count of Q is
one. Hence the common-parameter contribution is `sqrt(6) Delta_x`, with no
unauthorized use of the invariant in compressed prefixes. The independent
K=1 counterexample C-MICRO-03 prohibits that latter shortcut.

## Strong claim 2: identifiability and held-out rejection

The earlier broad detector-bias obstruction required correction after adding
the two-dose held-out tester. C's current proof makes the required distinctions:

1. With one-dose access and additive readout `P_observed=P+b`,
   `Phi(2x-sqrt(2)b)` is unchanged by
   `(x,b)->(x+c,b+sqrt(2)c)`. This access alone does not identify x.
2. With a shared, dose-independent b, the second response
   `Phi(4x-sqrt(2)b)` breaks that symmetry. From the inverse arguments z1,z2,
   `x=(z2-z1)/2` and `b=(z2-2z1)/sqrt(2)`; the two ideal parameters are jointly
   identifiable. The current analyzer still assumes b=0 and does not refit
   this nuisance from holdout data.
3. Allowing independent setting biases b_k restores the corresponding
   k-dose symmetry. That is a larger competing model, not a nonidentifiability
   theorem for the shared-bias protocol.

This correction changes the scope of a negative conclusion; it is not
additional experimental evidence. Current C source and prose state the
access-dependent claims correctly.

The different-setting prediction uses `Phi(4x)` from the single-dose set.
The 15 declared source/compiler/tester probability cells have sampling-error
union bound `30 exp(-10)`. Calibration failure is additionally charged when
claiming false-rejection control for the true shared model, giving
`2 exp(-6)+2 exp(-8)+30 exp(-10)<0.01`. No independence between the 15
within-stream empirical frequencies is required for this union bound.
The fixed drift alternative changes the actual force used in the held-out
setting while leaving calibration and the rejection threshold fixed. Its
rejection is a synthetic protocol failure control. Nonrejection of the null
stream does not identify a physical mechanism or measure full CQ trace
distance.

## Full-output and cost interfaces

The preparation-failure block retains the actual unnormalized
failure-conditioned reference marginal while resetting only the system.
Initial filtering is charged once. Subsequent parameter and dynamics
comparisons have identical failure blocks, so they need no extra duplicate
preparation charge. The source's acceptance effect is derived as `s^2 I`,
making this specific normalized accepted target CPTP. This is why contraction
of the preparation error is legitimate without an unmentioned posterior
amplification factor.

The physical compiler uses the true common gate; the finite nominal channel
is a predictor and is not asserted to be an available hardware gate. The
uniform all-input error theorem concerns the exact finite channel. Adding
the reserved numerical `1e-8` requires a separate accepted numerical receipt
for the returned output; the particular root interval calculation covers
only its specified entangled input.

The source retry probability is `s_N s^2`. The complete attempt cost includes
preparation failures and resets. One-time calibration is amortized by delivered
outputs, and unknown quantum inputs or references cannot be copied for free
retries. Counts of visible force labels are actual physical pulse counts only
under the explicit flag-first schedule; coherent scheduling has its own cost.

## Evidence classification and remaining responsibilities

The proof arguments above are paper proofs. C's independent exact checker and
raw-stream accounting are computational evidence with separately recorded
source identities. The streams are synthetic. This review adds no Lean
declaration and no hardware or project experimental evidence. Genuine device
claims still require the specified preparation/readout offsets and scales,
shared-pulse and drift bounds, Hamiltonian validity, filter/reference behavior,
input excitation certificate, failures/leakage and measured resource costs.

No new full-OPT reconstruction, independent complex-sector selection,
actualization mechanism identification, arbitrary-memory theorem, unbounded
time limit, or infinite-reference theorem is inferred from this result.
