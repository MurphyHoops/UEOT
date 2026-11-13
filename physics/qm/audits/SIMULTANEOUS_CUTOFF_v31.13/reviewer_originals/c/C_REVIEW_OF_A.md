# C's independent review of A and the integration interfaces

Reviewer: native research agent C, 2026-11-12 UTC. Research baseline:
`cb17211653fde30aa50e0e9848798a6a5b3b3f12`.
This is an internal AI non-author review, not external human peer review.
The exact consumed source identities are recorded in
`C_CROSS_REVIEW_IDENTITY.json`.

**Verdict:** the reviewed paper claims survive the attacks below on their
explicit domains. No unresolved scientific blocker was found. Their universal
quantifiers remain paper-proved; finite floating checks do not upgrade them to
machine proofs. The final runtime runner must bind the final delivered bytes.

## 1. Attack on the strongest operational claim: local defects imply a full-tree bound

The tempting invalid argument would normalize every branch, substitute the
more favourable exact prefix energy into a finite-prefix defect estimate,
discard failure leaves, or apply trace-distance contraction only to traceless
differences. These substitutions fail in a state-dependent instrument tree:
exact and comparison prefixes can have different masses, and an individual
outcome difference need not have trace zero.

A's actual claim avoids all four substitutions. For the common initial state,
write `sigma_h=F_h ... F_empty(rho)` using the **comparison** prefix only.
The exact continuation `C^E_h` from any node to the complete labelled terminal
output is normal CPTP by induction over the finite tree. Direct recursion gives

`Omega_E(rho)-Omega_F(rho)`
` = sum_h sum_o C^E_ho((E_ho-F_ho)(sigma_h))`.

No normalization is introduced, and every continuation retains stopping,
failure and outcome labels. A proves contraction on a Hermitian trace-class
operator Y using its Jordan parts, so the proof does not require `Tr Y=0`.
It therefore applies to each signed outcome difference. The local complete
outcome trace norm is the sum over orthogonal record blocks. The resulting
half-norm estimate has exactly the asserted sum of local defects.

The zero-prefix case is safe: a positive trace-class state of zero trace is
zero, so its contribution vanishes without division by mass. An unnormalized
unitary-prefix estimate scales linearly in the actual mass. For example, a
rare branch of mass m can carry conditionally orthogonal states while the
complete-output distance is only m. Substituting its conditional distance one
without mass would be a different, weaker quantity; deleting the branch would
falsely give zero.

Observation permissions are substantive. If the action coin is hidden, A sums
it inside the visible event before evolving; if visible, it belongs to the
record. The common policy is a function of the allowed visible fibre, and
persistent physical memory must be included in the system. Equality of an
isolated one-slot CP map is not used to identify two processes that retain an
omitted environment.

The finite model's optional full-space extension is used only to phrase a
common-carrier theorem. Its behaviour outside the reachable support is not
declared to be the oscillator. A normal CPTP extension exists, for example by
using the finite instrument on the support and a fixed complete preparation
on the complementary block. Neither the proof nor the runtime queries that
arbitrary extension as physical dynamics.

I checked the accompanying script and its receipt identity. The actual
finite-state controls include an entangled two-dimensional reference,
state-dependent unequal branch masses, early stopping, hidden Kraus refinement,
observation-fibre weights, zero branches and a label-swap counterexample. They
are relevant controls of the implementation and algebra; they are not the
reason the trace-class universal theorem is true. I did not repeat this
unchanged numerical run merely to produce a second PASS label.

**Disposition:** accepted as P-OPT-05 with the same complete instruments,
fixed finite tree, legal common policy, finite untouched reference, and the
specified F-prefix/E-suffix orientation. No unrestricted controller or
unbounded-stopping extension is inferred.

## 2. Attack on the strongest parameter claim: a uniform square-root-six displacement bound

There are two likely invalid enlargements: inferring `D(X^2)` from finite mean
number, and moving the infinite X invariant to compressed Galerkin prefixes.
The latter would directly invalidate the proposed uniform-in-input parameter
constant.

The reviewed A proof uses the appropriate domain. The inequality
`X^2<=4n+2` is a quadratic-form statement. A finite-mean input has purifications
in `D(X)`, which is the form domain of the positive operator `X^2`; it need not
be in the operator domain `D(X^2)`. Its norm `||X psi||` is finite. Strong
commutation follows from the exact force's spectral decomposition and the
spin-only nature of the phase, not from a merely formal commutator of
unbounded symbols.

For any such purified state, the spectral pointwise inequality
`|exp(-ix lambda)-exp(-iy lambda)|<=|x-y| |lambda|` gives the one-gate bound.
Hybrid telescoping of a k-force word with exact nominal prefixes and exact
true suffixes gives `k|x-y|sqrt(Tr X^2 rho)`. The fixed complete Q law is the
same in both processes and has mean k equal to one. After the declared
low-spectral filter, the normalized passing mean remains at most one. Thus
the complete-Q bound `sqrt(6)|x-y|` is justified; the reference is retained.

A's C-MICRO-03 counterexample explicitly blocks extending this invariant to
the finite model. In basis `(g0,g1,e0)` at K=1, the finite H couples g1 to e0,
while the compressed full X-square form is `diag(1,3,1)`. Starting from e0,
the finite moment becomes `1+2 sin^2(x)` although the infinite exact moment
remains one. This is a concrete statement about the actual compressed map,
not a Kraus-level commutation test.

The valid integrated order is therefore

`true infinite C_x -> nominal infinite C_xhat -> exact finite C_K,xhat`.

C's code uses this order. It computes the parameter displacement from
calibration alone and evaluates the Galerkin allowance at the resulting
rational xhat. It does not feed the unknown true parameter to the finite
predictor. The phase/control parameters, ideal preparation and detector
membership remain independent assumptions.

**Disposition:** accepted on the specified infinite force/phase family and
finite-mean input domain. It is not a stability theorem for arbitrary
Hamiltonian parameters or arbitrary finite prefixes. The domain and order
corrections are present in the reviewed final A source and C implementation.

## 3. Check of B's source and the downstream error domain

I read B's complete simultaneous-Galerkin proof. Its analytic dependencies are
acyclic: self-adjoint source construction; finite-support Duhamel remainder;
finite-matrix energy estimate; then lower-semicontinuous limits for arbitrary
finite-energy inputs. The Galerkin convergence used in the energy limit does
not consume the energy-growth statement being proved.

The relative-n bound establishes the positive-frequency Kato--Rellich
application on D(n). The zero-frequency force has its separate quadrature
realization. The general domain theorem is not evaluated at omega=0 by
continuity of a formula. The piecewise finite-time statement retains its
explicit self-adjoint realizations and G-preserving reference dynamics.

The finite expansion leaves the true unitary on the left and G-controlled
factors on the right. At j<=L all intermediate supports fit in
`K=N+2L`; the first L coefficients agree with the true matrix exponential's
finite expansion. Both L+1 remainders have the same product bound. Thus the
factor `2 c_(L+1)` compares two actual dynamics, not two projected states and
not a guessed infinite Dyson tail. Its tensor extension preserves the stated
finite-reference operator norm.

The a posteriori boundary integral also retains the necessary `sqrt(m)`
outside the finite-prefix purification error. Its square-root integrand is
homogeneous in the unnormalized prefix mass. Neither a floating boundary
sample nor a global energy mean is treated as a certified local integral.

The common Q-weighted bound follows from a separately derived state-independent
labelled-unitary law. It is not applied to the raw source using Q weights,
nor to state-dependent readouts. Arbitrary output controls still require A's
general prefix theorem and their actual defect bounds.

**Disposition:** B's bound is a valid input to the C certificate. No uniform
infinite-time limit, arbitrary controller, infinite reference or field-theory
completion is inferred.

## 4. Root numerical and kernel interface review

I read `interval_predictor.py`. Its finite generator is the actual G-cutoff
red-plus-blue matrix, not a projected exact displacement. It evaluates sparse
degree-100 polynomials on the stated `G<=1`, reference-dimension-two entangled
input at K=4175. Integer outward intervals enclose square roots, phase gates,
recurrences and coefficient roundoff. A uniform operator-norm bound 13 gives
the geometric Taylor tail beginning at order 101; products of two approximate
unitaries use `(1+r)^k-1`. Final centre normalization is charged by twice the
total vector error. The resulting exact normalized integer vectors form a
valid full Q CQ output with all zero failure blocks retained.

This is a numerical output certificate for that one input, not a numerical
verification of all mean-one inputs. The all-input result continues to refer
to the exact finite map. Root's reviewed kernel and execution contract state
this distinction explicitly, quote the conservative `0.041930158795` and
conditional numerical `0.041930168795` bounds, keep fixed-sample versus
post-admission coverage separate, and mark empirical physics as untested.

The early root numerical artifact was correctly labelled a development run:
its calibration hash precedes C's final statistical-scope metadata corrections,
although its xhat is unchanged. It must be retained with that original identity
or rerun on the final report, not relabelled as consuming new bytes. Root has
assigned the integrated runner to execute and rebind the final inputs.

## 5. Cross-review corrections already incorporated

The final C pipeline incorporates two substantive reviews from the other
roles: B's fixed-n coverage cannot become post-admission coverage or a
repeat-until-admit stopping rule; A's one-dose detector-bias symmetry does not
survive a second dose if the bias is fixed and shared. The final draft now
distinguishes that identifiable two-parameter model from arbitrary
setting-dependent offsets, and the two-dose holdout remains unfitted.

The C runtime also consumes the frozen inverse width and keeps the overlap
fallback inside that width; actual outer endpoints determine Delta_x. All
failures, filter disturbance, actual reference conditioning and conditional
numerical scope remain in the final certificate. There is no new hardware or
Lean evidence in these reviews.
