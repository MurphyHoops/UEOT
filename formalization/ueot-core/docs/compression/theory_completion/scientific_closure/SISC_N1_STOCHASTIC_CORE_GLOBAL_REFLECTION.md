# SISC N1 — scientific synthesis: three different notions of predictive closure

Status: **LOCAL FORMAL FINITE-STOCHASTIC SUBPROGRAM PASS WHEN GATE GREEN**;
full UEOT physical science remains **HOLD**. Canonical frozen Core unchanged.

## 1. Why the previous deterministic intuition needed revision

The previously established `SISCFutureResponseCore` has a canonical state
`F_x(w)=r(T_w(x))` for *deterministic* controlled evolution. Equality of these
full functions is automatically a congruence for every action, because
prefixing `a` simply changes the queried future word from `w` to `a::w`.

For a controlled **stochastic** process, merely forming classes from equality
of complete output-trace laws does **not** imply that the next transition
probability of each resulting class is independent of which hidden source
representative was used. That distinction is fundamental.

The new six-state `SISCStochasticTraceNoGo` formally constructs `0` and `1`
with identical probabilities for **all finite output words**, while one
step from `0` enters the predictive class of state `4` with mass 1 and
one step from `1` enters it with mass 0. This is not a stochastic partition
with its own autonomous Markov transition. It is a mathematical negative
result against the strongest tempting stochastic extension of the
deterministic quotient theorem.

## 2. The exact finite Markov criterion already hidden in the Core

P-ALG-01 (`FiniteStablePartition`, `FiniteStablePartitionQuotientLaw`)
already used **strong lumpability** of all-action block masses for finite
controlled stable partitions. The N1 modules expose its necessary-and-
sufficient universal factorization form and reconcile it with a general
reachable-image finite stochastic-kernel interface:

`StrongLumpability(K,q) ⇔ ∃! normalized nonnegative quotient Markov kernel`
`Stable(M,S) ⇔ ∃! exact real block transition Q`.

`SISCModelKernelReconciliation.lean` proves that converting `M` into the
general kernel and choosing `q(x)=⟦x⟧_S` makes the two block-mass formulas
**identical term-by-term**, and their lumpability predicates equivalent.
This is an integration check, not a previously absent physical theory.

## 3. The experimentally actionable bridge (N1.2 and N1.4)

Suppose a registered test family `f_i` linearly reconstructs the indicator
of every candidate destination class `C`:

`1_C(y) = Σ_i c_i(C) f_i(y)`.

If one-step test expectations coincide for source states in the same
candidate class and every action, then class transition masses coincide;
exact strong lumpability and the unique Markov quotient follow.

If indicator reconstruction error is at most `δ` and test-expectation
discrepancy is at most `ε`, the exact Lean theorem proves

`|K_a(x,C)-K_a(x',C)| ≤ 2δ + ε Σ_i |c_i(C)|`.

**New core intuition:** what controls scientific compression is not merely
the *number of registered probes* or pairwise state separability. It is the
**identifiability and conditioning of the measurement system relative to
transition-block probabilities**. Even tiny predictor errors may certify
very little if the observable basis poorly reconstructs class indicators.

The exact four-state counterexample proves that constant test expectations
can match perfectly while current-output Markov lumpability fails. These
are genuine, inspectable negative controls, not simulated empirical evidence
of new physical laws.

## 4. Two mathematically sound fallbacks after quotient failure

### A. Full normalized Bayes belief (positive probability semantics)

`SISCStochasticBeliefBridge.lean` embeds an arbitrary finite controlled
kernel with deterministic emission into the existing P-REF-02
`FiniteBayesBelief` interface. Under a **known and correct** kernel,
normalized latent beliefs predict normalized next-output laws and Bayes
updates explicitly signal `modelConflict` for zero-evidence events. The
same six-state trace-counterexample has no Markov predictive-class kernel
but does have a valid belief-predictive law. The belief generally contains
more information and more coordinates than a minimal predictive state.

### B. Finite-dimensional linear predictive span (signed linear semantics)

`SISCLinearPredictiveLift.lean` proves that the span of exact source trace
response functions is invariant under every action–observation prefix map.
Its dimension is at most the number of microscopic states, whether or not
strong lumpability holds. This is the classical observable-operator / PSR
mechanism, not a new UEOT-exclusive physical principle. Crucially, arbitrary
elements of this vector space may be **signed linear combinations**; they
are not guaranteed normalized, nonnegative or valid physical beliefs.

These three forms of closure are therefore distinct:

| Representation | Closure | Positivity | Need for strong lumpability |
|---|---|---|---|
| Microstate predictive classes with Markov quotient | autonomous stochastic transition on classes | yes | **yes**, for class-mass-preserving projection |
| Full latent Bayesian belief | posterior/predictive Bayesian step | yes, if proper posterior | **no**, but accurate hidden model required |
| Linear trace-response span | action/observation linear shift | not for arbitrary linear vectors | **no**, but physical cone/readout separately required |

## 5. What a truly original UEOT object theorem would still require

The above is a well-integrated mathematical hierarchy grounded in established
P-ALG, P-REF and observable-prediction structures. It is **not** in itself
the scientific emergence of physical objects, identity, purpose or GOD/GOA.

The next indispensable bridge is a **causally observed persistent object
certificate** whose identity-preserving structure includes: actual
intervention feasibility; a nonempty, sufficiently spanning evidence protocol;
complete candidate-universe coverage; independent formation/lineage history;
mechanistically checkable viability and repair; and compatible internally
or externally identified purpose semantics. The object may still have more
than one valid lineage or GOA; forced uniqueness is scientifically invalid.

## 6. Concrete next theorem agenda

1. **N2 observational closure versus conditional update:** identify a
   finite-dimensional *positive normalized cone* inside the predictive
   linear span, and prove precisely when the event-shift can be renormalized
   into a valid posterior; negative or zero-evidence examples mandatory.
2. **N2B robust finite-horizon propagation:** turn the `2δ+ε‖c‖₁`
   one-step class-mass bound into a multi-action path prediction bound with
   explicit total-variation/nonexpansivity assumptions, and quantify when
   the bound becomes useless.
3. **N3 protocol learning:** predeclare candidate classes and test family,
   estimate basis rank and reconstruction condition number with uncertainty,
   and return `UNRESOLVED` when classes are not distinguishable.
4. **N4 scientific source:** independent raw acquisition, precommitted
   protocols, out-of-distribution interventions, complete attempt inventory
   and second-party reviews. Existing C7 SQLite self-test is only method
   proof-of-operation, not independently verified physical evidence.

No numbered counted UEOT generator is claimed; original Core v3 and
`origin/main` stay frozen. Publication and external scientific closure HOLD.
