# Recursive Sufficient State Compression — Feasibility Audit

Status: **LOCAL LEAN PASS / M-QD SPECIALIZATION / NO NEW GENERATOR**

This audit revisits the earlier experimental M-BU / Bayesian Recursive Closure
candidate after the four-generator Core compression was finalized.

The question is whether a broader **M-RS — Recursive Sufficient State**
generator exists independently of M-QD.

## 1. Generic recursive-state equation

Let

\[
C:H\to S
\]

be a current-state representation of a richer history, and let

\[
R:H\to E\to T
\]

be the next response after one new input `e : E`.

The natural recursive-sufficiency condition is

\[
C(h)=C(h')
\Longrightarrow
R(h,e)=R(h',e)
\qquad\forall e.
\]

After currying the input, however,

\[
R:H\to(E\to T),
\]

this condition is exactly M-QD fibre compatibility.

The local module

`UEOT/V3/Compression/RecursiveSufficientState.lean`

formalizes this equivalence in

`inputFiberCompatible_iff_fiberCompatible_curried`.

## 2. Reachable-state correction

A state representation `C : H -> S` need not be surjective onto the ambient
state space `S`.  Therefore it would be incorrect to apply the M-QD unique
descent theorem directly to `C` without an extra assumption.

The right object is the reachable image

\[
S_{\rm reach}=\operatorname{range}(C).
\]

The canonical map

\[
H\to S_{\rm reach}
\]

is automatically surjective.  Hence M-QD gives a unique recursive update

\[
U:S_{\rm reach}\to E\to T
\]

whenever the input-wise fibre-compatibility condition holds.

Lean theorem:

`existsUnique_reachableUpdate`.

This is a useful conceptual refinement: **recursive state closure is a quotient
universal property on reachable states**.  Extension to unreachable ambient
states is a separate realization choice.

## 3. P-PRED-03 mapping

For P-PRED-03:

- `H` is the history carrier;
- `C h` is the current canonical predictive coordinate state;
- `E = A × O` is action plus newly observed symbol;
- `R h (a,o)` is the history-level continuation-response vector.

The already frozen coordinate-closure assumptions imply exact input-fibre
compatibility.  The local theorem

`pred03_inputFiberCompatible`

proves that obligation, and

`pred03_existsUnique_reachableUpdate`

then obtains the unique recursive update on reachable canonical states through
M-QD.

### What remains outside M-QD

The full frozen P-PRED-03 theorem is stronger.  It constructs an update on the
whole ambient coordinate space and proves joint measurability for finite action
and observation alphabets.

Those facts require the explicit Bayes-coordinate formula and measurable
extension.  They are not consequences of set-level quotient descent.

Thus P-PRED-03 decomposes naturally into:

\[
\text{M-QD reachable recursive closure}
+
\text{Bayes/measurable ambient realization adapter}.
\]

## 4. Relation to the earlier M-BU experiment

The earlier `BayesianRecursiveClosure.lean` correctly identified a reusable
Bayes ratio and preserved the zero-evidence semantic boundary.  However its
generic state-factorization theorem is not evidence for an independent
generator once the reachable-state M-QD formulation is made explicit.

M-BU contributes domain construction:

- numerator/denominator factorization;
- Bayes ratio;
- finite-alphabet joint measurability;
- explicit fallback/model-conflict distinction.

The universal **reason an update can depend only on the state** is M-QD fibre
compatibility.

Recommended classification:

**M-BU = BAYESIAN RECURSIVE-REALIZATION ADAPTER OVER M-QD, UNCOUNTED.**

## 5. P-REF-02 is not a second exact M-RS mapping

P-REF-02 contains genuine belief sufficiency, but its frozen theorem surface is
not merely a history-to-state recursive factorization.  It includes:

- Standard-Borel posterior/disintegration;
- observation-law/posterior reconstruction of the joint law;
- posterior averaging consistency;
- finite evidence normalization;
- positive-evidence Bayes formula;
- zero-evidence `modelConflict` semantics;
- one-step discounted-control reduction.

In the finite Bayes formula the current belief is already the state; using
`C = id` would make the M-QD descent step trivial.  The substantive theorem is
the Bayesian/disintegration structure, not quotient descent.

Therefore P-REF-02 remains a **partial adapter relation**, not a full exact
M-RS source mapping.

## 6. Why P-PROC-01 / P-REF-01 do not supply the missing third family

P-PROC-01 Markovizes a history-dependent process by carrying the complete
history as the state.  P-REF-01 similarly augments physical state with
reflexive structure and proves path-law/control-kernel statements.

These are recursive carriers, but their frozen endpoints additionally require:

- kernel composition;
- Markov-kernel validity;
- measurable readout recovery;
- path-law existence/uniqueness or controlled closure.

Taking the complete history itself as `S` makes recursive sufficiency trivial;
it does not produce an independent compression of history.  Counting this as a
third M-RS family would therefore confuse **state augmentation** with
**sufficient-state quotienting**.

## 7. Relation to dynamic lumpability

P-DYN-01 is closer in spirit: a macro representation is dynamically sufficient
when the pushed-forward next-state law depends only on the macro state.

But this is a kernel-valued/measurable quotient obligation, not the bare
set-level recursive-state theorem.  The first compression mission already
preserved this distinction rather than forcing P-DYN-01 into M-QD.

This boundary should remain intact.

## 8. Compression conclusion

The search for a fifth generator does **not** succeed here.

Instead it yields a stronger architecture statement:

\[
\boxed{
\text{recursive sufficient-state closure}
=
\text{input-parametrized quotient descent on reachable states}
}
\]

with richer measurable/Bayesian/kernel semantics supplied by domain adapters.

This explains the earlier M-BU ablation result: M-BU was useful but failed
nonredundancy because the universal factorization obligation already belongs to
M-QD.

Recommended status:

**M-RS REJECTED AS AN INDEPENDENT GENERATOR; RETAIN AS AN M-QD DERIVED
INTERFACE.**

The canonical four-generator count remains unchanged.

## 9. Next search direction

The next compression search should target a structure not already reducible to
the four generators.  Two candidates remain scientifically meaningful:

1. teleological/value equivalence across P-DDH-01 and P-TEL-01, with careful
   distinction between objective equality, ordering equivalence, and optimal
   policy equivalence;
2. control fixed-point / stochastic fixed-point stability, testing whether
   Bellman contraction and Dobrushin contraction share a reusable fixed-point
   perturbation core without erasing their domain-specific selectors and
   probability metrics.

Neither should be promoted without the same exact-mapping and deletion gates.
