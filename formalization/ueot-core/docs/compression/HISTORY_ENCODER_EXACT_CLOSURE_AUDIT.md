# History Encoder Exact Closure — Vanishing Fibre Defect Audit

Status: **LOCAL LEAN PASS / APPROXIMATE-TO-EXACT CLOSURE ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/HistoryEncoderExactClosure.lean`

This lane tests the main closure question left open by the approximate history
encoder work:

> If one fixed encoder representation has reward and encoded-transition fibre
> defects bounded by envelopes tending to zero, does the approximate control
> representation become an exact control quotient?

The answer is yes in the finite setting, and the proof reuses the existing
second-order structural-defect exactification theorem rather than recreating
zero-defect arguments locally.

## 1. Input structure

Fix:

- one finite micro/history model `micro`;
- one surjective encoder `C : H -> S`;
- one representative macro model generated from that same source and encoder.

Assume two envelopes

\[
\varepsilon_r(n)\to 0,
\qquad
\varepsilon_p(n)\to 0,
\]

such that, for every `n`, every pair `h,h'` in the same encoder fibre, and every
action,

\[
|r(h,a)-r(h',a)|\le \varepsilon_r(n),
\]

and

\[
D_{TV}
\bigl(C_\#P(\cdot\mid h,a),C_\#P(\cdot\mid h',a)\bigr)
\le \varepsilon_p(n).
\]

The underlying fibre discrepancy is fixed; only the certified envelope varies.
Therefore a discrepancy that is uniformly bounded by arbitrarily small
envelopes must vanish.

## 2. Representative macro target

The target macro model is exactly

`ApproximateHistoryEncoder.representativeMacroModel C hC micro`.

For each micro history `h`, the chosen representative of `C h` lies in the
same encoder fibre.  Hence the vanishing fibre envelopes imply vanishing
reward and transition-TV defects between `h` and the macro row at `C h`.

No external macro model is supplied.

## 3. Structural-defect reuse

The theorem

`exactControlQuotient_of_vanishing_fiber_defects`

does not prove exactness by a fresh squeeze argument.  It calls the existing

`StructuralDefectControlLimit.exactControlQuotient_of_vanishing_defects`.

That existing theorem already owns the second-order closure mechanism:

\[
\text{nonnegative defect}
\le
\text{vanishing envelope}
\Longrightarrow
\text{defect}=0,
\]

followed by zero-TV equality for the finite transition PMFs.

The history-encoder lane therefore becomes a genuine new application of the
registered structural-defect layer.

## 4. Exact control quotient conclusion

The resulting object is a literal

`ExactControlQuotient H S (fun _ => Act)`.

Thus the conclusion is stronger than saying that the P-QUO-02 radius `D`
vanishes.  The structure itself contains exact identities:

- exact reward closure on every encoder fibre;
- exact pushed-forward transition closure;
- exact common discount;
- exact source/target identity through the same encoder.

This is the right notion of exact descent for the finite control interface.

## 5. P-QUO-01 transfer

`p_quo_01_of_vanishing_fiber_defects` immediately transfers the frozen exact
quotient consequences:

\[
V^*_{micro}(h)=V^*_{macro}(C h),
\]

exact optimal action-value agreement,

and exact optimality of the lifted macro greedy policy against the full
history-dependent randomized causal policy class.

Hence the closure is semantic, not merely metric.

## 6. Zero-defect special case

`exactControlQuotient_of_zero_fiber_defects` specializes the envelope theorem
to constant zero envelopes.

This explicitly verifies the endpoint requested by the prior audit:

\[
\varepsilon_r=\varepsilon_p=0
\Longrightarrow
\text{literal exact control quotient}.
\]

The result therefore does not rely on informal reasoning that `D = 0` ought to
mean exactness.

## 7. Compression significance

The verified chain is now

\[
\boxed{
\text{finite encoder fibre defect}
\to
\text{approximate quotient}
\to
\text{near-GOD / near-GOA}
}
\]

for finite defects, and

\[
\boxed{
\text{vanishing fibre defect}
\to
\text{StructuralDefectClosure}
\to
\text{ExactControlQuotient}
\to
P\text{-QUO-01}
}
\]

in the exact limit.

This is meaningful second-order evidence because the same generic
structural-defect closure now operates both on the earlier control-limit
assembly lane and on a representation-generated fibre-defect lane.

It still does **not** justify replacing M-QD or M-TC, and it does not create a
new counted generator.

## 8. Boundary conditions

### Fixed source and encoder

The theorem keeps `micro` and `C` fixed while the certified envelopes vanish.
It does not yet treat a changing encoder sequence `C_n` or changing micro
source.

### Uniform finite action type

As in `ApproximateHistoryEncoder`, the history-level action carrier is one
uniform finite type.  State-dependent admissibility descent remains separate.

### No statistical estimation theorem

The envelopes are mathematical certificates.  The theorem does not show how
finite data estimates them, how confidence intervals shrink, or whether a
learned encoder generalizes out of sample.

### No path-law exactification beyond the stated control interface

Exact reward and encoded one-step transition descent is sufficient for
P-QUO-01.  Full equality of independently supplied history path laws is not
claimed.

### Finite-state closure

No compact/Feller/infinite-dimensional analogue is established here.

## 9. Disposition

Recommended classification:

**APPROXIMATE-TO-EXACT REPRESENTATION/CONTROL CLOSURE: PASS, UNCOUNTED.**

The four-generator FINAL accounting remains unchanged.  The new evidence is
architectural: an approximate representation theorem and an exact quotient
theorem are now connected by an already-registered second-order closure
mechanism.

## 10. Next pressure test

The most informative next step is no longer the constant-source squeeze.  It
is a **moving representation limit**:

1. allow a sequence of macro models or encoders generated by data/approximation;
2. require explicit convergence of the generated macro reward/transition
   coordinates and their fibre defects;
3. prove an exact limiting quotient without assuming the limiting macro model
   already has the desired identities;
4. determine whether M-TC + StructuralDefectClosure suffice for the whole
   argument or whether a genuinely new compactness/identification obligation
   remains.
