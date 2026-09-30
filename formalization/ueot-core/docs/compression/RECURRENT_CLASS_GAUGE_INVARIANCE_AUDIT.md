# Recurrent-Class Gauge Invariance Audit

Status: **LOCAL LEAN PASS / RECURRENT STRUCTURE GAUGE FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/RecurrentClassGaugeInvariance.lean`

This lane separates the exact recurrent structure of a finite closed loop from
the quantitative perturbation machinery used by frozen P-GOA-03.

The purpose is to establish which recurrent objects are true quotient-gauge
invariants before transporting transient fundamental matrices, absorption
weights, or perturbation constants.

## 1. Kernel powers are gauge covariant

For exact kernel conjugacy

\[
P(s,t)=Q(e(s),e(t)),
\]

`pow_conjugate` proves for every finite time `n`

\[
\boxed{
(P^n)(s,t)=(Q^n)(e(s),e(t)).
}
\]

This gives an exact bridge from one-step semantic gauge to finite-step graph /
communication structure.

## 2. Reachability and communication are label-free

Define positive-probability reachability by

\[
x\leadsto_P y
\iff
\exists n\ge0:(P^n)(x,y)>0.
\]

Then `reachable_relabel_iff` and `communicates_relabel_iff` prove

\[
e(x)\leadsto_Qe(y)
\iff
x\leadsto_Py
\]

and hence mutual communication is exactly preserved.

No irreducibility or recurrent-decomposition hypothesis is needed.

## 3. Closed recurrent carriers are gauge objects

`ClosedCarrier P A` means that positive one-step transitions from `A` never
leave `A`.

`RecurrentCarrier P A` combines:

- nonemptiness;
- pairwise communication inside `A`;
- closure under positive-probability one-step transitions.

Theorems

- `closedCarrier_image_iff`;
- `recurrentCarrier_image_iff`

prove that `A` is such a carrier for `P` iff `e '' A` is the corresponding
carrier for `Q`.

Thus recurrent support is not tied to the concrete state names chosen by one
quotient representation.

## 4. Carrier-supported stationary semantics also transports

`SupportedOn mu A` states that the law vanishes outside `A`.

`supportedOn_relabel_iff` proves exact support transport.  Combining this with
the already formalized invariant-set gauge gives

`carrierInvariantLawSet_relabel_eq`:

\[
\boxed{
\mathcal I_Q(eA)
=
e_\#\mathcal I_P(A),
}
\]

where the set consists of invariant laws supported on the chosen recurrent
carrier.

This is stronger than merely transporting the global invariant-law set: the
stationary family remains attached to the corresponding recurrent component.

## 5. Exact-control adapter

`selectorRecurrentCarrier_gaugeInvariant` applies the generic result to exact
control quotients related by `SemanticRelabel`, with one deterministic selector
transported through the same state equivalence.

The exact nonunique-GOA gauge chain is now:

\[
\boxed{
\text{semantic gauge}
\to
\text{kernel conjugacy}
\to
\text{finite-time reachability / communication}
\to
\text{recurrent carriers}
\to
\text{carrier invariant-law families}
\to
\text{Cesaro occupation / limits}.
}
\]

## 6. Why P-GOA-03 was not reused directly

`FiniteRecurrentDecompositionStability.lean` carries substantially more
structure:

- a fixed transient/recurrent partition;
- transient block `Q`;
- direct recurrent-entry block `R`;
- fundamental matrix `N=(I-Q)^{-1}`;
- absorption matrix `H=NR`;
- class laws;
- quantitative perturbation assumptions and bounds.

Those are required for P-GOA-03 perturbation theory but are not required to
state exact gauge invariance of recurrent structure.  Reusing the full package
here would conflate a structural equivalence theorem with its later numerical
stability adapter.

## 7. Boundary

- `RecurrentCarrier` is a structural closed communicating carrier; this file
  does not yet construct canonical equivalence classes or prove minimality.
- It does not yet transport P-GOA-03's transient block/fundamental matrix /
  absorption-weight data.
- It does not provide approximate recurrent-class stability under small model
  error.
- No counted generator, frozen P-ID, or ledger disposition changes.

## 8. Next pressure test

The next clean exact layer is to connect these carrier objects to the frozen
`FiniteRecurrentDecomposition` representation: transport a recurrent partition
and its class laws through state gauge, then prove that the resulting recurrent
mixture / absorption semantics agrees with the already established Cesaro
occupation gauge.

Only after that exact structural bridge should the P-GOA-03 perturbation bounds
be lifted to a gauge-invariant approximate recurrent-decomposition theorem.
