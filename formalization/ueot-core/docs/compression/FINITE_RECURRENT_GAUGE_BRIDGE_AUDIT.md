# Finite Recurrent-Decomposition Gauge Bridge Audit

Status: **LOCAL LEAN PASS / FROZEN P-GOA-03 STRUCTURE CONNECTED / UNCOUNTED**

Module:

`UEOT/V3/Compression/FiniteRecurrentGaugeBridge.lean`

This lane connects the exact recurrent/gauge architecture back to the frozen
P-GOA-03 source theorem without treating its bookkeeping labels as physical
objects.

## 1. Frozen recurrent classes become generic recurrent carriers

For a frozen `FiniteRecurrentDecomposition M` and class label `c`, define the
physical carrier

\[
A_c=\{\operatorname{inr}(r):K.\mathrm{classOf}(r)=c\}.
\]

`decomposition_class_is_recurrentCarrier` proves that `A_c` is:

- nonempty;
- internally communicating by the frozen `class_communicates` certificate;
- closed because recurrent-to-transient transitions vanish and cross-class
  recurrent transitions vanish.

Thus the class label `c` is only bookkeeping; the physical recurrent object is
the closed communicating carrier `A_c`.

## 2. Frozen class laws become carrier-supported invariant laws

`classLaw_supportedOn_classCarrier` proves the stored `classLaw c` vanishes
outside `A_c`.

`classLaw_mem_invariantLawSet` repackages the frozen vector invariance theorem as
membership in the generic invariant-law set.

Therefore

`classLaw_mem_carrierInvariantLawSet`

proves

\[
\boxed{
\pi_c\in\mathcal I_P(A_c).
}
\]

This is the exact bridge from P-GOA-03's class-specific stationary law into the
new set-valued GOA language.

## 3. Class mixtures commute with state gauge

`recurrentMixture_relabel` proves

\[
\boxed{
e_\#\Bigl(\sum_c w_c\pi_c\Bigr)
=
\sum_c w_c\,e_\#\pi_c.
}
\]

State relabeling does not change the class weights; it only transports each
physical class law.

This distinction is important: the labels in the quotient state space are
gauge, while mixture weights over long-run recurrent outcomes are semantic
quantities.

## 4. Source P-GOA-03 classes transport to an arbitrary conjugate target

`decomposition_class_transport` takes:

- one frozen source `FiniteRecurrentDecomposition`;
- any target finite stochastic kernel on the same finite carrier;
- any state equivalence `e` conjugating the two kernels.

For every frozen source class `c`, it proves:

1. `e '' A_c` is a target recurrent carrier;
2. `e_# pi_c` belongs to the target carrier-supported invariant-law family.

The target is **not** required to be separately packaged with the same
`T/R/C` bookkeeping split.  This is deliberate: transient/recurrent coordinate
labels are not themselves physical gauge invariants.

## 5. Interaction with the existing Cesaro gauge lane

The generic `CesaroOccupationGaugeInvariance` module already proves that exact
kernel conjugacy transports every finite Cesaro occupation average and every
convergent Cesaro subsequence limit.

The frozen P-GOA-03 theorem separately proves convergence of its source Cesaro
average to an absorption-weighted recurrent mixture.

Mathematically these imply the corresponding target recurrent-mixture limit.
They are intentionally not forced into one wrapper theorem in this file yet,
because the two historical modules expose different internal `DecidableEq`
instances for the same finite state type.  Lean therefore does not regard the
two `cesaroRow` expressions as definitionally identical without an additional
instance-stable adapter.

This is a representation/interface issue, **not** evidence against the
recurrent gauge statement.  The structural class/class-law bridge above is
fully machine checked.

## 6. Small infrastructure repair

`RecurrentClassGaugeInvariance.lean` was made explicit in its
`[DecidableEq S]` dependency instead of installing a hidden local
`Classical.decEq` instance.

That change is required because matrix powers used for reachability genuinely
depend on the `DecidableEq` instance in Lean's matrix semiring implementation.
Making the dependency explicit aligns the generic recurrent layer with frozen
P-GOA-03's standard `Sum` instance and avoids false instance mismatches.

No frozen source theorem was edited.

## 7. Scientific interpretation

The nonunique GOA architecture now connects all the way back to the frozen
source theorem:

\[
\boxed{
\text{P-GOA-03 recurrent decomposition}
\to
\text{closed communicating carriers}
\to
\text{carrier stationary-law families}
\to
\text{state-gauge transport}.
}
\]

Together with the already checked invariant-set and Cesaro-occupation gauge
modules, this materially weakens the earlier identification of GOA with a
single globally attracting invariant law.

## 8. Boundaries / next step

- This is an exact structural gauge bridge, not yet an approximate perturbation
  theorem.
- The frozen transient fundamental matrix, absorption matrix, hitting weights,
  and P-GOA-03 perturbation constants have not yet been transported modulo
  gauge.
- A direct wrapper combining the frozen Cesaro-limit theorem with the generic
  Cesaro gauge theorem is postponed until an instance-stable adapter is added;
  the mathematical components already exist separately.
- No counted generator, P-ID disposition, or four-generator ledger state
  changes.

The next substantive pressure test is therefore **Approximate Recurrent Gauge
Stability**: take P-GOA-03's fixed-partition perturbation calculus and formulate
its hypotheses/conclusions modulo the exact class/state gauge, while keeping
the decomposition-change boundary explicit.
