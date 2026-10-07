# C4 — Structural Identity / FBT Synthesis Audit

Package status: **LOCAL COMPLETE / PORT OPEN**
Conclusion classes: **CONDITIONAL_THEOREM + NO_GO + ADAPTER + METHOD**

## 1. C4-01 / C4-02 current canonical inputs

The repository already contains the generic transport infrastructure required by
Roadmap v2:

- M-TC finite exact/approx transport calculus;
- `ParentBindingDynamic.bindingTransportEnvelope` and semantic tracking;
- P9 typed `ObjectScaleTransport` and composition;
- finite-time same-parent preservation inside P5/P12 under an explicit identity
  bridge.

These are reused rather than re-proved.  They do not by themselves infer
structural object identity.

## 2. C4-03 structural identity upgrade

The package refuses parent-token equality as the definition of identity through
structural change.  `RealizedStructuralContinuation` is instead a directed,
registered tolerance relation between the old realized dynamics transported
forward and the newly formed parent's realized dynamics.

This is an **operational continuation certificate**, not a metaphysical identity
axiom and not equality of representations.

## 3. C4-04 formation–transport

`FormationRelation` is set-valued, preserving the parent-completion no-go.
`FormationTransportCompatible` is an exact interface condition for the
set-valued relation.  It is classified as an adapter obligation, not an
existence theorem.

For the quantitative endpoint a registered representative/selector may be used
with explicit defect

`dist(tp (f0 x), f1 (tx x)) ≤ epsF`.

The selector does not erase the underlying nonunique formation relation.

## 4. C4-05 binding–transport

`BindingTransportCompatible` records exact realization naturality.  The
quantitative theorem instead permits

`dist(B1(tp p), td(B0 p)) ≤ epsB`

and separately requires an `L`-Lipschitz new binding map with `L ≥ 0`.

## 5. C4-06 terminal quantitative theorem

`approximate_fbt_realized_bound` proves

`dist(B1(f1(tx x)), td(B0(f0 x))) ≤ L * epsF + epsB`.

`certified_formed_structural_continuation` adds independent source/target
formation membership and, when the registered margin dominates that error,
returns:

1. source is formed at time 0;
2. target is formed after lower-level transport;
3. the two are in directed realized structural continuation.

**No `SameObject` premise occurs.**

## 6. No-go control

`formationTransport_does_not_imply_bindingTransport` gives an explicit Bool
counterexample: formation naturality can hold exactly while binding naturality
fails.  Formation and realization compatibility therefore cannot be collapsed
into one unnamed premise.

Existing canonical no-go results additionally keep apart:

- same child evidence vs unique parent completion;
- equal history/control representation vs same parent;
- scale transport vs identity preservation.

## 7. What remains open

- derive `epsF` from a concrete changing response/formation mechanism;
- derive or empirically calibrate binding transport defect `epsB` in domains;
- extend from one-step registered representatives to set-valued Hausdorff/path
  continuation under genuine split/merge/birth/death;
- connect continuation to causal/predictive certificates in changing physical
  systems;
- empirically test the diagram under preregistered structural turnover.

Thus C4 local package is closed, but Core §31.2 C4 remains OPEN.
