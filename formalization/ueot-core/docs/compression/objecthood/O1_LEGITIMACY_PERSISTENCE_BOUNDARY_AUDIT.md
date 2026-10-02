# Track O / O1 — Functional Legitimacy and Persistence Boundary Audit

Status: **LOCAL O1 CLEAR — stage gate passed before commit**

Base:

- canonical local base: `main@522752637b3011f3fb7aacafc54badd5bdd7d864`;
- parent tracker: GitHub Issue #230;
- counted-core impact: **NONE**;
- frozen counted core remains `{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 1. Scientific question

The merged Track-X lift stores one selected preserving controller `pi` inside
the reflexive state and proves autonomous persistence of `K × {pi}`.  That is
too syntactic for a repair target because P-PER does not assert uniqueness of
the preserving controller.

O1 therefore asks for the weakest functional identity class that is already
supported by the frozen viability semantics.

## 2. Functional legitimate organization

For finite controlled dynamics `P` and a declared viability kernel `K`, define

```text
PreservingController P K c
  := forall x in K, support(P x (c x)) subset K.
```

The legitimate constitutive domain is

```text
L(P,K) = {(x,c) | x in K and c preserves K}.
```

This deliberately treats all controllers with the same persistence function as
legitimate organizational realizations.  Returning to one historical selector
is therefore not built into Object identity.

## 3. Positive closure results

The O1 theorem surface proves:

1. every previous singleton-controller domain `K × {pi}` embeds into `L(P,K)`
   when `pi` preserves `K`;
2. if `K` is nonempty and `viabilityStep P K = K`, then `L(P,K)` is nonempty,
   using the existing P-PER stationary-selector theorem;
3. the current `constitutiveLift` preserves the whole functional legitimate
   class, not merely one chosen selector.

Thus the existing Track-X construction already supplies the **closure** half of
a self-stabilizing object semantics.

## 4. Negative convergence result

Define the corrupted-controller domain by controllers that do **not** preserve
`K`.

Because the current Track-X lift copies its controller coordinate exactly,
O1 proves:

```text
non-preserving controller
  -> every one-step successor still has that non-preserving controller
  -> every finite-time marginal stays inside the corrupted-controller domain.
```

Since the corrupted-controller domain is disjoint from `L(P,K)`, the current
lift cannot supply convergence after controller corruption.

This is an explicit G3 boundary:

```text
constitutive runtime persistence != self-stabilizing repair.
```

## 5. Nonclaims

O1 does not provide:

- a repair operator;
- physical recovery from outside `K`;
- uniqueness of legitimate controller;
- P-OMG failure repairability;
- universal Objecthood;
- a fifth counted generator.

## 6. O1 stage gate

Before the O1 commit is allowed, the exact working tree must pass:

- focused `Legitimacy.lean` compile;
- public `Objecthood` root build;
- `UEOT.V3.Compression` build;
- full `lake build UEOT` regression;
- proof-escape scan over the Objecthood namespace;
- selected theorem axiom audit;
- post-FINAL research-governance validation for
  `compression/objecthood-self-repair`;
- research-governance regression suite;
- `git diff --check`;
- source review that O1 imports existing Track-X/P-PER surfaces but mutates no
  frozen theorem module.

Only after all of these are CLEAR may O1 receive its own local commit and O2
begin.

## 7. Exact local audit result

The first compile attempt was **BLOCKED** and therefore not committed.  It
exposed two interface defects in the draft proof:

1. membership in `nonPreservingControllerDomain` had not been explicitly
   unfolded before reuse as a controller predicate;
2. the all-marginals theorem uses `stationaryStateLaw` on the reflexive state
   and therefore requires explicit finite-state instances for `X` and `A`.

Both were repaired explicitly; no theorem statement was weakened to hide the
failure.

The repaired exact O1 working tree then passed:

- `lake env lean UEOT/V3/Compression/Objecthood/Legitimacy.lean`: **PASS**;
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS**;
- full `lake build UEOT`: **PASS — 9103 jobs**;
- Objecthood proof-escape scan for
  `sorry/admit/axiom/opaque/unsafe/native_decide`: **CLEAR**;
- selected axiom audit on nonemptiness, closure, and all-marginals boundary:
  only standard `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**, including Objecthood
  ownership, X/O isolation, fork rejection, and global concurrency cap;
- simulated exact candidate governance check against base
  `522752637b3011f3fb7aacafc54badd5bdd7d864`: **PASS — 4 changed paths**;
- `git diff --check`: **PASS**;
- source mutation audit: only the new Objecthood root/module/doc plus the one
  public `Compression.lean` import; **no frozen Core-v3 or Track-X theorem file
  was modified**.

O1 disposition: **CLEAR / eligible for its own local commit**.
