# Track O / O4 — Physical Recovery through P-REC Audit

Status: **LOCAL O4 CLEAR — stage gate passed before commit**

Parent local commits:

- O1 `0cc0316`;
- O2 `4a35633`;
- O3 `e2ddbd6`;
- counted-core impact: **NONE**.

## 1. Gap isolated by O1--O3

Controller self-stabilization assumes the physical coordinate is already in the
P-PER winning kernel `K`.  It says nothing about recovery after physical damage
has moved the system outside `K`.

O4 handles only this physical-recovery problem and deliberately reuses frozen
P-REC rather than inventing a parallel repair calculus.

## 2. Source-faithful repair model

A deterministic repair policy `rho : X -> A` induces the already formalized
homogeneous Markov kernel

```text
stationaryKernel P rho.
```

`PhysicalRepairCertificate P target` stores exactly the data required by
P-REC-04:

- repair policy;
- nonnegative measurable potential `W`;
- positive finite drift constant `c`;
- measurable target;
- drift inequality outside the target.

No viability or integrity theorem is reinterpreted as a repair theorem.

## 3. Quantitative recovery target

The frozen P-REC-04 route gives

```text
E_x[tau_target] <= W(x) / c.
```

The O4 repair basin is the finite-potential region

```text
B = {x | W(x) != infinity}.
```

Since `c` is positive and finite, every `x in B` has finite expected hitting
time.

## 4. Almost-sure recovery bridge

O4 additionally proves a missing generic bridge rather than assuming it:

1. if a path never hits the target, every truncated hitting time equals `N`;
2. therefore the extended hitting value is `infinity`;
3. Mathlib's `ae_lt_top` converts finite expected hitting time into
   `hittingValue < infinity` almost everywhere;
4. hence almost every genuine Markov path eventually hits the target.

The result is exposed both on the homogeneous Markov trajectory and on the
repository's `stationaryTrajMeasure P rho (PMF.pure x)` wrapper.

## 5. Explicit boundaries

O4 does not show:

- that P-PER viability implies recovery from outside `K`;
- that P-OMG failure/integrity data supplies a repair policy;
- that every physical state belongs to the repair basin;
- that the repair policy is internally selected by the damaged object;
- that recovery remains in the target after first hitting it;
- full constitutive self-repair.  O5 must combine O4 recovery with O3 closure.

## 6. Stage gate

O4 is committed only after focused compile, Objecthood/Compression/full UEOT
builds, proof-escape and axiom provenance checks, governance simulation and
regressions, diff-check, and an explicit P-REC assumption/nonclaim audit all
pass on the exact local working tree.

## 7. Exact local audit result

O4 had two pre-commit focused-compile blocks, both retained as audit evidence:

1. the first formal file omitted the `DynamicsKernel` namespace needed to
   resolve the already existing `homTrajMeasure` path constructor;
2. after that was fixed, the controlled trajectory wrapper still required an
   explicit `PMF.toMeasure_pure` bridge from `(PMF.pure x).toMeasure` to
   `Measure.dirac x`.

These were interface/provenance repairs.  No recovery assumption or theorem
conclusion was weakened.

After repair, the exact O4 tree passed:

- focused `PhysicalRecovery.lean` compile: **PASS**;
- public Objecthood build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS — 9106 jobs**;
- proof-escape scan: **CLEAR**;
- selected axiom audit for the never-hit/top bridge, finite-expectation a.s.
  bridge, P-REC wrapper, and controlled trajectory theorem: only standard
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**;
- simulated exact-candidate governance validation from O3 local head:
  **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

### Assumption / semantic audit

- Repairability is carried by an explicit `PhysicalRepairCertificate`; it is
  not inferred from viability, P-OMG failure structure, or integrity margin.
- The P-REC drift hypothesis is preserved literally on the induced homogeneous
  repair kernel.
- The repair basin is exactly the finite-potential region supported by that
  Lyapunov certificate; global recovery is not claimed.
- Almost-sure eventual hitting is *derived* from finite expected hitting time
  through a proved never-hit `hittingValue = infinity` lemma plus Mathlib
  `ae_lt_top`.
- O4 proves hitting, not post-hit closure.  O5 must perform the mode switch to
  O3 constitutive dynamics.

O4 disposition: **CLEAR / eligible for its own local commit**.
