# Track O / O2 — Autonomous Controller Self-Repair Audit

Status: **LOCAL O2 CLEAR — stage gate passed before commit**

Parent:

- O1 local commit: `0cc0316`;
- tracker: #230;
- counted-core impact: **NONE**.

## 1. Exact target

O1 established a functional legitimate domain

```text
L(P,K) = {(x,c) | x in K and c preserves K}
```

and proved that the old Track-X lift has closure but cannot converge from a
non-preserving controller.

O2 closes only the **controller-corruption** gap while the physical state is
already inside `K`.

## 2. Repair construction

From the fixed-kernel hypothesis

```text
viabilityStep P K = K
```

the existing P-PER theorem already proves existence of a deterministic
stationary preserving controller. O2 selects one canonical witness internally.

For a stored controller `c`:

```text
repair(c) = c                   if c preserves K
          = canonical witness   otherwise.
```

The physical action is selected **after** this repair decision, so a corrupted
controller cannot cause one unsafe transition before being repaired.

The runtime external action type remains `Unit`.

## 3. Target theorem surface

O2 must prove:

1. the canonical witness preserves `K`;
2. all repaired controllers preserve `K`;
3. already preserving controllers remain unchanged;
4. repair dynamics has no informative external action;
5. on legitimate states, repair dynamics equals the old constitutive lift;
6. from every state `(x,c)` with `x in K`, one step enters `L(P,K)`;
7. `L(P,K)` is thereafter closed;
8. every finite-time marginal from time 1 onward lies in `L(P,K)`.

## 4. Scientific interpretation

If validated, O2 establishes the finite-state **controller-level convergence**
half missing from O1. Together O1+O2 give closure + convergence against
controller-only transient corruption.

The legitimate target remains a functional equivalence class. O2 does not force
recovery to one historical selector when the existing controller is already
valid.

## 5. Explicit boundaries

O2 still does not prove:

- recovery of a physical state outside `K`;
- finite hitting-time recovery from a damage basin;
- repairability from P-OMG margins alone;
- computable/efficient synthesis of the classical choice witness;
- repair of the repair law itself;
- ontogenetic self-construction or universal Objecthood.

The repair rule is part of the constitutive transition law.  O8 must separately
audit the stronger question of whether that repair mechanism itself can be
damaged/reconstructed.

## 6. Stage gate

O2 may receive its own local commit only after focused compile, Objecthood and
Compression builds, full UEOT regression, proof-escape scan, selected axiom
audit, research-governance validation/regressions, diff-check, and an explicit
assumption/nonclaim review all pass on the exact O2 working tree.

## 7. Exact local audit result

The first O2 compile attempt was **BLOCKED** and therefore not committed.  It
identified three concrete proof/implementation defects:

1. method notation on `PMF.map` resolved ambiguously through the subtype
   representation rather than the intended PMF transformation;
2. a pair-controller equality was being discharged by brittle `subst` use;
3. the proposed time-shift recursion proof rewrote the nested
   `stationaryStateLaw` recurrence at the wrong syntactic level.

The implementation was repaired by:

- using the repository-standard `bind (fun y => PMF.pure ...)` construction;
- transporting controller equality explicitly;
- proving the after-one marginal invariant directly by induction on the PMF
  support recursion, rather than by a fragile time-shift rewrite.

The repaired O2 working tree then passed:

- focused `ControllerRepair.lean` compile: **PASS**;
- public `UEOT.V3.Compression.Objecthood` build: **PASS**;
- `UEOT.V3.Compression` build: **PASS**;
- full `lake build UEOT`: **PASS — 9104 jobs**;
- Objecthood proof-escape scan: **CLEAR**;
- selected axiom audit on canonical-controller preservation, one-step repair,
  and all-marginals convergence: only standard `propext`,
  `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**, including O/X isolation and
  Objecthood fork rejection;
- simulated exact-candidate governance validation from local O1 base:
  **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

### Assumption / semantic audit

- The repair controller is derived from `P`, `K`, and the fixed-kernel proof;
  it is not a runtime argument.
- A valid stored controller is left unchanged, so repair does not collapse the
  legitimate organization class to one arbitrary representative.
- Repair is applied before the physical transition, preventing one corrupt
  action from escaping `K` during controller repair.
- The proof remains finite-state and classical/noncomputable.  No claim of an
  efficient executable repair algorithm is made.
- The physical state is assumed to start in `K`; O2 does not smuggle in O4
  physical recovery.

O2 disposition: **CLEAR / eligible for its own local commit**.
