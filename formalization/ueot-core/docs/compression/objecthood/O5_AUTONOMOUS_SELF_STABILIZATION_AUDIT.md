# Track O / O5 — Finite Autonomous Self-Stabilization Audit

Status: **LOCAL O5 CLEAR — stage gate passed before commit**

Parent local commits:

- O1 `0cc0316`;
- O2 `4a35633`;
- O3 `e2ddbd6`;
- O4 `274f54d`;
- counted-core impact: **NONE**.

## 1. Objective

O5 must eliminate the semantic gap between:

- O3: autonomous controller repair/closure, but only once the physical state is
  already in the source winning kernel `K`;
- O4: physical recovery under a certified repair policy, but not yet connected
  to constitutive controller repair.

The target is one state-dependent autonomous transition law, not a prose-level
two-phase protocol.

## 2. Single hybrid dynamics

`autonomousRepairLift` has only `Unit` external action.

For reflexive state `(x,c)`:

```text
if x in K:
    execute O2 controller repair before physical transition
else:
    execute O4 physical repair policy and carry c unchanged
```

The mode switch therefore depends only on internal state.

## 3. Unified Lyapunov potential

With O4 potential `W` and drift `d`, O5 defines

```text
Phi(x,c) = 0          if x in K and c preserves K
         = d          if x in K and c does not preserve K
         = W(x) + d   if x notin K.
```

This is the key synthesis:

- controller corruption inside `K` consumes exactly one drift unit and reaches
  zero-potential legitimate organization in one step;
- outside `K`, the lifted expectation of `W(fst)+d` is exactly the O4 physical
  repair expectation plus `d`, so the P-REC drift inequality transports to the
  reflexive system.

Therefore the **same hybrid kernel** satisfies P-REC positive drift toward the
full legitimate constitutive domain.

## 4. Intended theorem result

The O5 lifted certificate should yield:

```text
E_z[tau_legitimate] <= Phi(z) / d
```

and, for every state whose physical coordinate lies in the O4 finite-potential
repair basin,

```text
P_z(eventually reaches legitimate organization) = 1
```

under the actual autonomous hybrid trajectory.

Once legitimate, the same dynamics is closed there by O2/O3.

## 5. Package

`SelfStabilizingConstitutiveCertificate` binds:

- the exact O3 controller certificate, including literal
  `K = winningSet P V` provenance;
- an O4 `PhysicalRepairCertificate P K` on that exact kernel.

It does not accept a separate unrelated target set.

## 6. Boundaries

O5 still does not prove:

- that a physical repair certificate always exists;
- that P-OMG failure margins imply one;
- that every state is in the repair basin;
- that the repair law can reconstruct itself after its own deletion;
- ontogenetic self-production;
- universal Objecthood or any counted-core change.

These boundaries are inputs to O6/O8.

## 7. Stage gate

O5 receives a local commit only after focused compile, Objecthood/Compression/
full UEOT builds, proof-escape and axiom checks, governance simulation and
regressions, diff-check, and a dedicated semantic audit of the hybrid mode
switch and lifted P-REC assumptions are all CLEAR.

## 8. Exact local audit result

O5 was developed through a separate `/tmp` feasibility proof before the formal
module was admitted to the stage gate.  The scratch proof exposed and resolved:

- the need to import Mathlib's PMF `Constructions` surface explicitly for
  `PMF.map` / `PMF.toMeasure_map`;
- the measurable-space mismatch for the reflexive lift map, resolved by the
  finite measurable interface rather than by changing the dynamics;
- the exact argument order for `lintegral_map`;
- ENNReal addition-normalization issues in the transported drift inequality,
  resolved using explicit `add_le_add` rather than commutativity-sensitive
  rewriting.

The complete scratch chain, including the hybrid drift, lifted P-REC
certificate, expected repair-time bound, and almost-sure eventual legitimacy,
compiled before the formal file was created.

### Formal-stage BLOCK and repair

The first formal O5 focused compile was **BLOCKED** and therefore not committed.
The formal declarations that accepted a `PhysicalRepairCertificate P K` had
omitted its required `[MeasurableSpace X] [MeasurableSingletonClass X]`
instances.  Lean consequently generated cascading unresolved metavariables in
later drift/basin proofs.  The declarations were repaired to expose the same
typeclass assumptions already present in the successful scratch model.  No
scientific hypothesis was added beyond the actual type of the O4 certificate,
and no O5 conclusion was weakened.

After that repair, the exact O5 working tree passed:

- focused `AutonomousSelfStabilization.lean` compile: **PASS**;
- public `UEOT.V3.Compression.Objecthood` build: **PASS**;
- `UEOT.V3.Compression` build: **PASS**;
- full `lake build UEOT`: **PASS — 9107 jobs**;
- Objecthood proof-escape scan for
  `sorry/admit/axiom/opaque/unsafe/native_decide`: **CLEAR**;
- selected axiom audit on hybrid drift, expected hitting time, almost-sure
  repair, packaged eventual repair, and packaged closure: only standard
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**, including Objecthood/X
  isolation, fork rejection, and concurrency rules;
- simulated exact-candidate governance validation from O4 local head:
  **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

### Hybrid-semantics / assumption audit

- The mode switch uses only the internal physical coordinate `x ∈ K`; no
  external repair-mode command exists.
- Outside `K`, the physical O4 repair policy is the only action source and the
  stored controller is carried rather than consulted.
- Inside `K`, O2 repairs the controller before its action is used, so entering
  `K` with a corrupted controller cannot cause one unsafe post-recovery step.
- The same hybrid Markov trajectory is used for both convergence and closure;
  no two unrelated path laws are spliced informally.
- The lifted potential
  `Phi = 0 / d / (W+d)` gives an exact one-drift-unit controller repair cost and
  transports the O4 P-REC inequality outside `K`.
- `SelfStabilizingConstitutiveCertificate` binds the O4 physical repair target
  to the exact O3/P-PER winning kernel; it cannot silently repair to an
  unrelated invariant set.
- Repair remains conditional on an explicit O4 physical repair certificate and
  its finite-potential basin.  Existence of that certificate is **not** derived
  from viability or P-OMG integrity data.
- The repair transition law itself is treated as intact architecture.  Repair
  of that mechanism, universal Objecthood, and autopoietic self-production
  remain explicit later-stage boundaries.

O5 disposition: **CLEAR / eligible for its own local commit**.
