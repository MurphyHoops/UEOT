# Track O / O6 — P-OMG Failure Envelope / Repairability Boundary Audit

Status: **LOCAL O6 CLEAR — stage gate passed before commit**

Parent local commits:

- O1 `0cc0316`;
- O2 `4a35633`;
- O3 `e2ddbd6`;
- O4 `274f54d`;
- O5 `166bd24`;
- counted-core impact: **NONE**.

## 1. Required negative result

P-OMG-01 and P-OMG-02 describe failure geometry:

- P-OMG-01 reconstructs a monotone failure family from inclusion-minimal
  destructive deletion sets;
- P-OMG-02 makes distance to a metric failure set 1-Lipschitz.

Neither theorem contains an O4 repair policy, a P-REC Lyapunov function, or an
O5 repair-basin membership fact. O6 therefore keeps

```text
failure(D)
```

and

```text
damage(D) lies in repair basin
```

as distinct predicates.

`p_omg_01_does_not_supply_repairability` proves that a complete P-OMG-01
minimal-failure witness coexists logically with an explicit nonrepairability
hypothesis.

To prove that this boundary is nonvacuous rather than merely propositional, a
finite `Bool × Unit` witness constructs:

- a fixed viability kernel;
- a valid `PhysicalRepairCertificate` whose finite-potential basin excludes
  one damaged state;
- a monotone deletion failure predicate with a genuine failing deletion;
- the P-OMG-01 minimal destructive witness for that deletion;
- a metric representation `y = 0` with positive P-OMG-02 integrity margin to
  the declared failure set `{1}`;
- an explicit metric-space damage realization sending that **same** `y = 0`
  to a damaged state outside the repair basin.

Thus **failure characterization and positive integrity margin do not imply
repairability**.

## 2. Explicit positive repairability condition

For a deletion realization

```text
damage : Finset V -> ConstitutiveState X A
```

O6 defines `RepairableDeletion` by membership of the realized physical state
in the O4/O5 repair basin.

Only after this extra condition is supplied does O6 combine:

```text
P-OMG-01 failure witness
+ O5 basin membership
-> minimal destructive subset witness
+ almost-sure autonomous return to legitimate organization.
```

The minimal destructive subset itself is not asserted to be repairable; the
actual realized failing deletion `D` is the state whose repairability must be
certified.

## 3. Integrity margin versus repair margin

For a metric representation space `Y` and damage realization

```text
damage : Y -> ConstitutiveState X A
```

define the O5-repairable representation set

```text
Rset = {y | physical(damage y) lies in repair basin}.
```

The repair margin is

```text
repairMargin(T) = dist(T, complement Rset).
```

The combined robustness radius is

```text
integrityRepairMargin(T)
  = min(integrityMargin(failure,T), repairMargin(T)).
```

Under the explicit nonempty-set side conditions required by the frozen
P-OMG-02 interface, O6 proves that

```text
dist(T,S) < integrityRepairMargin(T)
```

implies simultaneously:

- `S` is not in the P-OMG failure set;
- `damage S` remains in the O5 repair basin;
- therefore the O5 autonomous hybrid trajectory from `damage S` reaches the
  legitimate constitutive domain almost surely.

## 4. Scientific interpretation

O6 separates two robustness notions that must not be conflated:

1. **integrity margin** — distance before entering a declared failure set;
2. **repair margin** — distance before leaving the region whose damage remains
   recoverable by the explicit O4/O5 repair certificate.

The meaningful robust radius for a self-repair claim is the smaller of the
two, not the integrity margin alone.

## 5. Explicit nonclaims

O6 does not prove:

- that minimal destructive sets synthesize repair policies;
- that positive P-OMG integrity margin implies repairability;
- that all failures are inside the repair basin;
- monotonicity of repairability under adding more deleted mechanisms;
- global recovery outside the finite-potential basin;
- repair of the repair mechanism itself;
- universal Objecthood, autopoiesis, or any counted-core change.

## 6. Stage gate

O6 receives its own local commit only after focused compile,
Objecthood/Compression/full UEOT builds, proof-escape scan, selected axiom
provenance audit, research-governance regression and exact-candidate simulation,
`git diff --check`, and an independent semantic review of the P-OMG/O5 boundary
are all CLEAR.

## 7. Exact local audit result

O6 first passed as a complete `/tmp` feasibility proof. Two proof-normalization
issues were exposed there before any repository mutation: P-OMG-02 had to be
changed explicitly from `|integrityMargin| <= dist` to an `infDist` inequality,
and the contradiction with a strict margin was made by `not_lt_of_ge` rather
than a brittle arithmetic tactic. The repaired scratch proof compiled in full.

The formal O6 tree then passed:

- focused `FailureRepairabilityBoundary.lean` compile: **PASS**;
- public `UEOT.V3.Compression.Objecthood` build: **PASS — 3551 jobs**;
- `UEOT.V3.Compression` build: **PASS — 9089 jobs**;
- full `lake build UEOT`: **PASS — 9108 jobs**;
- Objecthood proof-escape scan for
  `sorry/admit/axiom/opaque/unsafe/native_decide`: **CLEAR**;
- selected axiom audit on the negative P-OMG-01 boundary, positive deletion
  bridge, combined-margin theorem, a.s. repair theorem, and both concrete
  separation witnesses: only standard `propext`, `Classical.choice`,
  `Quot.sound`;
- research-governance regression suite: **PASS**;
- simulated exact-candidate governance validation from O5 local head
  `166bd24`: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

### P-OMG / repairability semantic audit

- P-OMG-01 is used only to recover minimal destructive-set structure; no
  repair policy or basin membership is inferred from it.
- `RepairableDeletion` is evaluated on the realized damaged state itself.
  Containment of a minimal destructive subset does not imply that the minimal
  subset, a larger deletion, or any other damage realization is repairable.
- P-OMG-02 remains a distance-to-failure theorem. `repairMargin` is introduced
  separately as distance to the complement of the O5-repairable
  representation set.
- The combined robustness radius is literally the minimum of those two
  independent margins. This prevents a positive integrity margin from being
  renamed as a repair margin.
- The concrete finite witness proves nonvacuously that complete P-OMG-01
  failure structure exists, and separately that one and the same metric
  representation can have positive P-OMG-02 integrity margin while its explicit
  damage realization lies outside a valid repair basin.  The margin and damage
  conjuncts therefore no longer range over unrelated inputs.

## 8. Exact-head Codex P2 repair

PR #232 exact-head Codex review on `e1f5405` correctly found that the original
toy theorem conjoined a positive margin for `0 : ℝ` with nonrepairability of a
separate `Finset Unit` deletion realization.  Although both facts were true,
that conjunction did not prove they referred to the same representation.

The review fix introduces

```text
metricDamage : ℝ -> ConstitutiveState Bool Unit
```

and changes `positive_integrity_margin_and_no_repair` to prove simultaneously

```text
0 < integrityMargin {1} 0
and
0 notin repairableRepresentationSet repairCertificate metricDamage.
```

Thus the exact point `0` enjoying the positive integrity margin is also the
exact point whose realized damage is outside the repair basin.  This closes the
review finding without strengthening P-OMG-02 or weakening the O6 negative
boundary.
- Almost-sure return to legitimate organization is invoked only after explicit
  O5 basin membership has been established.

O6 disposition: **CLEAR / eligible for its own local commit**.
