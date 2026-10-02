# Track O / O7 — Formation × Identification × Self-Repair Synthesis Audit

Status: **LOCAL O7 CLEAR — stage gate passed before commit**

Parent local commits:

- O1 `0cc0316`;
- O2 `4a35633`;
- O3 `e2ddbd6`;
- O4 `274f54d`;
- O5 `166bd24`;
- O6 `416c97a`;
- counted-core impact: **NONE**.

## 1. Exact synthesis target

O7 consumes the merged Track-X
`OperationalFormedPersistentParent`. It does not reconstruct or reselect a
parent.

The O7 package `SelfRepairingOperationalParent` stores:

1. that exact operational formed-parent certificate;
2. one `PhysicalRepairCertificate` whose target is **definitionally the exact
   `operational.persistence.K`** already attached to the selected parent.

Therefore the repair target cannot silently drift to a different viable kernel
or a different formed candidate.

## 2. Preserved pre-repair semantics

O7 re-exposes without modification:

- response-generated parent provenance;
- family-wide interaction separation;
- the positive interaction-isolation consequence when the formed-candidate
  family is nontrivial;
- the original P-PER winning-kernel identity and seed through the existing
  persistence certificate.

The O3 controller certificate used by O7 is rebuilt on
`operational.persistence.K` itself. Hence the O5 self-stabilization package has
the same kernel by definitional equality rather than by a post-hoc isomorphism.

## 3. Repair semantics

For every damaged reflexive state whose physical coordinate lies in the
explicit O4 basin, O7 proves on the actual O5 hybrid path law:

```text
almost surely, eventually there exists n such that
  physical(omega_n) in operational.persistence.K
  and
  controller(omega_n) preserves that exact K
  for dynamics operational.parent.
```

Thus the restored state satisfies the same selected parent's legitimate
constitutive contract.

The same autonomous kernel is closed on that legitimate domain after entry.
O7 also inherits the quantitative expected hitting-time bound.

## 4. O6 failure integration

For a monotone deletion failure predicate, a repairable failing deletion can be
threaded through O7 to obtain simultaneously:

- a P-OMG-01 inclusion-minimal destructive subset witness;
- almost-sure return of the realized damage to the legitimate domain of the
  same formed parent.

Repairability remains an explicit basin condition; P-OMG failure data is not
used to synthesize it.

## 5. End-to-end chain now represented

O7 formally binds the narrower evidence-backed chain

```text
lower-level response provenance
-> formed parent
-> interaction-identifiable parent family
-> parent-specific P-PER persistence kernel
-> transient certified damage
-> autonomous O5 repair
-> restored legitimate organization of the same parent.
```

This is the O7 operational chain. It does not add objective, fitness,
teleological, or universal Objecthood semantics absent from Track X.

## 6. Explicit boundaries

O7 does not prove:

- that every operational formed parent admits a physical repair certificate;
- that interaction identification implies repairability;
- that P-OMG margins synthesize repair;
- that repair restores one historical controller rather than the functional
  legitimate controller class;
- that the repair mechanism itself survives deletion;
- ontogenetic self-production or biological autopoiesis;
- any fifth counted generator.

## 7. Stage gate

O7 receives its own local commit only after focused compile,
Objecthood/Compression/full UEOT builds, proof-escape and selected axiom audits,
research-governance regression and exact-candidate simulation, `git diff
--check`, and an explicit same-parent/same-kernel semantic audit are all CLEAR.

## 8. Exact local audit result

O7 was first checked as a complete `/tmp` synthesis.  The only pre-repository
failure was a Lean parsing issue in the expanded restored-state projection
(`omega n |>.1`); after replacing it by the explicit projection `(omega n).1`
and unfolding legitimate-domain membership at the bridge, the full scratch
chain compiled.  No scientific statement was weakened.

The formal O7 working tree then passed:

- focused `FormedParentSelfRepairSynthesis.lean` compile: **PASS**;
- public `UEOT.V3.Compression.Objecthood` build: **PASS**;
- `UEOT.V3.Compression` build: **PASS — 9090 jobs**;
- full `lake build UEOT`: **PASS — 9109 jobs**;
- Objecthood proof-escape scan for
  `sorry/admit/axiom/opaque/unsafe/native_decide`: **CLEAR**;
- selected axiom audit on exact-kernel identity, preserved interaction
  isolation, expected repair time, same-parent path restoration, expanded
  original-kernel restoration, restored closure, O6 deletion integration, and
  O7 package construction: only standard `propext`, `Classical.choice`,
  `Quot.sound`;
- research-governance regression suite: **PASS**;
- simulated exact-candidate governance validation from O6 local head
  `416c97a`: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

### Same-parent / same-kernel semantic audit

- O7 stores the existing `OperationalFormedPersistentParent`; it does not
  construct, choose, or substitute a second parent.
- `physicalRepair` is typed against
  `dynamics operational.parent` and `operational.persistence.K`.  Therefore
  both repair dynamics and repair target are attached to the exact selected
  Track-X parent.
- The O3 controller certificate is rebuilt using the original persistence
  seed, subset proof, fixed-kernel proof, and literal winning-set equality.
- `repair_kernel_eq_operational_kernel` is definitional (`rfl`), so there is no
  hidden equivalence or transport that could change object identity.
- Formation provenance and interaction-identifiability remain fields of the
  same stored operational certificate and are re-exposed unchanged.
- The path theorem restores the legitimate domain for
  `dynamics operational.parent`; its expanded form returns to the original
  `persistence.K` with a controller preserving that exact kernel.
- The same autonomous O5 kernel is closed after restoration.
- O6 failure information is threaded through only after explicit basin
  membership; failure detection is still not treated as repair synthesis.

O7 disposition: **CLEAR / eligible for its own local commit**.
