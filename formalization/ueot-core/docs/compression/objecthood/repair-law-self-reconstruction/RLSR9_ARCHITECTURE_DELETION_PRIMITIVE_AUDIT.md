# RLSR9 — architecture / deletion / primitive audit

Status: **HISTORICAL RLSR0--RLSR9 BASELINE — SUPERSEDED BY POST-AUDIT TIGHTENING**

> Post-audit note: the T1--T6 recompression cycle strengthens this baseline.
> In particular, the preferred runtime is now mode-free, program identity is
> available at the physical-kernel level, repair/preservation use one composite
> contract, recovered states project to O1 legitimacy, and the recovered joint
> Ionescu--Tulcea path law is formalized.  See
> `RLSR_T6_RECOMPRESSION_FINAL_AUDIT.md` for the authoritative final state.

Canonical base: `main@32a68ed3c740842be9e500e502ea32c0b5434825`

Track: O / Objecthood
Risk tier: L1 additive, uncounted
Counted-core impact: **NONE**

## 1. What RLSR now proves

RLSR closes the specific O8 boundary "repair of the repair-producing mutable
program" for one finite, explicitly typed benchmark relative to a trusted
execution/decoder substrate.

The machine-checked chain is:

```text
trusted execution semantics (contains no correct program)
  -> mutable repair-program representation
  -> carrier-relative behavioral program identity / validity
  -> identifiability no-go when corruption erases behavioral information
  -> triple-redundant one-replica-correcting representation
  -> exact one-step program reconstruction basin
  -> one two-mode autonomous joint kernel
       restoreProgram -> executeProgram
  -> reconstructed internal program drives physical recovery
  -> eventual-permanent target preservation under explicit validity
  -> finite dependency graph / no infinite repair regress
  -> exact same formed parent + unchanged Track-X semantic bound
```

For the concrete single-replica benchmark, ordinary controller state may be
arbitrarily corrupted.  Restore mode decodes the surviving mutable program
representation, rewrites the representation to a consistent codeword, binds the
ordinary controller to the decoded program, and does not move physical state.
Execute mode then uses that reconstructed internal program itself to select
physical actions.

## 2. The positive result is not an external-policy smuggling theorem

The trusted substrate stores only

`Program -> X -> A` execution semantics.

It does not contain a distinguished correct program or repair policy.  The
runtime `jointRepairKernel` receives only the current mutable joint state plus
ambient dynamics.  The correct repair program survives through the redundant
mutable representation and is reconstructed from that representation.

At RLSR8, a theorem-level bridge states that this reconstructed program
behaviorally implements the already-certified physical repair policy of one
exact selected formed parent.  That bridge is a specification assumption tying
the benchmark program to the parent; it is not a runtime external control
channel.

## 3. Identifiability boundary

RLSR3 proves a necessary information condition, not merely a toy counterexample:
for any deterministic exact behavioral reconstructor, equal corrupted
observations must imply carrier-relative behavioral equivalence of the original
programs.

Therefore arbitrary destruction cannot be repaired without surviving
information.  This prevents the RLSR theorem from collapsing into an
information-from-nothing claim.

RLSR4 then supplies one explicit surviving-information mechanism.  Triple
literal replication corrects one arbitrary replica replacement.  A separate
two-replica collision theorem proves that literal two-copy replication cannot
solve the same exact arbitrary-single-replacement problem for two distinct
source programs without additional side information.

## 4. Recovery-basin audit

RLSR5 does not claim universal reconstruction.  Its exact program basin is

```text
{ representation e | decode(e) is behaviorally valid }
```

and Lean proves an iff between basin membership and one-step entry into the
valid redundant-program target.

RLSR6 adds the physical condition separately: the physical state must lie in
the finite-expected-hitting basin of the *same reconstructed program*.  The
joint basin therefore exposes rather than hides the two independent information
requirements:

1. enough surviving program information to decode a valid repair law;
2. enough physical recoverability for that law to return the state to the
   declared object target.

## 5. Same-parent identity audit

RLSR8 binds the reconstructed program to the exact
`SemanticallyStableSelfRepairingOperationalParent` already selected by Track X.
The terminal theorem gives simultaneously:

- membership of the damaged state in the explicit RLSR joint basin;
- exact first autonomous reconstruction of program + controller;
- the existing Track-X `epsilon / kappaMin` semantic law-TV bound for that same
  selected parent;
- almost-sure eventual-permanent physical membership in that parent's
  persistence kernel under the reconstructed internal program;
- closure of the fully recovered joint target under the same joint kernel.

A `PhysicalRepairCertificate` guarantees hitting but does not itself state
post-hit target preservation.  RLSR8 therefore correctly keeps behavioral
program validity as an independent premise for the stronger eventual-always
claim.

## 6. Repair-regress audit

The explicit dependency graph is

```text
trusted substrate -> repair program -> controller
                                \----> physical
```

The graph has a strictly increasing finite rank away from the trusted boundary.
Lean proves well-foundedness, existence of a genuine two-edge repair-of-repair
chain, absence of any three-edge chain, and absence of an infinite regress.

This is **relative self-reconstruction**.  The trusted interpreter/decoder
semantics, mathematical logic and ambient physical laws are not claimed to
reconstruct themselves.

## 7. Architecture-role classification

| RLSR surface | Role | Reason |
| --- | --- | --- |
| trusted substrate | **G1 boundary/interface** | types immutable execution semantics; contains no repair solution |
| mutable representation + behavioral equivalence | **G1 semantic bridge** | states what object-level repair information and identity mean |
| observation collision theorem | **G3 boundary/no-go** | excludes exact reconstruction after total behavioral information loss |
| triple redundancy + program recovery basin | **G2 constructive synthesis** | provides one concrete recoverable internal program representation |
| two-replica collision | **G3 lower-bound boundary** | shows the chosen repetition-code fault model has a nontrivial information threshold |
| two-mode joint kernel | **G2 autonomous synthesis** | orders program reconstruction before internal-program-driven physical recovery |
| finite dependency graph | **G3 trusted-boundary closure** | blocks infinite repair regress without pretending absolute self-foundation |
| same-parent Track-X composition | **G1/G2 cross-track synthesis** | restores one already certified parent contract; does not generate Track-X semantics |

**No RLSR theorem is presently a G0 counted primitive.**

## 8. Deletion / nonredundancy matrix

| Delete | What remains | What breaks | Verdict |
| --- | --- | --- | --- |
| trusted execution substrate | mutable symbols/program replicas | no typed meaning for executing/decoding a repair program | explicit nonredundant trusted boundary |
| behavioral validity/equivalence | code reconstruction can still be stated syntactically | no operational criterion that reconstructed code preserves object identity | nonredundant semantic bridge |
| identifiability no-go | positive triple benchmark remains | architecture could falsely suggest arbitrary information erasure is repairable | nonredundant G3 boundary |
| redundant program representation | parent repair certificate remains | no object-internal surviving source from which a damaged repair law is reconstructed | nonredundant positive mechanism |
| program reconstruction kernel/basin | redundancy remains static | no autonomous object-level program reconstruction dynamics | nonredundant G2 mechanism |
| joint mode/order semantics | program and physical repair theorems remain separately | no explicit runtime rule guaranteeing program repair precedes use of a corrupted controller/program | nonredundant G2 composition |
| program-specific P-REC hitting certificate | program can be reconstructed | no theorem that its execution recovers an arbitrary damaged physical state | retained physical-recovery adapter remains necessary |
| program validity on target | finite-time hitting remains | no eventual-permanent identity theorem after first hit | nonredundant preservation premise |
| finite trusted-boundary dependency theorem | positive chain remains | repairer-of-repairer scope is left implicit | nonredundant G3 scope closure |
| Track-X formed-parent / semantic certificate | generic functional reconstruction remains | no theorem identifies the restored organization with the same formed/semantic parent | nonredundant specification layer |

The matrix shows a genuine synthesis of independent ingredients rather than a
new primitive that subsumes them.

## 9. Counted-core consequence

The frozen compression core remains exactly

```text
{ M-QD-01, M-TC-01, M-PE-01, M-OI-01 }.
```

RLSR introduces no counted mapping, changes no frozen P-ID disposition, and
supplies no deletion witness showing that one of the four counted generators is
redundant.  Conversely, it does not independently generate multiple frozen
source families, so there is no evidence for a fifth G0.

Any future G0 promotion would require a separate L3 lifecycle and fresh
ablation against the then-live counted theorem DAG.

## 10. Exact boundaries after RLSR

RLSR closes one O8 boundary but does **not** establish full autopoiesis.  The
following remain explicitly outside the theorem:

1. reconstruction of the trusted interpreter/decoder substrate itself;
2. reconstruction from complete loss of behaviorally distinguishing program
   information;
3. arbitrary multi-replica, adversarial or recurrent program corruption during
   execution;
4. learning/synthesizing a previously absent valid repair program from scratch;
5. resource, energetic, computational or thermodynamic closure of reconstruction;
6. reconstruction of the Track-X semantic certificate if that semantic
   machinery itself is destroyed;
7. unrestricted structural turnover of the parent-forming architecture;
8. lineage/self-reproduction;
9. infinite/continuous-state generality of the concrete joint benchmark;
10. universal biological autopoiesis.

A full Ionescu--Tulcea path-law equality for the enlarged joint state is also
not separately formalized in this cycle.  What is proved is the contractually
required autonomous ordered chain: exact first joint reconstruction,
`jointRepairKernel_restored` identifying every restored execute step with the
reconstructed-program physical kernel embedded in joint state, the corresponding
physical a.s. eventual-always theorem, and recovered-joint-target closure.  A
full joint path pushforward theorem would be a strengthening, not a missing
RLSR0--RLSR9 contract item.

## 11. Scientific verdict

RLSR upgrades the prior O1--O8 statement

```text
intact repair law + damaged object state -> repair
```

to the strictly stronger relative statement

```text
intact trusted interpreter/decoder
+ surviving redundant object-level repair information
+ one-replica repair-program damage
+ arbitrary ordinary-controller damage
+ program-specific physical recoverability
-> internal repair-program reconstruction
-> controller rebinding
-> reconstructed-program-driven physical recovery
-> eventual-permanent return to the same certified parent target
```

subject to the explicit same-parent behavioral bridge and Track-X specification.

That is a real closure of **repair-law self-maintenance relative to a trusted
substrate**, while the stronger autopoiesis claims above remain honestly open.

RLSR9 primitive verdict: **uncounted G1/G2/G3 architecture; no fifth G0.**

## 12. Final local validation

The exact RLSR0--RLSR9 working tree completed the following local gates before
this stage commit:

- RLSR umbrella `RepairLawSelfReconstruction.All`: **PASS**;
- `UEOT.V3.Compression`: **PASS — 9131 jobs**;
- full `lake build UEOT`: **PASS — 9150 jobs**;
- RLSR proof-escape scan for `sorry/admit/axiom/opaque/unsafe/native_decide`:
  **CLEAR**;
- research-governance regression suite: **PASS**;
- `git diff --check`: **PASS**;
- representative axiom audit:
  - observation-separation / exact-reconstruction no-go: no axioms;
  - triple correction, two-copy lower bound, exact reconstruction basin, joint
    recovery, same-parent terminal theorem: only standard `propext`,
    `Classical.choice`, `Quot.sound` as applicable;
  - no-infinite-regress theorem: `propext` only.

Warnings emitted during Compression/full builds are pre-existing repository
linter warnings.  New RLSR theorem files were individually tightened when Lean
reported avoidable theorem-surface or simp warnings.

## 13. Local lifecycle disposition

RLSR0--RLSR9 is scientifically/formally closed on the local research branch.
The GitHub tracker remains open by governance design: tracker closure, branch
retirement and canonical-main status require the later publication PR,
exact-head CI/review, merge and resulting-main regression.  No RLSR branch is
pushed by this local closure.
