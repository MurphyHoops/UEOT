# RLSR-T11 — final post-audit local closure

Status: **LOCAL FULL-GREEN / POST-AUDIT RLSR CLOSED**

Canonical base: `main@32a68ed3c740842be9e500e502ea32c0b5434825`

Track: O / Objecthood
Risk tier: L1 additive uncounted research
Counted-core impact: **NONE**

## 1. Closure scope

This audit supersedes the earlier local closure snapshots by incorporating the
full adversarial tightening cycle T1--T10 on top of RLSR0--RLSR9.

The strengthened theorem architecture is now:

```text
explicit trusted execution + codec + ambient dynamics + target specification
  -> mutable internal repair representation
  -> dynamics-level program identity
  -> exact decoder iff corruption is dynamics-unambiguous
  -> generic trusted-codec recovery semantics
  -> concrete triple one-replica correctable instance
  -> mode-free repair-before-action runtime
  -> repaired controller is the actual physical actuator
  -> repair-outside / preserve-inside unified policy contract
  -> same formed parent + Track-X semantic bound + O1 legitimacy
  -> exact recovered joint Ionescu--Tulcea path law
  -> stochastic recurrent organizational-fault masking inside codec fibre
  -> refined explicit trust-budget / no-infinite-regress closure.
```

## 2. What changed after the first RLSR0--RLSR9 closure

### T1 — semantic and trust tightening

- explicit `TrustedRepairCodec` added beside trusted execution semantics;
- preferred program identity weakened from action-label equality to physical
  transition-kernel equality on the carrier;
- exact deterministic reconstruction for a general corruption relation is
  characterized by an iff: every observation fibre must contain only one
  dynamics-equivalence class.

### T2 — mode-free safe runtime

The preferred runtime no longer carries a mutable scheduler/mode bit.  Before
every physical move it decodes/canonicalizes the repair representation, rebuilds
the controller, and then reads the action from that rebuilt controller.  Thus
`program -> controller -> physical transition` is a real causal chain.

### T3 — one repair/persistence contract

`repairThenPreservePolicy` uses certified recovery behavior outside the target
and a preserving viability controller inside.  First-hitting-time semantics are
proved invariant under this patch.  A single dynamics-level implementation
contract now implies both recoverability and post-hit preservation.

### T4 — tightened same-parent endpoint

The strongest same-parent theorem uses the mode-free runtime and the unified
repair/preserve contract, retains the selected parent's Track-X semantic bound,
and projects the recovered organizational target back into the established O1
`legitimateConstitutiveDomain`.

### T5 — full recovered joint path law

The canonical recovered organizational manifold is strongly lumped to physical
state.  Ionescu--Tulcea path naturality proves exact equality between the
projected recovered-organizational path law and the reconstructed program's
physical path law.

### T6 — public integration / first post-audit full closure

The RLSR umbrella was added to the governance-permitted Objecthood public root,
so normal Compression/full-UEOT builds cover RLSR automatically.

### T7 — runtime dependency isolation

Program-specific physical-recovery adapters were extracted into
`ProgramPhysicalRecovery.lean`.  The preferred mode-free runtime no longer
imports or depends on the historical two-mode `JointRecovery` runtime.  Both
runtimes share a neutral physical-recovery adapter.

### T8 — generic codec recovery and identity basins

Recovery semantics are now generic in `TrustedRepairCodec`.  Three concepts are
explicitly separated:

- decoded-validity basin;
- exact source-program basin;
- dynamics-source basin modulo physical transition equivalence.

Triple repetition is machine-checked as a concrete
`CodecCorrectsCorruption` instance for the single-replica fault relation.

### T9 — recurrent stochastic organizational faults

A state-dependent stochastic fault PMF may be applied before every safe macro
step.  It may arbitrarily corrupt controller and program representation, as
long as it does not directly move physical state and the representation remains
inside the intended codec fibre.

Under that envelope, Lean proves:

```text
faultThenSafeRecoveredPMF = recoveredSafePMF
recurrentFaultSafeKernel = recoveredSafeKernel
```

and therefore exact strong lumping and full projected path-law equality.
The concrete triple instance allows a new arbitrary replica index, bad program
value and controller corruption at every cycle.

### T10 — explicit trust budget

`TrustedRepairContext` enumerates the exact external context:

1. execution/interpreter semantics;
2. codec semantics;
3. ambient physical dynamics;
4. target/object specification.

It contains no distinguished correct `Program`.  A refined dependency graph
proves strict finite rank, well-foundedness, no dependency into trusted nodes,
a genuine repair-of-repair chain, and no infinite regress.

## 3. Current strongest scientific statement

Within the declared finite-state/object specification and a trusted execution +
codec context, a repair program can be stored as mutable object-level data,
suffer correctable representation faults, reconstruct the controller that
actually drives physical dynamics, and restore the same selected parent while
preserving its semantic/O1 identity.

Moreover, recurrent stochastic controller/representation faults can occur at
every cycle without changing the physical trajectory law, provided each fault
remains inside the codec's correctable fibre and does not directly alter
physical state.

This is strictly stronger than the original one-shot RLSR0--RLSR9 benchmark.

## 4. Exact remaining boundaries

The following remain genuinely open and are **not** hidden by the new theorems:

1. faults that destroy trusted execution/interpreter semantics;
2. faults that destroy trusted codec semantics;
3. corruption leaving the correctable/dynamics-identifiable codec fibre;
4. exogenous faults that directly move physical state during the recurrent
   fault process — these belong naturally to RH/QT/joint-mixed-drift analysis;
5. learning or synthesizing a previously absent valid repair law from scratch;
6. reconstruction of the target/semantic specification if that specification
   itself is destroyed;
7. resource/energy/computation/thermodynamic closure;
8. unrestricted structural turnover of the parent-forming architecture;
9. lineage/self-reproduction;
10. infinite/continuous-state generality of the concrete positive benchmark;
11. universal biological autopoiesis.

Thus the correct scientific label remains **relative endogenous repair-law
self-reconstruction with fault-contained recurrent organizational maintenance**,
not absolute self-foundation or unrestricted autopoiesis.

## 5. Primitive/deletion verdict

No new result changes the frozen counted compression core:

```text
{ M-QD-01, M-TC-01, M-PE-01, M-OI-01 }.
```

T7--T10 improve adapter structure, codec generality, fault containment and trust
accounting, but they neither generate a fifth counted primitive nor prove a
4->3 deletion.  RLSR remains an uncounted G1/G2/G3 synthesis.

## 6. Exact local validation

On the post-T10 source tree:

- RLSR proof-escape scan: **CLEAR**;
- `git diff --check`: **PASS**;
- research-governance regression suite: **PASS**;
- exact branch validator: **PASS — 40 changed paths**;
- protected counted ledger/coverage/index/registry/workflow surfaces: **ZERO DIFF**;
- representative axiom audit covering T1/T3/T4/T5/T8/T9/T10: only standard
  `propext`, `Classical.choice`, `Quot.sound` as applicable;
- `lake build UEOT.V3.Compression`: **PASS — 9149 jobs**;
- full `lake build UEOT`: **PASS — 9168 jobs**.

Warnings in global builds are inherited repository linter warnings.  New T7--T10
modules were individually focused-compiled and their avoidable local warnings
were removed before stage commits.

## 7. Local lifecycle disposition

RLSR theorem development should now be considered **locally frozen** unless a
new scientific defect is discovered.  Additional work on direct physical fault
processes, resource closure, self-generated repair-law learning or autopoietic
turnover should be opened as new research problems rather than silently folded
into this RLSR closure.

The GitHub tracker must remain open until publication governance is completed:
push one existing branch, open one coherent L1 PR, obtain exact-head CI and
independent review, merge, validate resulting main, close #257 and retire the
branch.  No separate authorization/final-governance PR is required.
