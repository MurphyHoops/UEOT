# RLSR-T6 — post-audit recompression / final local audit

Status: **LOCAL FULL-GREEN / POST-AUDIT RECOMPRESSION CLOSED**

Canonical base: `main@32a68ed3c740842be9e500e502ea32c0b5434825`

Track: O / Objecthood
Risk tier: L1 additive uncounted research
Counted-core impact: **NONE**

## 1. Why a second tightening cycle was necessary

RLSR0--RLSR9 already proved a valid relative repair-law self-reconstruction
benchmark.  A fresh adversarial review nevertheless found several places where
the theorem architecture was stronger than needed or carried implicit structure:

- action-label equality was used where physical transition-kernel equality is the
  invariant notion;
- the trusted decoder was implicit rather than typed as part of the trust budget;
- the first joint runtime carried a mutable mode/scheduler bit;
- that runtime repaired a stored controller but selected physical actions through
  a parallel direct execution call rather than through the rebuilt controller;
- same-parent recovery used separate global policy-implementation and target-
  preservation assumptions;
- recovered RLSR state was not explicitly projected back into O1 legitimacy;
- whole recovered joint trajectories were not yet related by one exact path-law
  theorem;
- the RLSR subtree was not yet imported by the public Objecthood root.

The T1--T6 cycle closes those issues without changing the frozen counted core.

## 2. Tightened semantic/trust kernel

The trusted boundary is now split explicitly into:

1. `TrustedRepairSubstrate Program X A`, which supplies only execution semantics
   `Program -> X -> A`;
2. `TrustedRepairCodec Program Representation`, which supplies encode/decode
   semantics and `decode_encode` but no distinguished correct program.

The preferred program identity is now

```text
RepairProgramDynamicsEquivalentOn T P K r1 r2
```

meaning that the two programs induce the same physical one-step PMF on every
carrier state.  Action-label equality remains only a stronger adapter.
Preservation validity transports across the weaker dynamics-level equivalence.

## 3. Complete identifiability criterion

RLSR3's collision no-go is strengthened to a complete theorem schema for a
general corruption relation:

```text
exists exact deterministic dynamics-level decoder
iff
all sources compatible with one observation lie in one dynamics-equivalence class.
```

Thus positive reconstruction and information-loss impossibility now share one
criterion.  Triple repetition is one concrete trusted-codec instance; the
existing two-copy collision remains the matching negative benchmark for literal
replication under one arbitrary replacement.

## 4. Mode-free runtime / real causal chain

The preferred runtime is now `safeRepairKernel` on the RLSR1
`SelfReconstructingState` specialization.  There is no mutable scheduler bit.
Before *every* physical transition it:

1. decodes the mutable repair representation;
2. rewrites it to canonical encoded form;
3. rebuilds the stored controller from that decoded program;
4. reads the physical action from the rebuilt controller;
5. performs the physical transition and carries the repaired organization forward.

Hence the actual causal chain is

```text
repair representation -> decoded program -> controller -> physical transition.
```

For triple repetition, arbitrary corruption of one replica plus arbitrary stored
controller corruption is masked before the physical action.  The same stepwise
theorem applies to a fresh one-replica corruption encountered during execution.
This does not yet model a separate stochastic exogenous fault process over entire
trajectories.

The earlier two-mode `jointRepairKernel` remains a compatible historical theorem
surface, but it is no longer the preferred terminal architecture.

## 5. One contract for repair and persistence

The post-audit policy is

```text
repairThenPreservePolicy =
  preserving viability selector, inside K;
  certified recovery policy, outside K.
```

Lean proves that policies inducing equal physical kernels outside `K` have equal
finite survival tails and therefore exactly equal expected first-hitting times.
Consequently `repairThenPreservePolicy` has the same hitting-time semantics as
the original physical-repair policy while automatically preserving `K` after
entry.

The preferred internal-program assumption is one dynamics-level implementation
contract for this composite policy.  That single contract implies both:

- `RepairProgramValid` on the persistence kernel;
- transfer of the selected parent's certified physical-repair basin.

The former independent `himpl + hvalid` pair is therefore not needed by the
strengthened endpoint.

## 6. Tightened same-parent endpoint

`tightened_singleReplica_sameParent_recovery` combines:

- one-replica repair-program corruption;
- arbitrary stored-controller corruption;
- repair-before-action under the mode-free runtime;
- the exact selected formed parent's Track-X semantic law-TV bound;
- almost-sure eventual-permanent physical return under the reconstructed program;
- closure of the recovered organizational target;
- projection of every recovered target state into the established O1
  `legitimateConstitutiveDomain`.

Thus RLSR no longer introduces a parallel notion of final legitimacy: its
recovered target refines the pre-existing Objecthood legitimacy API.

## 7. Full recovered joint path law

For a fixed reconstructed program, the canonical recovered organizational
manifold is canonically equivalent to physical state `X`.  The induced
`recoveredSafeKernel` is proved to be the actual restriction of
`safeRepairKernel` to that manifold after forgetting the subtype proof.

Physical projection is a strong lumping from this recovered organizational
kernel to `stationaryKernel P (T.execute r)`.  The repository's existing
Ionescu--Tulcea naturality theorem then gives exact infinite-path equality:

```text
(recovered organizational path law).map physicalPathProjection
=
reconstructed-program physical path law.
```

The post-reconstruction stochastic dynamics is therefore one rigorously related
joint process, rather than only a collection of one-step correspondences.

## 8. Public integration

`RepairLawSelfReconstruction.All` imports the original RLSR0--RLSR9 surface plus
T1--T5.  `UEOT/V3/Compression/Objecthood.lean` now adds exactly one permitted
Track-O import:

```text
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.All
```

This is the governance-authorized additive-root exception.  It ensures ordinary
`lake build UEOT.V3.Compression` and full `lake build UEOT` automatically cover
RLSR; no separate remembered build is needed after publication.

## 9. Primitive/deletion verdict

The tightening cycle changes no counted mapping, no frozen P-ID disposition and
no proof dependency establishing a fifth primitive.  The four counted generators
remain exactly:

```text
{ M-QD-01, M-TC-01, M-PE-01, M-OI-01 }.
```

RLSR remains an uncounted synthesis of:

- G1 typed trust/semantic/cross-track interfaces;
- G2 constructive coding, reconstruction and autonomous runtime synthesis;
- G3 identifiability/trusted-boundary/no-go results.

No 4->3 deletion witness and no fifth-G0 promotion evidence is created.

## 10. Exact remaining scientific boundaries

Even after tightening, this is **relative endogenous repair-law
self-reconstruction**, not unrestricted autopoiesis.  The theorem still does not
establish:

1. reconstruction of the trusted interpreter/codec semantics themselves;
2. recovery after complete erasure of all dynamics-distinguishing program
   information;
3. arbitrary multi-replica/adversarial corruption beyond the declared code
   correction class;
4. a full stochastic recurrent *fault-process* theorem interleaving exogenous
   faults with every safe transition (although T2 proves stepwise one-replica
   masking whenever such a state is presented);
5. learning a previously absent valid repair law from scratch;
6. resource/energy/computation/thermodynamic closure of reconstruction;
7. reconstruction of the Track-X semantic specification if that machinery is
   itself destroyed;
8. unrestricted turnover of the parent-forming architecture;
9. lineage/self-reproduction;
10. infinite/continuous-state generality of this concrete finite benchmark;
11. universal biological autopoiesis.

The trusted ambient physical dynamics `P` and the object/parent specification
also remain theorem inputs; RLSR does not claim that physical law or semantic
criteria self-generate.

## 11. Final machine validation

The integrated post-audit tree completed all local gates before the T6 commit:

- `RepairLawSelfReconstruction.All` Lean compile: **PASS**;
- RLSR umbrella build: **PASS — 8852 jobs**;
- public `Objecthood.lean` compile with the additive RLSR root import: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS — 9145 jobs**;
- full `lake build UEOT`: **PASS — 9164 jobs**;
- proof-escape scan for `sorry/admit/axiom/opaque/unsafe/native_decide`: **CLEAR**;
- research-governance regression suite: **PASS**;
- `git diff --check`: **PASS**;
- representative post-audit axiom audit on identifiability, dynamics equivalence,
  mode-free fault masking, hitting-time equivalence, one-contract recoverability,
  tightened same-parent recovery, safe-kernel restriction and full path-law
  projection: only standard `propext`, `Classical.choice`, `Quot.sound` as
  applicable.

Warnings shown by the full builds are inherited linter warnings from previously
merged modules; the new T1--T5 modules were individually compiled and tightened
so that their own final focused checks emit no avoidable new theorem-surface
warnings.

## 12. Scientific verdict

The post-audit recompression strengthens the earlier statement

```text
trusted execution semantics
+ redundant mutable repair program
+ one-replica program fault
+ controller/physical damage in the declared basin
-> repair-law reconstruction
-> same-parent recovery
```

into the cleaner architecture

```text
explicit trusted execution + codec semantics
+ dynamically identifiable redundant repair information
+ mode-free repair-before-action runtime
+ one repair-outside/preserve-inside program contract
-> reconstructed controller actually drives physical dynamics
-> eventual-permanent same-parent/O1-legitimate recovery
-> exact recovered joint Ionescu--Tulcea path projection.
```

This is the recommended RLSR terminal surface for publication.
