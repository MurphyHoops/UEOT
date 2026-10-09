# Objecthood post-reflection: historical research reconciliation (2026-10-10)

**Status:** PROVENANCE RECONCILED / CURRENT PROOFS ALREADY IN MAIN /
NO NEW THEOREM / UNCOUNTED. **Authority:** the current Lean declarations,
not a superseded local integration report.

## Why this is here

The local branch local/post-reflection-scientific-audit at
8654125fe648929e8e55d81a2d711ca09293f922 retained
formalization/ueot-core/docs/compression/POST_REFLECTION_LOCAL_INTEGRATION_AUDIT.md.
That report is absent from main. Its historical baseline
3cbec434411980af701d0342bbdd9531e1a9a813 and local integration PASS
are **not** certificates for the present main.
On main@66c999d3c2911d7f732c66a827689a8ae6613892, all five
PostQTTightening Lean module blobs in this archived branch match main
byte-for-byte. The current Objecthood.lean root evolved, so replaying the
old branch would overwrite subsequent imports.

The existing modules are:

- Objecthood/PostQTTightening/CanonicalCertificateOptimality.lean
- Objecthood/PostQTTightening/GeneralCausalObjecthoodClosure.lean
- Objecthood/PostQTTightening/CanonicalJointMixedDrift.lean
- Objecthood/PostQTTightening/StrictJointMixedDriftWitness.lean
- Objecthood/PostQTTightening/JointMixedDriftDownstream.lean

All paths are relative to formalization/ueot-core/UEOT/V3/Compression/.
Blob identity does not by itself constitute an independent semantic audit.

## Scientific value already present in canonical Lean

**Canonical homeostasis margin.**
canonical_homeostaticMarginReal_isGreatest and
canonical_homeostaticMarginReal_pos_iff_exists_certificate optimize over
the specified fixed-system RH1 fault-certificate class, not every
physical homeostasis process.

**Same-parent causal endpoint.**
generalCausal_semantic_bound_and_eventually_always_same_parent_repair
and generalCausal_failingDeletion_semantic_and_eventuallyAlways_sameParent
reuse the finite controlled-PMF causal premises. Neither produces a new
physical repair law unconditionally.

**State-coupled mixed drift is strictly sharper.**
For a fixed damaged-occupation coefficient kappa, the canonical joint
mixed-drift residual is the least uniform upper bound on the positive
statewise mixed-kernel drift excess. In
CanonicalJointMixedDrift.lean, theorems
canonicalJointMixedDriftResidual_le_of_bound and
canonicalJointMixedDriftResidual_le_canonicalFaultEnvelope certify
optimality and comparison under their explicit premises. In
StrictJointMixedDriftWitness.lean, the finite three-state witness has
canonicalFaultBurden = 1 and canonicalJointMixedDriftResidual = 0
at faultHazard = 1/2 and the existing standard coefficient, while the
separated envelope equals 1/2. The strict difference is a valid
conditional finite witness, not a physically calibrated universal law.

**Downstream boundaries.**
JointMixedDriftDownstream.lean propagates the optimized residual into
finite-horizon occupation, asymptotic average and invariant Cesaro
statements. These do not imply eventual pathwise safety, universal
necessity of a phase transition or optimally choosing kappa itself.

## Not re-integrated

The old report also describes Track-S primitive reward/transition
defect to GOA work under one common literal finite micro model. That
work is already present in current main under Track S; this Track-O
document does not re-own, duplicate or weaken that separate API.

Existing authoritative Objecthood stage audits already on main:
OAB_ENDPOINT_CLOSURE_AUDIT.md, OC_CANONICAL_JOINT_MIXED_DRIFT_AUDIT.md,
OD_STRICT_JOINT_MIXED_DRIFT_WITNESS_AUDIT.md and
OEG_JOINT_MIXED_DRIFT_DOWNSTREAM_AUDIT.md in
docs/compression/objecthood/post-qt-tightening/.

## Provenance and status

Exact blob identity is tested using git rev-parse on each of the five
source paths at local/post-reflection-scientific-audit versus main.
The original historical report and all historical commit objects are now
also retrievable from the permanent GitHub archival tag
archive/ueot-post-reflection-20261004, resolving to
8654125fe648929e8e55d81a2d711ca09293f922. In any fresh clone:

    git fetch origin tag archive/ueot-post-reflection-20261004
    git show archive/ueot-post-reflection-20261004:formalization/ueot-core/docs/compression/POST_REFLECTION_LOCAL_INTEGRATION_AUDIT.md

The source Git object and its SHA-1 are independent of any author's
local branch. A local full-history bundle remains an optional extra
recovery path, not the only evidence.

**Promotion classification:** Additive provenance-only Track O L1;
counted-core impact NONE. No existing source, ledger, frozen Core
or mathematical theorem changed.

## Immutable per-file Git blob identity receipt

The following full Git SHA-1 blob OIDs were obtained with git rev-parse <commit>:<path> on 2026-10-10. The receipts are now part of this tracked file, not a claim requiring the authors private .git archive to inspect. A public reviewer can at least independently verify the main-side Git blob for every path from the pinned main commit.

| Path (under PostQTTightening/) | Historical blob OID | main blob OID |
|---|---|---|
| CanonicalCertificateOptimality.lean | 59d76648834a4dcd4cf08232e4c130c69d7198e1 | 59d76648834a4dcd4cf08232e4c130c69d7198e1 |
| GeneralCausalObjecthoodClosure.lean | 0eeea59c95f83a10aa6f8ba45a921c0c39503405 | 0eeea59c95f83a10aa6f8ba45a921c0c39503405 |
| CanonicalJointMixedDrift.lean | fc57c020a9bfec045ec7cfc281f70fc47629ed6e | fc57c020a9bfec045ec7cfc281f70fc47629ed6e |
| StrictJointMixedDriftWitness.lean | cb176c2ba26ebf282c7ebcb133ac0eee0fd66bf1 | cb176c2ba26ebf282c7ebcb133ac0eee0fd66bf1 |
| JointMixedDriftDownstream.lean | 461bb78428142e39aadd8490292018f5f09d98f4 | 461bb78428142e39aadd8490292018f5f09d98f4 |

Commit used for the historical column: 8654125fe648929e8e55d81a2d711ca09293f922. Canonical comparison main commit: 66c999d3c2911d7f732c66a827689a8ae6613892. The Git bundle is a supplementary local restore artifact, not the only source of this recorded comparison. No implication of type or theorem equivalence beyond exact blob identity is claimed.
