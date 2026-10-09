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
The original historical report is recoverable from the retained local
branch or the locally verified archive
.git/UEOT_DIVERGENT_BRANCH_ARCHIVE_20261010.bundle. The bundle is not a
GitHub-hosted artifact.

**Promotion classification:** Additive provenance-only Track O L1;
counted-core impact NONE. No existing source, ledger, frozen Core
or mathematical theorem changed.
