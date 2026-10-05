# RLSR-T1 — trust / dynamics / identifiability tightening

Status: **LOCAL PASS**

## Changes

1. The trusted boundary now has an explicit `TrustedRepairCodec Program Representation`
   containing only encode/decode semantics plus `decode_encode`; it still contains no
   distinguished correct repair program.
2. Triple repetition is packaged as `tripleRepairCodec`, making the decoder trust
   explicit instead of leaving it as an untyped ambient helper.
3. Program identity gains the weaker and physically more meaningful
   `RepairProgramDynamicsEquivalentOn`: two programs are equivalent when they induce
   the same physical transition PMF on the object carrier, even if their action labels
   differ.
4. Preservation validity transports across this dynamics-level equivalence.
5. The RLSR3 collision no-go is strengthened to a complete criterion for a general
   corruption relation: an exact deterministic dynamics-level decoder exists iff each
   corrupted observation is compatible with only one carrier-level transition behavior.

## Independent scientific audit

Action-label equality remains as a stronger adapter but is no longer the most primitive
behavioral notion.  The new equivalence matches UEOT's quotient principle: operational
identity should be invariant under representational relabelings that leave reachable
physical dynamics unchanged.

The decoder existence theorem uses classical choice only to select one representative
from each nonempty observation fibre; its necessity direction is constructive.
