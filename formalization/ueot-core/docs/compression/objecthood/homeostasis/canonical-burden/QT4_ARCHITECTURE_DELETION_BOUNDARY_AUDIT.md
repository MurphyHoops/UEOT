# QT4 — Architecture / Deletion / Downstream-Boundary Audit

Status: **FINAL LOCAL PASS**

Tracker: #253
Authorization base: main@d082ec1cfbde93a22bec0cab19eea539437db9d5
Prior local stages:
QT0 ae53e34, QT1 c3ab102, QT2 ac98f9b, QT3 53672aa
Stage: QT4
Counted-core impact: **NONE**

## 1. Scientific verdict

The authorized QT0--QT4 quantitative-tightening problem is locally closed.

For every finite recurrent-homeostasis system S whose repair potential is finite
on the retained carrier, QT constructs the canonical single-step fault burden

b* = max_{z in carrier} ( E_F[W(next) | z] - W(z) )_+.

QT0 proves b* is finite and directly yields a valid FaultBurdenCertificate.
QT1 proves b* is no larger than the burden of every certificate in the existing
RH1 interface and gives a strict finite witness where the prior generic
automatic constructor returns burden 1 while b*=0.
QT2 proves this order propagates monotonically through the RH quantitative
outputs: real fault load, load ratio, homeostatic margin, and the exact RH3/RH4
certified damaged-occupation ratio.
QT3 specializes the canonical certificate to Objecthood, reuses the RH3 mean and
RH4 invariant-Cesaro conclusions, and constructs an RH8
HomeostaticOperationalParent on the same already selected parent with only its
burden field tightened.

No RH dynamical law, semantic coupling, parent-selection rule, or path-law
claim is changed.

## 2. Exact meaning of optimality

The word "minimal" in QT is deliberately local and typed.

b* is least among FaultBurdenCertificate burdens for:

- the same recurrent-homeostasis system;
- the same explicit fault kernel;
- the same carrier;
- the same repair potential W.

QT does **not** prove a globally optimal homeostatic certificate over alternative
repair potentials, repair policies, carriers, or parent constructions.

In particular, even with least b*, the ratio

epsilon*b* / ((1-epsilon)*c)

may remain non-sharp because c and W come from the already fixed RH/AR repair
certificate and because the RH3 telescope itself is only a sufficient
occupation bound.

Therefore QT is a genuine canonical tightening of the RH burden coordinate, not
a proof of a globally sharp phase boundary.

## 3. Architecture classification

QT0 is an uncounted G2 quantitative certificate constructor layered on the
closed RH model.

QT1 is an uncounted G1 order/minimality theorem plus a finite strict-separation
witness.

QT2 is an uncounted G1 monotone quantitative consequence layer.

QT3 is an uncounted G2 Objecthood/same-parent specialization layer.

QT4 is audit only.

No QT stage has G0 role. No theorem is promoted into the counted four-generator
core.

## 4. Deletion / nonredundancy audit

No source deletion is justified.

The pre-existing RH1 function faultBurdenCertificateOfUniformBound should remain:
it is a generic existence constructor from any supplied finite uniform potential
bound and does not require computing a canonical maximum.

The QT0 canonical constructor serves a different purpose: it computes the least
burden compatible with the same RH1 certificate inequality under the finite
carrier/potential assumptions.

The layers are therefore complementary:

- RH1 generic constructor: coarse but simple existence interface;
- QT0/QT1 canonical constructor: preferred finite-state quantitative interface.

DownstreamTightening is not redundant with RH5 because RH5 proves properties of
a fixed burden, whereas QT2 compares burdens and proves monotonic improvement.

ObjecthoodCanonicalBurden is not redundant with RH3/RH4/RH8 because it performs
the canonical substitution while preserving the same pre-existing dynamics and
parent.

## 5. Frozen RH boundaries

QT does not alter the RH6 G3 boundary:

mean/invariant damaged-occupation control does not imply almost-sure pathwise
recurrent legitimacy without extra path-level structure.

The strict QT1 witness concerns burden sharpness only and supplies no pathwise
recurrence theorem.

QT also does not upgrade the RH5 sufficient load/margin condition into a
necessary threshold or a sharp phase transition.

RH7's explicit physical-to-semantic statewise coupling remains necessary for
the semantic-homeostasis theorem. QT does not derive that coupling
automatically.

RH8 still uses an externally fixed repair law. QT therefore remains distinct
from repair-law self-reconstruction.

## 6. Same-parent / no-reselection audit

canonicalHomeostaticOperationalParent extends the same
SemanticallyStableSelfRepairingOperationalParent already selected before RH.
The dynamics, persistence kernel, autonomous repair law, semantic child,
semantic kernel, explicit fault kernel, and fault hazard remain unchanged.

Only the burden field is replaced by the canonical Objecthood certificate.

canonicalHomeostaticOperationalParent_system confirms definitionally that the
underlying recurrent-homeostasis system is unchanged.

Thus QT cannot be interpreted as selecting a better parent or changing the
physical dynamics to obtain the tighter numerical bound.

## 7. Frozen counted-core / protected-surface audit

The cumulative origin/main -> QT3 diff leaves unchanged:

- docs/V3_COVERAGE_STATUS.md;
- docs/PID_STATUS.yaml;
- docs/CORE_COMPRESSION_THEOREM_INDEX.csv;
- docs/compression/COMPRESSION_LEDGER.yaml;
- docs/compression/COMPRESSION_RESEARCH_TRACKS.json;
- docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md;
- Compression/Hierarchy.lean;
- Compression/CrossTrack.lean;
- all historical RH0-RH9 theorem files and audits;
- Track-S / Track-H / Track-X source surfaces.

The only theorem-source additions are under
Compression/Objecthood/Homeostasis/CanonicalBurden/, plus import-only additions
to Compression/Objecthood.lean.

The canonical counted state therefore remains:

- source theorem inventory: 106/106;
- unresolved: 0;
- counted minimal core:
  {M-QD-01, M-TC-01, M-PE-01, M-OI-01};
- counted generators: 4;
- no fifth-generator claim.

## 8. Local-history audit

The selected local QT branch contains exactly one stage commit for QT0 through
QT3 before this QT4 audit commit:

ae53e34 -> c3ab102 -> ac98f9b -> 53672aa.

Several obsolete pre-push reflog commits were created during interrupted or
parallel local execution. They are not ancestors beyond the selected stage
chain and must not be used as research authority.

No QT research branch has been pushed at the time of this audit.

## 9. Boundary after QT

QT4 ends the #253 theorem-mutation cycle.

The next main scientific program returns to #246 RLSR planning. RLSR remains
unauthorized until a fresh tracker and separate governance lifecycle explicitly
define the trusted ambient substrate and mutable object-level repair-program
boundary.

QT does not authorize RLSR, EC, OC, AP, or any autopoiesis claim.

## 10. Local validation

- focused Lean compile of ObjecthoodCanonicalBurden.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9124/9124 jobs);
- cumulative proof-escape over all QT0-QT3 theorem modules: **CLEAR**;
- representative QT0-QT3 #print axioms: only
  propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- protected-file / source-isolation cumulative audit: **PASS**;
- full second-pass lake build UEOT: **PASS** (9143/9143 jobs);
- QT4 stage exact-candidate Track-O validation: **PASS**;
- cumulative origin/main -> QT0-QT4 exact-candidate validation: **PASS**;
- final git diff --check: **PASS**.
