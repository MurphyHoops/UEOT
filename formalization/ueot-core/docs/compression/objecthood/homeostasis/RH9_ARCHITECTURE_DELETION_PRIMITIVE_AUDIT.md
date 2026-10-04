# RH9 — Architecture / Deletion / Primitive Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Planning parent: #246
Authorization base: main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f
Prior local stages:
RH0 faebae1, RH1 f23fbce, RH2 a3156e5, RH3 4961e3f,
RH4 24307a6, RH5 67a1fbb, RH6 a6c1397, RH7 f0cdd41, RH8 3e9e954
Counted-core impact: **NONE**

## 1. Scientific verdict

The authorized RH0--RH9 problem is locally closed.

Within the finite controlled-PMF / Objecthood semantics inherited from the
closed GCR cycle, RH proves a recurrent-fault maintenance architecture with:

- explicit repair kernel Q;
- explicit fault kernel F;
- fault hazard epsilon;
- inherited finite repair potential W and nonzero finite repair drift c;
- finite fault-burden certificate b;
- exact repair/fault mixture expectation;
- mixed one-step homeostatic drift;
- finite-horizon damaged-occupation telescope;
- asymptotic mean damaged-occupation bound;
- finite PMF to row-stochastic matrix / Cesaro bridge;
- invariant Cesaro cluster laws satisfying the certified occupation bound;
- a sufficient homeostatic load ratio/margin with explicit no-go witnesses;
- an explicit separation between mean homeostasis and pathwise recurrent
  legitimacy;
- semantic homeostasis only under an explicit statewise semantic coupling;
- one HomeostaticOperationalParent extending the same already selected
  semantically-stable self-repairing parent.

This is maintenance under continuing faults. It is not repair-law
self-reconstruction.

## 2. Stage classification

RH0 is a G2 typed recurrent-fault system/carrier adapter over the closed GCR
repair domain.

RH1 is a G2 finite fault-burden certificate.

RH2 is a G1 quantitative bridge / G2 certificate composition: it proves the
exact mixed expectation and one-step drift budget.

RH3 is a G1 quantitative consequence: finite-horizon telescope and asymptotic
mean occupation control.

RH4 is a G1 semantic bridge from exact finite PMF evolution to the existing
M-OI / finite Cesaro invariant-law machinery.

RH5 is a G2 certified sufficient-load interface plus G3 boundary evidence from
explicit no-go witnesses.

RH6 is a G3 semantic-boundary result: mean homeostasis is formally weaker than
pathwise recurrent legitimacy. The explicit two-class path-law counterexample
prevents this boundary from being erased by terminology.

RH7 is a G1/G2 semantic coupling theorem: physical damaged occupation controls
average semantic defect only after an explicit statewise coupling assumption.

RH8 is a G2 end-to-end same-parent synthesis.

RH9 is audit only.

No RH stage has G0 architecture role. No RH theorem is counted merely because
it composes several prior interfaces.

## 3. Exact retained G3 boundary

RH does **not** prove

mean long-run damaged occupation control
  => almost-sure infinitely-often return to the legitimate domain.

RH6 proves this implication is invalid in general by a normalized path-law
counterexample: half the mass can remain damaged forever while the mean damaged
probability remains bounded by one half.

Therefore the exact retained boundary after RH is:

**pathwise recurrent legitimacy requires additional path-level structure
beyond the RH mean/invariant occupation certificate.**

This is a retained G3 boundary, not an unfinished proof obligation hidden by
the RH closeout.

## 4. Sufficient margin is not a phase transition

RH5 defines certified repair capacity, fault load, margin and load ratio.

Positive margin implies load ratio below one under the stated finite positive
repair-capacity assumptions.

The theorem is sufficient only. The RH cycle proves no converse establishing a
necessary threshold and no sharp thermodynamic/statistical phase transition.

Explicit no-go witnesses record that:

- epsilon = 1 destroys certified repair capacity;
- c = 0 destroys certified repair capacity;
- a fault may leave the declared repairable carrier;
- even within a finite carrier, a fault can make finite burden impossible if
  the declared potential is infinite on a reached state.

## 5. Same-parent synthesis and RLSR boundary

RH8 does not create a second operational parent.

HomeostaticOperationalParent is a dependent extension of the already selected
SemanticallyStableSelfRepairingOperationalParent. The parent, persistence
kernel, autonomous repair law, semantic child and semantic kernel remain those
of the base parent. RH adds only the recurrent fault model and its burden
certificate.

RH8 additionally proves that the same selected parent can instantiate the RH7
invariant semantic-homeostasis theorem.

This still uses an externally fixed repair law. It does **not** represent,
corrupt, identify, reconstruct or regenerate the object-level repair program.
Therefore RH8 is not RLSR and cannot be renamed autopoiesis.

## 6. Frozen counted-core audit

The cumulative origin/main..RH8 source diff leaves the following protected
surfaces unchanged:

- docs/V3_COVERAGE_STATUS.md;
- docs/PID_STATUS.yaml;
- docs/CORE_COMPRESSION_THEOREM_INDEX.csv;
- docs/compression/COMPRESSION_LEDGER.yaml;
- docs/compression/COMPRESSION_RESEARCH_TRACKS.json;
- docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md;
- Compression/Hierarchy and all Track-S / Track-H / Track-X source surfaces.

The canonical counted state inherited from authorized main therefore remains:

- source theorem inventory: 106/106;
- unresolved: 0;
- counted minimal core: exactly
  {M-QD-01, M-TC-01, M-PE-01, M-OI-01};
- counted generators: 4;
- minimal-core state: frozen.

RH introduces no fifth generator and requests no promotion audit.

## 7. Source isolation audit

The cumulative RH theorem-source diff is confined to:

- Compression/Objecthood/Homeostasis/*.lean;
- import-only additions in Compression/Objecthood.lean.

RH audit evidence is confined to:

- docs/compression/objecthood/homeostasis/*.md.

There are no RH mutations to historical O/ER/AR/GCR theorem files, their audit
evidence, source tracks S/H/X, the counted ledger, coverage, theorem index,
research governance, validator policy or workflows.

## 8. Deletion / nonredundancy audit

No RH source deletion is justified.

- RecurrentFaultSystem is the typed physical model and carrier contract.
- FaultBurden isolates the genuinely independent fault-side finiteness
  certificate.
- MixedHomeostaticDrift contains the exact one-step mixture identity and drift
  inequality.
- FiniteHorizonHomeostasis performs the no-subtraction telescope and mean bound.
- CesaroHomeostasis is the exact PMF-to-existing-M-OI adapter; it does not
  duplicate FiniteCesaroInvariant or OccupationLimitInvariance.
- CertifiedHomeostaticMargin names only the sufficient scalar certificate and
  keeps its no-go boundaries explicit.
- HomeostasisSemantics is not redundant with SemanticHomeostasis:
  the former separates mean and pathwise recurrence, while the latter adds an
  explicit physical-to-semantic defect coupling.
- HomeostaticOperationalParent is the same-parent synthesis layer and reuses
  the prior parent rather than replacing it.

The read-only preflight and obsolete local scratch/worktree variants are not
repository source and require no source deletion.

## 9. Local duplicate-history normalization

During local development several pre-push duplicate commits/worktrees were
created while recovering lost execution context. They are not part of the
selected research branch history.

The selected RH branch has exactly one ordered stage commit for RH0 through RH8
before this RH9 commit:

faebae1 -> f23fbce -> a3156e5 -> 4961e3f -> 24307a6 ->
67a1fbb -> a6c1397 -> f0cdd41 -> 3e9e954.

An older local worktree remains parked at RH3 and is operationally obsolete; it
must not be used for further research work.

RH4's audit body had already recorded every mandatory gate as PASS, but its
status line still said FINAL LOCAL CANDIDATE. RH9 normalizes that single status
line to FINAL LOCAL PASS without changing RH4 theorem source or its proof
history.

## 10. Boundary after RH

RH9 ends this authorized theorem-mutation cycle.

The next scientific program is RLSR repair-law self-reconstruction, but it is
not authorized by #248. Any RLSR work must begin from a fresh tracker and
governance lifecycle after the RH research PR, resulting-main checks, tracker
close and separate RH final-governance closeout are complete.

RLSR must first distinguish immutable trusted ambient substrate from the mutable
object-level repair program. It may not require the mathematical evolution laws
themselves to reconstruct themselves.

EC, OC and an explicit AutopoieticObject contract remain later still.

## 11. Local validation

RH9 is an audit stage. Its terminal and cumulative gates pass:

- focused Lean compile of HomeostaticOperationalParent.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9120/9120 jobs);
- cumulative proof-escape over all RH0--RH8 theorem modules: **CLEAR**;
- representative RH0--RH8 #print axioms: only
  propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- protected-file/source-track cumulative diff audit: **PASS**;
- full second-pass lake build UEOT: **PASS** (9139/9139 jobs);
- RH9 exact-candidate Track-O validation: **PASS**;
- cumulative origin/main -> RH0--RH9 exact-candidate validation: **PASS**;
- final git diff --check: **PASS**.

No RH research branch has been pushed at this point.
