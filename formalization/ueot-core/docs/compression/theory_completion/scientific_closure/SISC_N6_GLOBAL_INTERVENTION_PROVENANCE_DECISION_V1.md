# SISC N6 — Global intervention and transfer-provenance scientific decision

Date: 2026-10-09. Local additive research branch: research/sisc-local-20261008. Frozen 106/106 Core theorem governance and four counted Compression generators are unchanged.

## 1. Existing components rechecked and reused (no unnecessary reproving)

- P4 InverseObjecthood/Identifiability and InverseObjecthood/NonIdentifiabilityBoundaries distinguish observational evidence equality, literal-candidate identification and physical object identity. N6-A calls the existing validity-aware no-go and uses the equality Setoid, rather than rebuilding a second inverse-objecthood theory.
- SI-2 SISCFormationIdentityBridge already proves the common-response triangle, LocalResponseGap and unique_formed_target_of_local_gap. N6-B calls these original theorems directly to prove uniqueness of a registered parent candidate set.
- N3 RegisteredCausalCandidates already implements certified/ambiguous/uncovered threshold decisions, and N4 proves samplewise calibration, false-decision bounds and gap-dependent power. N6 does not claim to replace their finite decision machinery.
- The frozen P-STAT BoundedLossTwoSided.measure_exists_candidate_bad_le provides a two-sided finite-coordinate Hoeffding union bound. N6-D invokes it directly, not as a new concentration result.
- P8 LineageEvolution already provides typed SameObject, parentOf, OffspringOf and ReproductiveTransmission. N6-B's conversion to P8 genealogy explicitly takes an independently verified audit-to-lineage soundness mapping, plus separately established identity difference.
- P12 AutopoiesisClosure already has conditional finite lifecycle, resource/repair and parent bridges. It does not deduce the authenticity of a program/material-transfer log from a passive Markov transition.
- CrossTrack ParentBinding/ParentSemantic no-go statements and N5 full-microprocess no-go exclude identifying parenthood from an observed transition alone. N6 preserves these boundaries.

## 2. N6-A: passive equivalence vs active discrimination

A pinned two-parent Boolean model has identical passive response 0 for both parents, while a separately declared active intervention yields response 0 vs 1. Lean proves P4 literal parent labels cannot be identified from passive evidence but can be separated by the active response interface.

This is a formal interventional *response model*. No actual physical intervention happened; its manipulation fidelity, compliance and absence of hidden interference remain external scientific assumptions.

## 3. N6-B: intersecting intervention response and externally authenticated transfer evidence

FiniteInterventionTransferAudit registers a finite candidate source set, a per-child independently attested material/program-transfer predicate, predicted response fingerprints for each parent across probes, measured child intervention responses, and a tolerance. It contains **no preselected correct parent or tp**.

The constructed auditedSourceCandidates enumerates only candidates simultaneously: (a) registered; (b) transfer-attested to child; and (c) fitting every declared intervention response within tolerance.

Using the already proved SI-2 gap theorem, Lean derives a singleton accepted set under registration, reliable transfer evidence, one compatible parent fingerprint and a gap >2 tolerance to every other possible fingerprint. It also proves that two distinct accepted parents cannot be called uniquely identified.

The P8 parentOf and offspring bridge requires external proof that authenticated transfer records really imply the chosen P8 parentOf semantics, and (for reproduction vs repair) independent inequality of identity labels. No assumed equivalence between response and biological/material genealogy is hidden in the result.

## 4. N6-C: actual three-way nonvacuity and abstention

The local toy audit registers *both* Boolean parent hypotheses and deliberately gives both permissive transfer records, so provenance alone cannot select a winner.

- Passive-only probe: both parents exactly fit; there cannot be a singleton accepted source.
- Active probe: two reference responses differ and only one matches observations; SI-2 LocalResponseGap is proved and the accepted source set equals a singleton.
- A separate, intentionally permissive P8 toy lineage interpretation plus an identity difference gives a conditional offspring result. The toy relation is NOT asserted as physical genealogy.

These are fully compiled Lean proofs, not hypothetical pseudo-examples.

## 5. N6-D: finite IID experimental units and power theorem

A sampled version constructs empirical means of each registered intervention coordinate and intersects them with the same audited transfer records. Under:
- N>0 independent repeated experimental units with a joint vector of measurable [0,1] probe responses,
- the registered sample law correctly matching the response model of the actual parent,
- a genuine authenticated transfer trace, registration and SI-2 source fingerprint gap >2u for other candidates,

Lean proves:

Pr[ accepted source set != {actual parent} ] <= 2 |Probes| exp(-2 N u^2).

The proof reuses the same old P-STAT finite union-bound surface and SI-2 local gap. Its penalty depends on the number of independent registered probe coordinates rather than number of parent candidates.

**Key limitation:** the theorem's data type requires a joint intervention-response record on repeated independent experimental units. Ordinary observational samples with one realized treatment do not provide every counterfactual probe response for each unit. Estimating causal effects in that setting needs explicit randomized assignment, experimental identification, dose/compliance data, dependence handling or potential-outcome assumptions; those have not been proved here. Merely labelling a passive measurement an intervention does not satisfy N6-D.

## 6. Scientific state

N6 proves stronger conditions for *operational parent-source identification* relative to declared interventions and externally authenticated transfer evidence. It does NOT infer actual material/program transfer or complete physical ancestry from the kernel; does NOT certify the physical meaning of P8 parentOf, nor source program self-reconstruction, P12 lifecycle viability, self-repair, GOD or GOA.

Next evidence-facing tasks, not unnecessary abstract theorem count inflation:
1. Specify actual intervention protocol, observed treatment assignment, compliance/time stamps, independent transfer instrumentation and anti-spoof custody.
2. Provide explicit probability model/valid tail theorem for samples produced by that protocol; handle temporal dependence and unavailable counterfactual outcomes correctly.
3. Conduct falsifiable intervention controls: swap candidate source, block purported transport, change or disable program/material channel and compare against preregistered response distributions.
4. Verify mechanism-to-genealogy physical semantics separately; then instantiate the already existing P8/P12 interfaces.
5. Preserve abstention when candidates are observationally or physically non-identifiable.

## 7. Reproducibility and governance

V8 source inventory hashes 598 first-party Lean files and 106779 source lines, with 3605 lexical theorem/lemma declarations, 596 public-root reachable modules, zero missing local imports and zero import cycles. Lexical theorem declarations are not the 106 frozen governed Core theorems.

The local exact-head V10 audit checks the full Lake build, selected new theorem axioms, prohibited proof escape scan, prior V1–V7 source digests, C7 tamper/negative controls and legacy Compression/Finalization regression suites. A green result is formal source verification by the same developer environment, NOT independent empirical confirmation.

Disposition: LOCAL_FORMAL_PASS only after the exact-head gate; SCIENTIFIC_FINAL=HOLD; real_world_support=UNVERIFIED; independent_review=REVIEW_PENDING; CLOUD_PUSH=HOLD.
