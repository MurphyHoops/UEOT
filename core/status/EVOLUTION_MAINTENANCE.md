# UEOT Core v3 — Evolution and Formalization Maintenance Contract

Date: 2026-09-10
Status: active maintenance policy for the `core/v3-maintenance` branch
Canonical baseline: UEOT Core Mathematics v3.0

## 1. Purpose

UEOT Core v3 is the current canonical mathematical baseline, not an immutable historical relic. Formalization, counterexamples, prior versions, and later domain work may reveal a missing hypothesis, an overstrong statement, a reusable theorem, or a clearer formulation. Those discoveries must feed back into Core without silently changing what v3 means.

The maintenance loop is therefore bidirectional:

`historical derivation -> v3 semantic audit -> Lean theorem -> counterexample/failed proof -> Core erratum or next-version proposal -> re-formalization`.

The Lean library is a verifier and theorem-discovery aid. It is not authorized to redefine UEOT merely because a different statement is easier to prove.

## 2. Core invariants that must survive version evolution

The following are architectural invariants. A proposed revision that destroys one of them is not a routine cleanup and requires an explicit theory-level decision.

1. **Dynamics first.** The substrate is a process/history/intervention model before an object label is introduced.
2. **Being through persistent identity, not static material identity.** An object may change microscopic state or constituents while retaining an identity-supporting persistence/viability certificate.
3. **Omega is a certificate family, not one mandatory geometric loop.** Topological loops, invariant cores, viability, recurrence, QSD/metastability, or recovery mechanisms may implement identity-supporting closure in different model classes.
4. **Canonical predictive identity precedes arbitrary macrostate choice.** For a designated future/protocol family, an exact object macrostate must be at least sufficient to recover the canonical predictive response/core.
5. **Predictive sufficiency alone is not objecthood.** Persistence, boundary/interface, realizability/robustness, and where relevant causal/interventional requirements remain logically separate axes.
6. **Canonical state does not imply a unique physical boundary.** Redundancy, symmetry, and gauge-like recodings can produce multiple minimal realizations; uniqueness requires extra assumptions such as an appropriate intersection property or interventions.
7. **Object-level teleology is downstream of object/control closure.** Value, GOD and GOA are defined only after admissible futures, rewards/objectives and a control-sufficient quotient are specified. They must not be used circularly to define the object whose quotient they optimize.
8. **Composition requires irreducibility, not correlation alone.** A parent object must carry joint predictive/causal structure not eliminable into independent children plus interface variables under the declared criterion.
9. **Representation covariance is restricted to information-preserving admissible recodings.** Lossy coarse-graining may legitimately change a detected object and must be recorded as resolution dependence rather than called observer invariance.
10. **Core remains domain-neutral.** Quantum-, biological-, cognitive-, social- or engineering-specific axioms do not enter the generic Core unless explicitly reclassified as generic assumptions with an independent justification.

## 3. Historical derivations that must be preserved

Earlier versions contain results that should remain available even when the canonical exposition is reorganized. They are treated as a theorem/counterexample archive, not as competing active specifications.

### H1. No-go: contraction is not universally necessary for persistence

Quasiperiodic/neutral recurrent examples and noncontractive recoverable systems show that a single global contraction condition cannot be promoted to a universal objecthood axiom. Contraction remains a strong sufficient certificate for one class of objects.

### H2. No-go: predictive closure alone is not objecthood

An i.i.d. process can admit a trivial exact predictive statistic while carrying no nontrivial persistent identity. This guards against collapsing UEOT into predictive-state reconstruction alone.

### H3. No-go: strong instantaneous coupling alone is not a persistent individual

Large instantaneous correlation/coupling can coexist with complete temporal resampling. Persistence is an independent requirement.

### H4. Boundary nonuniqueness under redundant encoding

A unique canonical predictive quotient can have multiple inclusion-minimal physical supports. Physical-boundary uniqueness therefore needs extra structural/interventional assumptions.

### H5. Exact controlled quotient theorem

When rewards and controlled transitions close exactly on an object quotient, optimal value is fiber-constant and macro-optimal policies lift to micro-optimal policies. This is the rigorous bridge from object representation to object-level GOD/control.

### H6. Approximate quotient value-loss bound

Approximate reward and transition closure yield an explicit discounted value-loss bound. This is the correct quantitative interface for learned/Object-RG macrostates and must not be replaced by a qualitative "approximately same" claim.

### H7. Parent predictive emergence

A parent state may contain predictive information not recoverable from child predictive cores and shared interface variables. This provides an irreducibility criterion for composition, while not by itself proving full parent objecthood.

### H8. Resolution-flow lesson

Minimal carriers can change and even proliferate as spatial/measurement resolution is refined. The invariant target is therefore predictive identity plus a compatible realization flow/plateau, not necessarily a unique fixed microscopic boundary at infinite resolution.

## 4. Formalization feedback classes

Every Lean difficulty must be classified before Core text is edited.

### F0 — proof engineering only

The source theorem is correct at the stated strength; Lean needs a library lemma, type coercion, measurable instance, algebraic normalization, or a different proof route. **Core text does not change.**

### F1 — hidden standard hypothesis

The proof requires a standard mathematical hypothesis that the prose implicitly used, e.g. standard Borel, measurability, finite measure, compactness, nonexplosion, or generator-domain regularity. **Add the hypothesis explicitly in the next Core revision or an erratum candidate; do not weaken the theorem silently in Lean.**

### F2 — theorem splits by model class

A prose statement conflates two-sided flows with one-sided semiflows, finite with general state spaces, pointwise with a.e. claims, or observational with interventional semantics. **Split the statement into correctly typed cases while preserving the motivating UEOT claim.**

### F3 — counterexample to the stated theorem

A valid counterexample satisfies all written assumptions and violates the conclusion. **The proposition cannot remain canonical as written. Record the counterexample and prepare a versioned correction.**

### F4 — useful strengthening

Lean proves a genuinely stronger theorem without extra assumptions. **Keep v3 source semantics unchanged; record the stronger result as a reusable Core lemma and consider promotion in the next version.**

### F5 — historical recovery

An earlier version contains a rigorous theorem/no-go omitted from v3. **Recover it only if it is domain-neutral and consistent with the v3 dependency direction. Add it as a next-version candidate or explanatory guardrail, not by altering an existing P-ID silently.**

## 5. Versioning rule

The exact v3 source identity remains fixed. Any change to a v3 theorem's mathematical meaning, assumptions, or conclusion requires one of:

- an explicit erratum record tied to the existing P-ID, while preserving the original v3 text/hash; or
- a new Core version (normally v3.1 for compatible corrections/clarifications, v4.0 for architectural changes).

Existing P-IDs are stable and never recycled. If a statement is corrected, provenance must retain: original text/hash, reason for correction, counterexample or proof obligation, revised statement, and Lean declarations verifying the revision.

## 6. Bidirectional maintenance loop

For every active P-ID:

1. Read the exact v3 source statement and proof sketch.
2. Trace relevant predecessors in Mathematical Foundations I–IV and unified versions.
3. Extract historical lemmas, counterexamples and assumptions that materially support the source theorem.
4. Formalize the exact v3 statement first, using helper lemmas as needed.
5. Classify every mismatch as F0–F5.
6. If F0/F4, keep v3 unchanged and continue proof work.
7. If F1/F2/F3/F5, create a Core maintenance note before changing any canonical statement.
8. Re-run the pinned Lean build, replay, axiom audit, and 106-P-ID coverage gate.
9. Only after source-semantic review may a P-ID be promoted to `proved`.
10. Feed accepted corrections/strengthenings into the next Core release and re-formalize that release from its own immutable source hash.

## 7. Current audit notes from active proof lanes

These are maintenance findings, not automatic edits to v3.

- **P-DYN-02:** finite CTMC semigroup/generator/block-sum equivalence is consistent with the source direction. The macro block-sum matrix must also be verified to satisfy CTMC generator sign and row-sum conditions; this is a source-semantic obligation, not an optional strengthening.
- **P-PER-01:** forward invariance of an omega-limit set follows for a semiflow, but exact equality under time translation needs the precise source assumptions. If v3 intends a genuinely one-sided semiflow theorem with equality, the reverse-inclusion proof/assumptions must be checked carefully; inverse-time arguments only solve a stronger two-sided-flow model and cannot silently replace the source statement.
- **P-PER-03:** the finite deletion/viability recursion matches v3. Finite-time marginal invariance is an intermediate lemma; the source statement requires probability-one nonexit for all discrete times and the reverse maximality direction.
- **P-REC-02:** a pointwise differentiable Gronwall theorem is not enough if v3 states local absolute continuity plus an a.e. Dynkin drift inequality. The AC/a.e. bridge must be formalized at the source regularity, or a missing regularity assumption must be reported as F1/F2.
- **P-INFO-01:** exact chain identity and epsilon-retention are on the right path, but the discrete entropy lower bound requires the separate inequality `I(M;Y) <= H(M)` in a compatible finite/discrete entropy formalization.
- **P-FAC-01:** value invariance should follow from primitive representation covariance through induced path-law covariance; assuming the final path-law equality as an extra hypothesis would prove a weaker theorem than the source intends.

## 8. Merge discipline

Proof branches may run in parallel, but Core maintenance is serialized conceptually:

- proof branches can add helper theorems freely;
- source-level `proved` promotion requires semantic audit against canonical v3;
- Core text changes require an F1/F2/F3/F5 maintenance record;
- historical results are archived with provenance;
- domain-specific results stay outside Core;
- no proof hole, new UEOT axiom, `native_decide` shortcut, or regenerated source substitute may be used to satisfy completion gates.

## 9. Release objective

The target is not merely `106/106` Lean labels. The target is a self-consistent UEOT Core in which:

`core idea continuity + exact source provenance + machine-checked theorems + explicit counterexample boundaries + controlled version evolution`

all agree.
