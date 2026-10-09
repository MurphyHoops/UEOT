# UEOT Core v3 — Full-module Lean duplication audit (2026-10-10)

Pinned main: 48b582beabec2ebae61ab0d51081b83356fcb3e1.
Status: READ-ONLY RESEARCH EVIDENCE; ZERO Lean theorem, ledger, or open-port changes.

## All-module enumeration

All **633** first-party modules were scanned, encompassing **111,565 raw
lines**, **85,421 non-comment nonempty lines**, **2,343 imports**, and **5,553
lexically declared items**: 3,675 theorem, 284 lemma, 1,407 def, 48 abbrev,
121 structure, and 18 inductive. There are **zero exact duplicate files**
and zero exact matches after stripping comments and normalizing whitespace.

Lean Environment prefix UEOT contains 9,977 named constants:
6,408 theorem constants, 3,099 definition constants, plus constructors etc.
The separate CrooksJarzynski namespace contains 324 constants.
This includes machine-generated _simp_ and _proof_ helpers, not only
manually established independent mathematics.

Source-compiled symbol reconciliation: **5,310 exact public fully-qualified
matches + 50 recovered qualified-name matches; 192 private source
declarations; one unresolved public candidate**. Of these, **3,793**
are publicly resolved authored source theorem proofs. Original FKRG misses
names after qualified section constructs and a UEOT-only environment
enumeration misses the CrooksJarzynski namespace. One unresolved candidate:
UEOT.V3.FreeInformationValue.integrable_finset_sup.

## Repeated theorem statements

Strict original Elaborated Expr render equals: **6 groups, 13 items**.
After erasing only binder display names and metadata (preserving
expression constants, binder info and type structure): **37 groups,
77 theorem declarations**, i.e. **40 extra theorem names**. Thirty-two
groups cross files (67 declarations, 46 files); five are in-file.

For all 40 representative-to-duplicate pairs, the compiled Lean Meta.isDefEq
check succeeded (**40/40 PASS**), confirming that the *elaborated theorem
types are definitionally equal* in the pinned Lean environment, not merely
similar printed signatures. The checked pair list and a repeatable Lean
verification script are included in this research snapshot. This still
does NOT prove the corresponding proof bodies independently derive new
science, nor license public API deletion.

Real proof-term direct dependency extraction from all 77 cluster members
shows **26 in-cluster direct proof-reference edges**; 23 clusters reuse
another equivalent-type theorem directly. **14 clusters lack such an
edge**, warranting manual independent derivation/adapter assessment.
An equal theorem type does NOT establish that one API name can safely be
deleted. Keep counted Core and public consumers stable.

**11 of the Core 106 registered theorem names** occur in these groups:
P-ALI-02, P-GOA-01, P-PER-02, P-KL-05, P-CTL-03, P-API-01,
P-DYN-04, P-DYN-03, P-REF-02, P-BRG-02 and P-STAT-02.
This is counted theorem-interface duplication, not a proof that the 106
registered obligations are false or should be recounted.

## Proof-level reuse across all public authored source theorems

3,793 actual theorem values were traversed by Lean to extract
first-party proof constants. **2,422** depend directly on at least one
other registered public source theorem, **1,371** do not; there are
**4,886** direct registered-source-theorem edges, **2,760** different
public source theorem targets, and **23,542** first-party constant
occurrences in the proof-term dependency sets. The 1,371 may directly
use Mathlib, private proof helpers, or first-party definitions and
must NOT be equated with gratuitous independent reproofs.

The lexical proof scan identified **242 concise alias-like proof
candidates** and 135 trivial one-line proofs, which overlap other
categories. Names alone generated 50 cross-file collision groups
(102 occurrences); namespaces and types often differ.

## The 14 equal-type clusters without direct in-cluster reuse

**P1 high-value candidate consolidation:**
- OccupationLimitInvariance p_goa_01_via_occupationLimit vs
  FiniteCesaroInvariant.p_goa_01; Feller occupation-limit invariance
  vs PersistenceOccupation; p_per_02_via_occupationLimit vs base
  p_per_02. Review all three with M-OI minimal generator boundaries.
- TransportCertificate processInterface_approx_via_twoStage and
  processInterface_exact_source_via_twoStage vs ProcessInterface
  P-API-01; dynamicsCrossScale_approx_via_twoStage and
  dynamicsCrossScale_exact_via_factor vs DynamicsCrossScale P-DYN-04.
  Some approximate proofs are 60+ lines, not mere aliases.
- InformationPacking.tvDist_symm and StatisticalDefect.tvDist_symm
  independently reproduce nearly the same total-variation symmetry
  proof. A prime low-risk reuse prototype.

**P2 abstraction-route tests (may legitimately be independent):**
- AlignmentParentValue P-ALI-02 core/terminal vs Compression
  ValueAlignment M-VA directionalScore-based derivations (two groups).
- ContractiveFixedPoint Bellman residual/unique fixed-point vs
  FiniteDiscountedControl, using abstract ContractiveWith (two groups).
- PathError P-DYN-03 vs Compression.TransportPathError.
- Two physical-seed program no-go names both invoke one generic no-go.

Do not delete a wrapper if it is an intentionally typed downstream
API, a registered minimal-generator witness, or a weaker/stronger
assumption variant. First test direct reuse in Lean with exact types,
source interface preservation, downstream consumers, negative controls,
and full CI.

## Nearby theorem statements that are NOT equal types

A limited constant-bucket and token-triple screening produced 23
high-similarity cross-file pairs, of which 8 are already in the 37 exact
binder-normalized groups. **Fifteen distinct remaining near-type pairs**
require individual checks for weaker hypotheses, stronger results, or
different conclusion directions. Examples:
- RewardInfinite.policy_values_affine vs TeleologicalEquivalence adapter;
- CommonBottleneckRank P-DDH-04 vs C5DualDriveTest rank necessity;
- EvolutionReproductiveMartingale P-EVO-04 vs PositiveEigenstructure;
- PredictableOLSConfidence vs Good-Gram-controlled confidence;
- Several upper/lower concentration inequalities, which are emphatically
  NOT automatically equivalent.

These 15 are not all possible semantic equivalences; the candidate
blocking strategy has false negatives and positives. Never claim
complete mathematical equivalence classification from this screen.

## Structural API overlap: two largest module pairs

**PredictionAE vs PredictionDependent:** eight repeated short names.
PredictionAE uses a common output space Y, while PredictionDependent
uses a dependent family Y i. The latter imports and reuses the former's
AEFactors/AESigmaLE relations. Legitimate stronger typing, not wholesale
duplicated source. Potential shared-definition factoring must preserve
a non-cyclic import graph.

**FiniteDiscountedControl vs CompactFellerControl:** fifteen repeated
short names, including Bellman, fixedPoint_unique and valueIteration.
But the first model has finite state-dependent action spaces; the
second uses compact metric state/action spaces, weakly continuous
Markov kernels, and continuous-map value functions. These are
not equal mathematical assumptions or interchangeable Lean models.
Abstract common contraction lemmas are appropriate; merging modules
or deleting one is not.

## Per-file inventories included in this snapshot

1. EVERY_FILE_633_DETAILED_METRICS.csv: one row for each of 633 Lean
   modules, source SHA, lines/imports/declarations, Core counted flags,
   matched public theorem proofs, incoming/outgoing theorem reuse,
   equal theorem type hits and risk annotations.
2. EVERY_DECLARATION_5553_COMPACT.csv: all 5,553 lexical declarations,
   file/line, symbol match confidence, reconciled fully-qualified
   Lean name, exact and binder-normalized type fingerprints.
3. ALL_binder_normalized_equal_type_clusters.json: the 37 strongest
   repeated-type clusters, 77 declaration names and file/line
   locations, statement renderings, and 26 internal direct proof edges.
4. NEAR_TYPE_15_DISTINCT_HEURISTIC_PAIRS.json: full candidate pairs,
   scores and source context, excluding equal-type repetitions.
5. BINDER_NORMALIZED_TYPE_PAIRS_40.tsv and VERIFY_40_TYPE_EQUIVALENCES.lean:
   re-run from formalization/ueot-core with lake env lean and the relative
   VERIFY script; requires all 40 Lean Meta.isDefEq checks to succeed.
6. all_3793_theorem_direct_reuse_graph.csv: each public authored
   source theorem and its direct referenced public source theorems.

### Method and confidence

Compiled with Lean 4.33.1 against the pinned Mathlib checkout; environment
constant types and .thmInfo.value.getUsedConstants were inspected in
Lean, not inferred from commentary. Python/FKRG then enumerated all
first-party source files. Exact source bytes and normalized line
content were fingerprinted; theorem types were grouped by exact
expression text and by an Expr constructor tree that removes ONLY
binder display names and metadata. The 15 approximate candidates
used restricted same-first-party-constant buckets, length and token
3-gram Jaccard scores. The latter is deliberately NOT exhaustive.

An equal elaborated type expression or direct proof dependency can
certify interface reuse, but it cannot by itself establish
minimal-generator independence, physical adequacy, or necessity
of UEOT's philosophical structure. All conclusions are from
source and compiled declarations at the pinned SHA; no theoretical
physics open port, proof count, or experimental evidence is promoted.

### Recommended governed follow-up, in order

1. **Fix FKRG namespace/section parser completeness** and resolve
   the one unmatched public declaration. Add adversarial tests for
   nested/noncomputable sections and non-UEOT third-party namespaces.
2. Store canonical predecessor/provenance/assumption signatures
   alongside future theorem entries. Require search + proof-reuse
   preflight before opening any new Lean theorem task.
3. In a new proof-safe branch, test the easiest replacement:
   StatisticalDefect.tvDist_symm via the InformationPacking lemma,
   preserving both public theorem names. Compile and prove no new axioms.
4. Audit the three OccupationLimitInvariance and four TransportCertificate
   same-type reproof routes, distinguish genuinely new bridge theorems
   from duplicated terminal derivations, then propose tiny refactors
   with exact-head CI and independent review. Frozen 106/106 theorem
   signatures, P-IDs, ledger and minimal generator claims cannot change
   without separate promotion authority.
5. Review the 15 near-type pairs manually, then broaden to deliberately
   distinct hypotheses via definitional and logical equivalence checks.
6. Keep this audit read-only/snapshot for now: numerical reuse signals
   are NOT proof that deleting modules is safe.

This is an exhaustive **module/source-declaration inventory and
public theorem proof-dependency census**, plus bounded mathematical
duplication candidates. A manually checked pairwise semantic equivalence
proof for every possible theorem pair remains future research.
