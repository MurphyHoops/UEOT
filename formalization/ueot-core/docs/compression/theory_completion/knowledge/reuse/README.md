# FKRG proof-level reuse navigator — additive research v1

This is an ADDITIVE, read-only extension of FKRG's existing lexical source
search. It does NOT modify fkrg.py, the Core 106 Lean theorem files, the
Compression counted ledger, frozen proof semantics, or open scientific ports.

The existing FKRG cache remains useful for broad keyword/module search.
This supplement adds real proof-term direct dependencies, verified same-type
theorem peers, source copies, and a read-only scientific-role distinction.

The current six-layer census is **650 modules = 639 UEOT-maintained + 11
adapted upstream**, with **3,992 registered public theorem nodes** and
**5,157 registered direct proof edges**. The layer-by-layer counts below
retain each historical scope.

## Governed overlay chain

The 2026-10-10 633-module audit remains immutable history.

### Layer 1 — relation/defect MINCORE

`MINCORE_REUSE_OVERLAY_V1.json` is the first immutable additive layer, pinned
to source checkpoint `fb70de6fb5dd26918222bc7b0849fb38900f8604`.
It records the 634th Lean module, the then-current import-only
`TheoryCompletion.lean` source-hash update, and 10 public theorem nodes. Its
certificate `VERIFY_MINCORE_OVERLAY_TYPES.lean` performs 37,930
cross-snapshot `Meta.isDefEq` checks plus 45 internal pair checks and finds
0 definitionally-equal matches. Its compiled proof terms contain 0 registered
base/overlay theorem edges.

That historical result remains unchanged. In particular, source text for
`rescale_changes_nonzero_defect` mentions `rescale_defect` in a tactic, but
the theorem constant is absent from the elaborated proof term; FKRG records
kernel proof dependencies, not tactic-token references.

### Layer 2 — calibrated defect comparison

`CALIBRATED_DEFECT_REUSE_OVERLAY_V1.json` composes on top of the 634-module
state instead of rewriting Layer 1. It is pinned to source checkpoint
`fb16512a6b4e813ef94f2ba3db0e6f3a44500886` and adds the 635th module,
`CalibratedDefectComparison.lean`, plus 8 public theorem nodes.

`VERIFY_CALIBRATED_DEFECT_OVERLAY_TYPES.lean` kernel-checks those 8 theorem
types against all 3,803 previously registered theorem nodes:
30,424 cross-layer `Meta.isDefEq` comparisons plus 28 internal comparisons,
with 0 matches. The same verifier checks exact compiled proof dependencies and
certifies exactly 3 registered theorem edges:

- `DefectCalibration.rel_iff` → `DefectCalibration.zero_defect_iff`;
- `DefectCalibration.tendsto_zero_iff` → `DefectCalibration.reverse_budget`;
- `calibrated_weighted_chain_bound` →
  `TransportCertificate.weighted_chain_bound`.

The last edge is the intended theorem reuse: the calibrated bridge transports
an already-proved M-TC finite-horizon certificate rather than reproving the
weighted recurrence.

### Layer 3 — defect gauge covariance

`DEFECT_GAUGE_REUSE_OVERLAY_V1.json` composes on the intact 635-module state,
pinned to source checkpoint `3fb6c422638a6c8dbb2ea31cf9affd4e2f17b668`.
It adds `DefectGaugeCovariance.lean` and 6 public theorem nodes.

`VERIFY_DEFECT_GAUGE_OVERLAY_TYPES.lean` compares those 6 types with all
3,811 prior registered theorem nodes: 22,866 cross-layer `Meta.isDefEq`
comparisons plus 15 internal comparisons, with 0 matches. The same native
certificate checks exactly 6 registered direct proof edges:

- `DefectCalibration.triangle_quasi` and
  `calibrated_cross_stage_contraction` each use
  `DefectCalibration.reverse_budget`;
- `rescaled_weighted_chain_bound` uses
  `TransportCertificate.weighted_chain_bound` and the three new scalar-gauge
  helpers `rescale_triangle_preserved`, `rescale_contraction_transformed`, and
  `rescale_local_budget_transformed`;
- the three scalar-gauge helpers have no registered direct theorem edges.

The immutable-base PR preflight finds six new theorem names, with prior
lexical reuse candidates for one of them: `rescaled_weighted_chain_bound`.
Its three hints are the registered weighted-chain bound, the earlier calibrated
bound, and `TransportCertificate.chain_bound`. These remain name-similarity
hints; the compiled dependency certificate above establishes the actual reuse.
The PR parser's lexical corpus counts (3,812 to 3,818) and the registered
proof graph counts (3,811 to 3,817) are distinct scopes.

That third layer's historical census is **636 modules = 625 UEOT-maintained +
11 adapted upstream**, with **3,817** registered public source theorem nodes.

### Layer 4 — calibrated finite-horizon risk of actual projected paths

`FINITE_HORIZON_RISK_REUSE_OVERLAY_V1.json` retains the intact 636-module
base and adds five physical UnifiedClosure modules:
`FiniteHorizonPathAdapter`, `FinitePMFProjection`, `CalibratedRiskRows`,
`AbsorbingLeakage` and `FiniteHorizonRisk`. The source checkpoint is explicitly
identified by the frozen full-source content hash; it is not represented as a
Git commit that already contained uncommitted source.

The native export confirms **48 public source candidates**, their actual
compiler source-module ownership and compiled proof terms. It compares their
raw stored types with 3,817 prior registered nodes: **183,216 cross-layer** and
**1,128 internal** `Meta.isDefEq` comparisons, with **0 matches**. Each pair
uses a fresh `liftTermElabM` state. This inherits the historical raw-type
protocol; universe parameter names are retained, and zero matches does not
establish general logical inequivalence or rule out instantiated reuse.

The fixed `VERIFY_FINITE_HORIZON_RISK_OVERLAY_TYPES.lean` certificate rejects
any change to the observed **73 registered direct proof edges**: 20 target
previously registered theorems and 53 target another new public theorem.
The actual composition includes:

- `pmf_tv_le_clipped_coordinate_budget` → the existing
  `FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs` and
  `TotalVariation.tvDist_le_one`;
- `finite_horizon_path_error` → the existing
  `PathError.p_dyn_03_finite_path_error`;
- `same_policy_coordinate_path_error` → the actual projected-path endpoint
  and the normalized-PMF coordinate budget;
- `calibrated_representative_path_error` → that same actual path endpoint
  and `calibrated_observable_partition_tv_budget`;
- `calibrated_representative_failure_risk` → the calibrated path endpoint
  and the measurable-event transfer theorem.

The supporting `FINITE_HORIZON_RISK_NATIVE_V1.json` preserves actual type
displays, universe parameters, all direct proof constants for the 48 public
source nodes, and an independent axiom census of **75 theorem constants**
owned by the five compiled modules. That native census comprises 48 confirmed
public source candidates, **8 private constants** and **19 other nonprivate
constants** outside the lexical source candidate list. Those 19 are not
silently counted as authored source declarations. All 75 are checked through
`Lean.collectAxioms`; the allowlist is `propext`, `Classical.choice`, `Quot.sound`.
The type display is `ppExpr` output, not a lossless Lean expression encoding.

The existing PR-preflight parser, applied to the immutable base and the frozen
worktree sources, finds 48 new public names and lexical hints for 15 of them.
Its corpus grows from 3,818 to 3,866; the registered proof graph grows from
3,817 to 3,865. These are different scopes. The committed PR gate still runs
against actual Git objects after commit.

The fourth layer records **641 modules = 630 UEOT-maintained + 11 adapted
upstream**, with **3,865** registered public source theorem nodes and **4,968**
direct registered edges. All four overlay JSON files, certificates and the
new supporting native export are hash-bound. Overlay areas are derived from
physical source paths, so the new UnifiedClosure nodes are not mislabelled
as MinCore. No counted Core/Compression tier or scientific open port is
promoted. The [44-file reading guide](../CANONICAL_READING_GUIDE_V1.md)
explains the calibrated representative model and the finite-horizon boundary.

### Layer 5 — finite-sample calibration and empirical reference risk

The pinned Lean 4.33.1 focused build, full `UEOT` build, native export and
independently executed fixed certificate all passed against the exact source
hashes in this layer. Its checkpoint is frozen source content
`0f8ab9e7ccbf15f7f42305ec8018841bfd7dd92691f412aab283f9eee4067ea3`,
not a Git commit claimed to contain then-uncommitted files. These local
results do not assert that subsequent canonical integration or CI has passed.

`STATISTICAL_RISK_REUSE_OVERLAY_V1.json` preserves the immutable 641-module,
3,865-public-theorem state and appends five physical UnifiedClosure modules:
`StatisticalRiskCalibration`, `MicroscopicFailureRisk`, `EmpiricalReferenceRisk`,
`StatisticalRiskBoundary` and `StatisticalRiskWitness`. It has **73 confirmed
public source candidates**, **282,145 comparisons** with the 3,865 prior
registered raw stored types and **2,628 internal comparisons**, with **0
matches**. Each comparison uses a fresh `liftTermElabM` state. Universe
parameter names retain their stored form; this protocol does not decide
general logical equivalence or all possible instantiated reuse.

`VERIFY_STATISTICAL_RISK_OVERLAY_TYPES.lean` independently checks the exact
**91 observed registered direct proof edges**. Its emitted native JSON
matches the initial native export in every field. The two independently
registered digests are different artifacts; the native JSON is separately
hash-bound by the overlay:

| Artifact | SHA-256 |
| --- | --- |
| `STATISTICAL_RISK_REUSE_OVERLAY_V1.json` | `f0d0ea91584773c24eeed59f8f1915102b92c318bf864f3b08a4c7093552c755` |
| `VERIFY_STATISTICAL_RISK_OVERLAY_TYPES.lean` | `5615a23f94b3ba53f9faec51b72d021f204e539fc73448f793752cc78727438d` |
| `STATISTICAL_RISK_NATIVE_V1.json` | `9a87e5f99d48cfc7fa95df595d7884837f0dd24253205858f5c27ae22545a63d` |

Examples of actual registered proof dependencies are:

- `measure_finite_row_calibration_bad_le` uses
  `BoundedLossTwoSided.measure_exists_candidate_bad_le`;
- `statistical_representative_risk_certificate` uses
  `empirical_representative_risk_of_calibrated`,
  `measurableSet_empirical_transition_calibrated` and
  `measure_empirical_transition_uncalibrated_le`;
- `statistical_empirical_reference_certificate` uses
  `empirical_reference_risk_of_calibrated` and those same two calibration
  event/probability lemmas;
- `same_policy_microscopic_failure_risk` uses
  `risk_microscopic_event_le_envelope` and `same_policy_projected_failure_risk`.

These are compiled direct constant dependencies, not import edges or tactic
token matches.

`STATISTICAL_RISK_NATIVE_V1.json` independently enumerates **126 compiler-owned
theorem constants**: 73 confirmed public source candidates, **11 private
constants** and **42 other nonprivate constants** outside the confirmed source
candidate list. The 42 include generated and other non-lexical theorem names;
they are not automatically classified as handwritten source declarations.
Every one of the 126 records retains `name`, physical `source_module`,
`is_private`, stored `level_parameters`, the full `ppExpr` `type` display,
all proof-body `direct_constants`, `direct_theorem_constants` and transitive
`axioms`. The native theorem-constant lists are not restricted to lexical
public candidates. Every theorem in this physical module scope passed
`Lean.collectAxioms` with only `propext`, `Classical.choice` and `Quot.sound`.

The 73 public records additionally carry `source_theorem_deps`, restricted
to registered public source theorem targets. Consequently private helper
references and their own proof dependencies remain in the 126-record native
evidence without being counted among the 91 public graph edges. The public
graph is a navigational subset of the compiled scope, not the authority for
deciding which native theorems exist. The existing raw-stored-type and
non-lossless `ppExpr` limitations remain.

The scientific additions relate a fixed finite row-sampling experiment to
one measurable simultaneous calibration event and actual finite path risk.
Each row has IID samples with exactly its true source PMF law; distinct rows
may be dependent in the generic theorem. The model, tests, sample size,
horizon and concentration radii are fixed before the samples. On the one
good event, all subsequently selected representations, coefficients and
common observable-history policies satisfying the deterministic checks are
covered without an additional union over those choices. This does not allow
unrestricted data-selected tests, radii or online stopping.

For `m` coarse classes, indicator approximation error `delta`, empirical
same-fibre error `eta`, sampling radius `rho` and coefficient L1 bound `kappa`,
the sparse-test route uses true representative rows and the per-step budget
`min 1 ((m / 2) * (2 * delta + (eta + 2 * rho) * kappa))`.
The full finite-event route constructs empirical reference PMFs and uses
`min 1 (rho + eta)` from true-to-empirical TV and a checked empirical coarse
fit. Its prototype need not be a section. The fixed full event library has
`2^|X|` tests; its statistical cost is retained. Both routes preserve the same
policy and projected initial law when comparing actual and reference paths.

Microscopic failure risk requires an explicit failure label and a
conservative coarse envelope. `StatisticalRiskBoundary` gives a genuine
finite-PMF example where optimistic action selection increases calibration
failure from `1/4` for each fixed action to `7/16`, demonstrating why the
simultaneous event matters. `StatisticalRiskWitness` constructs the product
row-sampling law and a four-state, non-stable coarse partition. With two
steps and 4,096 samples per row, one good training event has probability at
least `3/4`; on it the actual microscopic ever-failure risk is at most
`143/256 < 1`, using the explicitly computed reference risk `31/256` and
path budget `7/16`. This layer supplies a common constructive witness; Layer 6
below constructs the associated finite training-and-deployment joint law.
That construction requires the stated conditional deployment law; physical access
to the row experiments and validation of failure labels remain separate
empirical obligations. Finite path error bounds do not establish all-time
safety. These additions remain uncounted; global scientific closure remains
`NOT_ESTABLISHED`.

The existing PR parser, applied to the immutable base and final frozen source
bytes, finds 73 new public names and lexical hints for **11** of them.
The cumulative overlay hint count is **27**. Its lexical theorem corpus
grows from **3,866 to 3,939**; the registered native public graph grows from
**3,865 to 3,938**. Hints remain lexical candidates. The immutable Git-object
PR preflight is separately required after commit.

The historical five-layer source census is **646 = 635 UEOT-maintained + 11 adapted
upstream**, with **3,938** registered public source theorem nodes and
**5,059** registered direct edges. The overlays account for **145** of those
public nodes and **173** of those edges.
The philosophy feedback and continuous Core rewrite document the precise
theorem/conditional/empirical boundaries without promoting the counted ledger.

### Layer 6 — registered deployment coverage and training/deployment joint risk

`DEPLOYMENT_JOINT_REUSE_OVERLAY_V1.json` preserves the intact 646-module,
3,938-registered-theorem base and adds four physical UnifiedClosure modules:
`DeploymentCoverage`, `DeploymentCoverageWitness`, `TrainingDeploymentJoint`
and `CalibratedDeploymentJoint`. The frozen Lean source fingerprint is
`9489908b8ce8a335f7eafa57405d938ecc8bbdd343e611656fb1cb7da5384275`.
The focused four-module build, full `UEOT` build, native exporter and
independently executed fixed verifier all passed against those exact source
bytes with Lean 4.33.1. These are local source-bound results; they do not
assert that a later Git commit or remote CI run has passed.

The native evidence confirms **54 public source candidates**, compares them
with **3,938 prior registered types** in **212,652 cross-layer** and **1,431
internal** raw-stored-type comparisons, and finds **0 matches**. Each
comparison uses a fresh `liftTermElabM` state; stored universe parameter names
are retained. This protocol does not establish general logical inequivalence
or rule out reuse after instantiation. Source and compiled-type review of the
13 new declarations with 26 lexical hints separately examines their actual
hypotheses, outputs and existing proof routes.

The fixed certificate independently checks **98 registered direct proof
edges**. Its emitted full JSON matches the initial native export in every
field. The overlay and fixed verifier have independent registered hashes;
the native JSON is separately hash-bound inside the overlay:

| Artifact | SHA-256 |
| --- | --- |
| `DEPLOYMENT_JOINT_REUSE_OVERLAY_V1.json` | `72fd346f3ab3adca4cb29de1f5c19cc6742555e3003fc32efa345eabbda850f2` |
| `VERIFY_DEPLOYMENT_JOINT_OVERLAY_TYPES.lean` | `48e310eb767413092a0e02fff53bc00b22c87808b4abc838be1ec2279c35b873` |
| `DEPLOYMENT_JOINT_NATIVE_V1.json` | `04058c199ae439fbafb0a659ed78228b3c5e5ab2a4e2444efa6e60d1df588725` |

`DEPLOYMENT_JOINT_NATIVE_V1.json` independently records **93 compiler-owned
theorem constants: 54 confirmed public source candidates, 12 private
constants and 27 other nonprivate constants**. Every native record retains
`name`, physical `source_module`, `is_private`, stored `level_parameters`,
the full `ppExpr` `type` display, all `direct_constants`,
`direct_theorem_constants` and transitive `axioms`. All 93 satisfy the same
standard-axiom allowlist. The 27 other nonprivate constants are not silently
classified as authored source declarations. The 98 public graph edges omit
private helpers and unregistered targets, which remain visible in the full
native records; a public node with zero registered edges can still use them.

The actual registered proof routes include:

- `coverage_registered_row_calibration` → the existing
  `measure_finite_row_calibration_bad_le` →
  `BoundedLossTwoSided.measure_exists_candidate_bad_le`;
- `coverage_projected_causalLaw_error` →
  `coverage_tv_extend_same_kernel` → the existing
  `PathError.pmfCommonMass_extend_lower_bound`;
- `coverage_same_policy_microscopic_failure_risk` → the new actual-occupancy
  path bound and the existing `risk_event_transfer` and
  `risk_microscopic_event_le_envelope`;
- `statistical_selected_empirical_deployment_risk` → the existing
  `statistical_empirical_reference_certificate` and the new joint risk bound;
- `coverage_statistical_selected_joint_failure_risk` → registered source
  calibration, empirical microscopic failure risk and the constructed joint
  risk bound;
- `statistical_fixed_policy_training_deployment_witness` → the existing
  `StatisticalRiskWitness.good_sample_exists` and
  `microscopic_two_step_risk_on_good`, then the joint risk bound.

These routes use actual proof constants. Their typed contracts also preserve
the fixed source `P`, the specified sampling experiment and one common
microscopic failure event. The actual state/action occupancy `nu_n` is
constructed from the actual finite prefix law and the same observable-history
policy. With certified rows `C` and row budget `epsilon_n`, the path budget is
`sum_n<T (epsilon_n + (1 - epsilon_n) * nu_n(C.compl))`. Registered rows and
sampling tests are fixed before training. Calibration of their response
distributions does not estimate the deployment mass of unregistered rows.
The reference risk and occupancy terms remain checked model inputs.

The joint law is constructed as `pmfExtend training (deployment ∘ select)`
on training outcomes and deployed paths. The finite tower identity is proved
from that construction. For conditional good-event risk at most `beta` in
`[0,1]` and bad-training mass at most `alpha`, its risk is at most
`min 1 (alpha + (1 - alpha) * beta)`. The data-dependent theorem retains
the actual bad-training mass plus the training-probability-weighted budget
on the good event. The statistical adapters use `Measure.toPMF_toMeasure`
to preserve the same training measure. Training and finite path spaces are
finite here; the candidate index family need not be finite. Choices may
depend on training, but feasibility of their checks is an explicit premise.

The constructive coverage witness has actual two-step failure probability
`583/1024` and invokes the generic coverage bound `11/16`. Its boundary
example has zero empirical loss with probability `7/8` while an uncovered
deployment fails with probability one. A separate nonconstant selection
witness gives positive training mass to two different deployment PMFs and
attains the sharp mixture value `5/8`, with `alpha = 1/4`, `beta = 1/2`.
For the earlier fixed-policy statistical witness, the deployment law does
not vary with training: existence of a good sample gives the stronger joint
bound `143/256`, without an additional bad-training penalty. The wrong-law
counterexample makes the conditional-law premise necessary. The construction
does not identify an arbitrary external conditional law from fixed-candidate
marginals, prove access to the row experiments or establish all-time safety.

The lexical preflight finds **54 new public names** and **13 groups of hints**;
the cumulative overlay group count is **40**. Its corpus grows from **3,939
to 3,993**, while the registered graph grows from **3,938 to 3,992**. The
historical one-name difference remains: the lexical parser also sees
`UEOT.V3.FreeInformationValue.integrable_finset_sup'`, outside the frozen
registered base. This layer does not rewrite that historical registry. The
immutable Git-object PR preflight remains a separate post-commit gate.

The six-layer source census is **650 = 639 UEOT-maintained + 11 adapted
upstream**, with **3,992** registered public source theorem nodes and
**5,157** registered direct edges. The overlays account for **199** nodes
and **271** edges. No counted Core/Compression tier is promoted, and global
scientific closure remains `NOT_ESTABLISHED`.

## Run from repository root

    P=formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse
    python3 "$P/fkrg_reuse.py" status
    python3 "$P/fkrg_reuse.py" search "tvDist_symm"
    python3 "$P/fkrg_reuse.py" show UEOT.V3.StatisticalDefect.tvDist_symm
    python3 "$P/fkrg_reuse.py" show UEOT.V3.Compression.TransportCertificate.processInterface_approx_via_twoStage
    python3 "$P/fkrg_reuse.py" clones --min-lines 20
    python3 "$P/fkrg_reuse.py" --json status
    python3 "$P/test_fkrg_reuse.py"
    python3 "$P/REBUILD_CLONE_CANDIDATES.py"
    python3 "$P/VERIFY_PMF_TV_BRIDGE.py"

Run the new native certificate from `formalization/ueot-core` after building
the public imports with the pinned toolchain:

    lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_DEPLOYMENT_JOINT_OVERLAY_TYPES.lean

## Strongly typed and provenance-limited evidence

- 633 immutable-base source modules = 622 UEOT-maintained + 11 adapted upstream modules;
  six governed overlays extend the live census to 650 = 639 + 11.
- 3,793 immutable-base public source theorem proofs + 199 governed overlay theorem
  proofs = 3,992 live graph nodes, with 5,157 direct registered-source theorem
  references. The historical four overlays add 0, 3, 6 and 73 certified direct edges;
  the fifth adds 91 and the sixth adds 98 certified direct edges.
- 37 equal-type groups / 77 names. The original audit checked 40/40
  representative-to-peer theorem type pairs via Lean Meta.isDefEq. Here
  the CLI identifies these as PINNED SNAPSHOT checks, not a fresh proof run.
- The canonical Compression ledger fixes the role of 14 independently
  reconstructed same-type cases: 8 counted M-TC/M-OI family results
  (including an intermediate support lemma), 4 uncounted retained
  P-ALI/P-CTL experimental adapters, 1 repeated TV symmetry helper,
  and 1 interface alias for an existing physical-seed no-go.
- The other 15 near-type candidate pairs were ALL rejected as closed
  definitional type equalities in the initial compilation, 0/15 PASS.
  Their inference direction or implicit assumptions may still relate.
- 68 cross-file source-code spans with at least 8 normalized nonblank
  lines (61 wholly nonvendored and 7 involving adapted upstream code);
  12 spans reach 15 lines. This is a text-copy candidate index, NOT
  a proof-equivalence decision procedure. The historical 646-module recomputation
  preserved all 68 historical rows exactly, with no added or missing rows.
  The current scanner recomputes all 650 modules and rejects any difference
  from that immutable result; its actual command result establishes whether
  the current-source scan passes. The historical snapshot alone does not.

## New exact Lean bridge despite non-identical closed types

Two P-GOA-related files, FiniteRecurrentDecompositionStability and
SymmetricKilledSpectralStability, locally implement the same PMF
total-variation half-L1 calculation over 31 identical consecutive
nonblank proof lines. Comparing their raw closed elaborated theorem types
using Meta.isDefEq gives FALSE, reflecting the theorem contexts and
implicit type arguments.

Nevertheless, a temporary whole-module compilation of the latter after
importing the former and replacing the second PMF TV proof with a direct
exact invocation of the first PASSES with Lean. The script
VERIFY_PMF_TV_BRIDGE.py reproduces this while validating two hardcoded
historical source SHA-256 hashes BEFORE any compilation and never editing
real Core Lean files.

This is evidence of a technically viable future refactor, NOT authorization
to mutate the frozen source. Core's L3 governance and its semantic
review requirements must be satisfied separately.

## Fail-closed freshness and source authority

The navigator validates fixed, independent SHA-256 values for EVERY
source audit input file, its own 68-row clone snapshot, the immutable
canonical Compression ledger used for scientific-role classifications,
the pinned Lean compiler/dependency environment (lean-toolchain,
lakefile.lean and lake-manifest.json including the pinned Mathlib revision),
the exact set of live Lean source paths (including detecting ANY newly added
or deleted module), and all immutable-base source hashes plus the governed
overlay-chain hashes against the exact 650-module live source census. It refuses to
answer if any source or metadata changed. A docs-only Git commit does
not spuriously make a valid source snapshot stale.

For a real subsequent Lean source change, regenerate source+elaboration
evidence and independently review new pinned digests. Do not silently
overwrite the old audit or treat the existing cached evidence as current.

The direct proof graph only includes registered PUBLIC source theorem
targets; a declaration with zero registered outgoing dependencies may
still reuse Mathlib, source definitions, private/local helpers or
compiler-generated theorem constants.

## Required future anti-repetition preflight

1. Search original FKRG lexical index (fkrg.py find/show).
2. Search this proof reuse navigator for prior theorem statements and
   inspect direct dependencies and same-type peers.
3. Open source and compare actual Lean hypotheses, including instances,
   universe types and domain mappings. Test exact/apply in temporary
   compilation before inventing a new proof or deleting an existing one.
4. If a repeated theorem is a counted family generator witness,
   preserve its actual abstract-to-Core derivation, rather than making
   the terminal statement an immediate alias and calling it compression.
5. Follow the canonical Compression ledger for uncounted adapters and
   counted mappings. Green type-checking never promotes scientific claims.

KNOWN LIMITATIONS: no general logical equivalence algorithm; no
identifier-renaming-invariant clone detection; some copy spans include
theorem statement headers; code matching can miss renamed or rewritten
proofs; pinned type results are not dynamically recomputed; no claim
that UEOT physical validity or generator minimality follows.
