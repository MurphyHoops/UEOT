# FKRG proof-level reuse navigator — additive research v1

This is an ADDITIVE, read-only extension of FKRG's existing lexical source
search. It does NOT modify fkrg.py, the Core 106 Lean theorem files, the
Compression counted ledger, frozen proof semantics, or open scientific ports.

The existing FKRG cache remains useful for broad keyword/module search.
This supplement adds real proof-term direct dependencies, verified same-type
theorem peers, source copies, and a read-only scientific-role distinction.

The current ten-layer census is **684 modules = 673 UEOT-maintained + 11
adapted upstream**, with **4,272 registered public theorem nodes** and
**5,614 registered direct proof edges**. The layer-by-layer counts below
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

The historical six-layer source census is **650 = 639 UEOT-maintained + 11 adapted
upstream**, with **3,992** registered public source theorem nodes and
**5,157** registered direct edges. The overlays account for **199** nodes
and **271** edges. No counted Core/Compression tier is promoted, and global
scientific closure remains `NOT_ESTABLISHED`.

### Layer 7 — finite support viability and registered Good-event joint risk

This layer adds nine modules on the unchanged source baseline
`7b1f7c3cf2e86cb85dcdb1b4618c247c517407f8`. It records frozen worktree
content, not a fabricated future Git object: `source_checkpoint_kind` is
`FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT` and the lexical `candidate_ref`
is null. The source-tree digest is
`91621694fadc223f63b76298a6eaf10078e59bd87c9dbc798726a6e366b1f357`.
The V3 manifest binds all nine module files and the public root import:
`993bd1a5c32b9872212282fba38411caf683c088f374b4d3c178fd79cc8c923e`.
A later immutable Git-object PR preflight and remote CI remain separate gates.

The actual pinned-toolchain build returned 0 for the nine modules
(8,774 jobs, 29.190 seconds) and for `lake build UEOT` (9,365 jobs,
13.423 seconds). The original root-import placement failure and the first
native collision failure were retained; neither is presented as a passed run.
The two later independent native executions returned 0 and produced identical
complete JSON objects, including private/generated constants, types, owners,
axioms and ordered proof-constant arrays. The fixed verifier is generated from observed evidence; the pipeline then
compares its complete actual export with the first independent export.

| Artifact | SHA-256 |
|---|---|
| [SUPPORT_VIABILITY_NATIVE_V1.json](SUPPORT_VIABILITY_NATIVE_V1.json) | `34376e2c8564d148e5dcd4452ab0dddeb9aa20bbb1b9d0f7c88c194b9b82baca` |
| [SUPPORT_VIABILITY_REUSE_OVERLAY_V1.json](SUPPORT_VIABILITY_REUSE_OVERLAY_V1.json) | `2af284000d6a6c25f67e9356a236817b22334dbfba777ca2eaf37e8060a3a45e` |
| [VERIFY_SUPPORT_VIABILITY_OVERLAY_TYPES.lean](VERIFY_SUPPORT_VIABILITY_OVERLAY_TYPES.lean) | `26fd18e77dd6b7db550c6c5e1105376ef7f494db03bbab646e8d8fa42313a118` |

The complete compiler scope is **219 theorem constants = 102 public source
candidates + 22 private constants + 95 other nonprivate constants**. Every
native record retains `name`, `source_module`, `is_private`, stored
`level_parameters`, the displayed type, all `direct_constants`, direct theorem
constants and the transitive axiom list. All 219 axiom lists are subsets of
`propext`, `Classical.choice`, `Quot.sound`. The 102 public candidates are
independently matched to those records; their registered graph adds **163
direct edges**. Owners are physical compiled modules, not names inferred
from the logical namespace. A type display remains a display, not a lossless
serialization of a Lean expression.

| Physical module | Public source candidates | All native theorem constants |
|---|---:|---:|
| `ControlCoverageWitness` | 37 | 85 |
| `FiniteSupportViability` | 15 | 30 |
| `FiniteSupportViabilityCheck` | 5 | 25 |
| `ObservableActionCoverage` | 9 | 14 |
| `PosteriorSupportCoverage` | 3 | 4 |
| `ReachablePolicyExtension` | 4 | 4 |
| `RegisteredDeploymentRisk` | 2 | 5 |
| `RegisteredDeploymentRiskWitness` | 26 | 51 |
| `ViableRegisteredJoint` | 1 | 1 |

The historical seven-overlay state adds **301 public nodes and 434 registered edges** to
the immutable base, giving **4,094 nodes and 5,320 edges**. The lexical
corpus has **4,095 candidates**, preserving the historical one-name offset
rather than rewriting the base registry. The new 17 name-hint groups bring
the cumulative overlay count to 57. No Core/Compression counted tier is
promoted; the frozen 4/11/89 classification and `NOT_ESTABLISHED` scientific
status remain unchanged.

#### Actual-law support and finite policy existence

`ObservableActionCoverage` reuses the canonical deployment row law to derive
an occupancy cap from observable action restrictions whose permitted actions
are certified on the entire observation fiber. Its finite mask is executable
when the observation equality and certification predicates have
executable decision procedures. Nonempty fibers alone do not guarantee a
common certified action. A total fallback policy handles the full-time API;
classical policy selection under nonempty masks is not itself an algorithm.

`PosteriorSupportCoverage` relaxes whole-fiber certification only to the
support of the **actual** terminal posterior under a fixed actual policy.
Null observation histories need no probabilistic constraint. This fixed-policy
validation is not reused as though its posterior were unchanged after selecting
a different policy. `ReachablePolicyExtension` first reuses the existing generic
prefix-law congruence: the law at time `n` needs equality only before `n`,
whereas the state/action row law also needs equality at the current time `n`.
Its older strong Extend condition remains a sufficient nonblocking condition;
it is not a premise of the new viability equivalence.

`FiniteSupportViability` derives the trace-support update from the same
microscopic source and recorded action/observation history. It proves the
posterior-support correspondence and the zero-uncertified-mass equivalence;
support correctness is not supplied as an unproved law-matching field. A
finite remaining-horizon recursion chooses one action certified for all
indistinguishable states and requires every nonempty **merged observation
successor** to remain viable. Viability of every positive initial observation fiber
is equivalent to the existence of a complete history policy whose
actual uncertified-row occupancy is zero at every transition before the
horizon. The theorem retains a supplied complete fallback policy, including
the zero-horizon boundary.

`FiniteSupportViabilityCheck` proves its finite Boolean checker equivalent to
that recursion. The executable version reads a finite support relation and
requires a proved exact correspondence to the actual PMF support. The concrete
source proves this correspondence; it is not a substitution of an unverified
transition relation. The same-source witness has a complete successful policy
and another locally certified prefix that reaches a genuine dead end. Thus
existence of a complete policy is weaker than extendibility of every already
certified prefix. Support suffices for this zero-occupancy question; it does
not determine arbitrary nonzero probability bounds or costs, and a finite
horizon does not imply all-time safety.

#### One calibration event and the same selected deployment

`RegisteredDeploymentRisk` uses fixed registered rows and the original
finite-row calibration bound. Source-row laws and row-wise IID samples are
required only on that registered subtype. The empirical-fit, actual occupancy
cap and checked numerical budget obligations are required **on the same
measurable Good event**, after the data-dependent selection. There is no second
confidence penalty for consuming the same event twice. The actual constructed
training/selection/deployment PMF uses the same microscopic source, selected
initial law, observation map and history policy as the conditional risk bound.
The theorem invokes the original joint-risk and coverage endpoints.

`ViableRegisteredJoint` directly invokes `viablePolicy_zero_uncovered` for its
own synthesized policy. It removes the separate occupancy-cap premise on Good;
it retains initial-fiber viability, registered calibration, empirical fit,
the conservative microscopic-to-coarse failure envelope, and the numerical
Good-event budget check. Neither initial viability nor an empirical estimate
of the true source is manufactured by this adapter.

The actual registered product experiment in `RegisteredDeploymentRiskWitness`
has two registered rows and 256 samples per row. Its selector genuinely depends
on an observed training bit; the two action probabilities are `7/8` and `1/8`,
with actual deployment failure probabilities `1/8` and `1/4`. The canonical
joint tower yields exact risk **`9/64`**. The common calibration and checked
risk theorem yields the nontrivial, conservative bound **`17/32`**. A
positive-probability all-true training record has checked budget 1, proving
that the corresponding all-record budget at most `1/2` is false; the valid
obligation is on Good. This is a mathematical sampling/deployment experiment,
not external empirical validation or a proof of optimal learning. The concrete
witness directly checks its own zero occupancy; it is not presented as an
application of an unimplemented general learning algorithm.

Zero uncertified-row occupancy removes the coverage penalty. It does not
remove reference failure or row-calibration error and does not imply zero
physical failure. Identifying the external transition law and observation
map, gaining access to the registered row experiments, and validating the
microscopic failure label/envelope remain independent obligations.

#### Genuine collisions retained behind a smaller public API

The first native attempt found nine real closed-type coincidences. The three
local concrete-computation lemmas `SafePrefixDeadend.initial_checker_pass`,
`SafePrefixDeadend.good_successor_checker_pass`, and
`RegisteredSelectionWitness.allTrue_selects_true` each matched both old facts
`flip_next_state_is_true` and `survival_micro_alias`, and matched one another.
Only those three local helpers were made private. Their mathematical
propositions and proof bodies were unchanged. The full native export still
contains each private theorem with the same displayed type, stored universes,
axioms, direct constants and direct theorem constants as before.

The initial checker fact remains a direct dependency of
`SafePrefixDeadend.a_complete_zero_uncovered_policy_exists`; the all-true
selection fact remains a direct dependency of `allTrue_checkedBudget`; the
good-successor computation has no named consumer. The new native regression
requires these records and these actual consumers. The full native scope did
not shrink from 219. Public terminal conclusions and the executable checker
remain available.

The unchanged public-candidate protocol compares 102 new raw stored types
against 3,992 prior registered types (**407,184** comparisons), and all pairs
within the new set (**5,151** comparisons). Each runs in a fresh elaborator
comparison with its recorded stored universe names. It reports zero public
matches. This does not claim that private coincidences disappeared, that the
new results are logically independent, or that old generic theorems cannot
be instantiated to prove them.

#### Typed review of all 17 name-hint groups

Every group below was compared against its actual old/new source contracts
and the new compiled type and proof constants. Names without a full prefix
are under `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure`. Name similarity
and a zero raw stored-type match were not accepted as semantic review by
themselves. All groups are CLEAR; direct reuse was retained wherever applicable.

1. **`ObservableActionCoverageCheck.MissingFiber.representative_is_certified`**. Prior candidates: `StatisticalRiskWitness.representative_section`, `statistical_representative_risk_certificate`. A certified Bool representative sharing the same Unit observation with an uncertified actual state is not a quotient section identity, nor a simultaneous statistical calibration event. Neither hinted theorem gives whole-fiber certification.

2. **`PosteriorSupportStrictWitness.initial_apply`**. Prior candidates: `UEOT.V3.FiniteRecurrentDecompositionStability.initialClassWeights_apply`. This computes the phase/side initial PMF. The old initialClassWeights_apply relates recurrent-class weights to an absorption potential for a recurrent decomposition; input spaces and output objects differ.

3. **`PosteriorSupportStrictWitness.actualPrefix_apply`**. Prior candidates: `UEOT.V3.HilbertMeanPrefixFiltration.prefixFiltration_apply`. This computes actual one-step history mass, directly using pmfExtend_apply. The hinted prefixFiltration_apply is a definitional equality of sigma-fields, not a PMF product identity.

4. **`PosteriorSupportStrictWitness.actual_prefix_masses`**. Prior candidates: `DeploymentCoverageWitness.actualRow_mass`, `StatisticalRiskWitness.actualRow_mass`. The new pair of masses concerns two complete histories of the four-state posterior example. The hinted row masses concern single transitions of different models. Existing local actualPrefix_apply and initial_apply are reused.

5. **`PosteriorSupportStrictWitness.actual_uncovered_probability_zero`**. Prior candidates: `DeploymentCoverageWitness.uncovered_probability`, `DeploymentCoverageWitness.restricted_uncovered_probability`. The old witnesses concern a state-independent action mixture and uncovered probability 1/4. This history-sensitive posterior example proves zero actual bad occupancy by the existing posterior coverage endpoint and indicator helper; it cannot use the older model-specific formulas.

6. **`SupportViabilityClosure.SafePrefixDeadend.mem_source_support_iff`**. Prior candidates: `UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC.audited_source_mem_iff`. The new iff identifies deterministic PMF support with a transition value. audited_source_mem_iff instead describes a registered/authenticated intervention-response candidate filter. These predicates and source objects differ.

7. **`PolicyPrefixCongruenceCheck.actual_causalLaw_congr_before`**. Prior candidates: `causalLaw_congr_before`. The old generic causalLaw_congr_before is an actual direct proof dependency. The new interface specializes it to the same q/P and two policies agreeing strictly before n. No parallel causal-law induction is introduced.

8. **`RegisteredSelectionWitness.actualRow_mass`**. Prior candidates: `DeploymentCoverageWitness.actualRow_mass`, `StatisticalRiskWitness.actualRow_mass`, `DeploymentCoverageWitness.actual_row_error`. The old same-named row formulas belong to different uncovered-action/hidden-state models; actual_row_error is a TV distance, not a mass coordinate. The new 1/8-versus-1/4 row directly reuses the general AbsorbingLeakage.kernel_mass.

9. **`RegisteredSelectionWitness.samples_measurable`**. Prior candidates: `StatisticalRiskWitness.sourceSample_measurable`. The new measurable sample is indexed only by the fixed registered-row subtype. It directly reuses productRowSample_measurable instead of the older all-row sourceSample wrapper, and does not invent samples for missing rows.

10. **`RegisteredSelectionWitness.samples_independent`**. Prior candidates: `StatisticalRiskWitness.sourceSample_independent`, `UEOT.V3.AlignmentGlobalExactness.pathIndependent`. Row-wise IID directly reuses productRowSample_independent on the registered product experiment. sourceSample_independent wraps all rows; AlignmentGlobalExactness.pathIndependent concerns integrals of a one-form under closed periods, unrelated to probabilistic independence.

11. **`RegisteredSelectionWitness.actual_failure`**. Prior candidates: `StatisticalRiskBoundary.actualFailure_eq`. The new theorem evaluates an actual one-step causal failure event with action-dependent probability 1/8 or 1/4. StatisticalRiskBoundary.actualFailure_eq evaluates a different fixed 3/4 row. The proof uses its actual one-step private helper and actualRow_mass.

12. **`RegisteredSelectionWitness.empirical_fit`**. Prior candidates: `DeploymentCoverageWitness.empirical_loss`. The empirical reference is exactly the same registered empirical PMF, so TV is at most zero by registered_eq and tvDist_self_eq_zero. The old empirical_loss is a one-draw loss to a fixed safe reference. Zero empirical fit here is not asserted to be zero true error.

13. **`RegisteredSelectionWitness.referenceFailure_eq`**. Prior candidates: `StatisticalRiskBoundary.actualFailure_eq`, `UEOT.V3.FiniteCTMCPathKL.fullReference_eq`, `DeploymentCoverageWitness.reference_one_step_failure`, `DeploymentCoverageWitness.reference_two_step_failure`. The new equality identifies empirical-reference path failure with a selected empirical-row mass. The hinted older objects are fixed actual risk 3/4, CTMC generator-independent counting reference measures, and always-safe one/two-step reference paths. None yields this data-dependent identity.

14. **`RegisteredSelectionWitness.confidenceBudget_eq`**. Prior candidates: `StatisticalRiskWitness.concrete_confidence_budget`. The new exact value 16*exp(-8) comes from two registered rows, all finite events, N=256 and radius 1/8. The old value 64*exp(-8) comes from a different full-row sparse-test experiment. registered_card is reused; equal exponential factors do not identify the budgets.

15. **`RegisteredSelectionWitness.confidenceBudget_small`**. Prior candidates: `StatisticalRiskWitness.concrete_confidence_budget`. The new 16*exp(-8) <= 1/16 bound uses confidenceBudget_eq and the existing concrete_confidence_nonvacuous inequality 64*exp(-8) <= 1/4. It scales the prior estimate rather than reproving the exponential inequality.

16. **`RegisteredSelectionWitness.selection_probability`**. Prior candidates: `StatisticalRiskBoundary.selected_bad_probability`. This gives the actual action-selection probabilities 1/8 and 7/8 using selectedAction_law and actualRow_mass. The hinted selected_bad_probability is an older selected calibration-failure event of probability 7/16 under a different experiment.

17. **`RegisteredSelectionWitness.actual_joint_failure_exact`**. Prior candidates: `StatisticalRiskBoundary.actualFailure_eq`. The new 9/64 joint failure uses the canonical selectedTrainingDeployment_failure_tower, actual_failure, selectedAction_pmf and coverage_expectation_map. A fixed row-risk theorem in a different model cannot replace this constructed joint-law calculation.

The three new consumer regressions preserve all historical layer checks and
verify the new registered support/checker/joint proof routes, the complete
native field/axiom/owner scope, and the three retained private computations.
An isolated source-mirror run passed all **28 Python tests**, including the
unchanged clone scanner on all **659** modules: its result still exactly
matches the immutable 68 rows. This is local consumer verification, not a
claim about later production installation, immutable Git objects or remote CI.

### Layer 8 — variable registered samples and arbitrary observation risk

This layer uses the actual canonical policy base
`86dfbec88c20a9da3c98cd222611aac55cc55f2f`, after governance PR
[#355](https://github.com/MurphyHoops/UEOT/pull/355) merged. Seven new modules
extend the source census from 659 to 666. The complete production source
fingerprint is
`29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`.
The actual full `lake build UEOT` completed successfully (9,372 jobs,
107.421 seconds). The earlier focused PASS is reused only after equality of
all 666 source files, three environment files, nine dependency checkouts,
Lean/Lake binaries and import environment. The interrupted earlier full
attempt remains an interrupted record.

| Artifact | SHA-256 |
|---|---|
| [REGISTERED_INTERFACES_NATIVE_V1.json](REGISTERED_INTERFACES_NATIVE_V1.json) | `75945bbff2e0212a406f27859c68a777bc3deba75b0b8aece66c84236b5e39c1` |
| [REGISTERED_INTERFACES_REUSE_OVERLAY_V1.json](REGISTERED_INTERFACES_REUSE_OVERLAY_V1.json) | `6667bf7a908d713394e5daae5291c3a82f1ff7b3da144e2addf3da5959d0e781` |
| [VERIFY_REGISTERED_INTERFACES_OVERLAY_TYPES.lean](VERIFY_REGISTERED_INTERFACES_OVERLAY_TYPES.lean) | `0d3eb26c9471e1701a28652f308c9dd1e1ccac72c0b9ef36eec27c1bc3165d32` |

Both actual Lean executions succeeded and their complete JSON exports agree,
including types, universe parameters, physical ownership, all proof constants
and transitive axioms. The native scope covers **92 theorem constants in
eight physical modules: 53 newly registered public names, 17 private constants
and 22 other public constants**. Those 22 include previously registered
declarations and are not all described as generated declarations. All 92
axiom closures are subsets of `propext`, `Classical.choice`, `Quot.sound`.
The actual type comparisons are **216,982 across the old 4,094-node registry
and 1,378 within the 53 registrations**, with zero collisions. Raw stored-type
comparison retains its earlier limits; it is not semantic equivalence checking.

The 53 registrations consist of **52 new public source declarations and one
unchanged historical declaration**,
`UEOT.V3.FreeInformationValue.integrable_finset_sup'`. Its exact trailing
apostrophe was omitted by the historical lexical registry. This layer repairs
that name additively with unchanged source bytes and native ownership/type
evidence; it neither changes the frozen parser nor counts the repair as a new
mathematical proof. An actual narrow scan of all 4,094 prior proof terms finds
one direct caller, `UEOT.V3.FreeInformationValue.p_ref_03`. Its old edge set is
preserved and its one actual edge to the repaired name is added in memory.
The consumer verifies the complete observed caller set, the prior edge set,
the native constants and `actual = prior ∪ delta` before changing any row.
Historical CSVs and the first seven overlay artifacts remain byte-for-byte
unchanged.

The new registrations contribute **97 outgoing registered edges**; the old
caller contributes **one separately counted repair edge**. The historical
eight-layer graph has **4,147 nodes and 5,418 edges**. Those eight overlays account for
354 nodes, 531 outgoing edges from their nodes and one repair of an old node.
The 18 new lexical hint groups bring the cumulative count to 75. The earlier
independent review of all 18 groups and 39 pairs is bound to the unchanged
25-file source scope and the actual native results in the
[completion review](../../unified_closure/registered_interfaces/release_20261021/independent_review/NATIVE_EVIDENCE_REVIEW_2.md).
Original `PENDING` fields remain historical outputs; the new review records
their later resolution without rewriting them.

The mathematics keeps the actual experiment and policy throughout:

- Fixed positive row sizes `N j` use true sample coordinates `Σ j, Fin (N j)`.
  Calibration needs independence within each row and the stated true row law;
  it does not impose extra independence between rows.
- Finite microscopic and action types permit arbitrary measurable observation
  types with measurable singletons. A finite observation image plus one escape
  atom preserves TV against the same actual source. It does not preserve TV
  between arbitrary references, nor identify a reference that can exit and
  return with an absorbing coordinatewise pushforward.
- The selected fit, actual occupancy cap, event measurability, event envelope
  and numerical check are all required on the same Good event. With
  `β ∈ [0,1]`, the actual training–deployment failure is at most
  `min(1, α_N + (1−α_N)β)`; the bad event is charged once.
- The viability adapter proves zero uncertified occupancy for its own
  `viableFamilyPolicy`. This does not imply zero physical failure or infinite
  survival. Row sizes are fixed before training; no adaptive stopping theorem
  is claimed.

The [mathematical audit](../../unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)
states the full hypotheses, quantifiers, Nat-valued escape counterexample and
the boundaries of these interfaces. Complete consumer verification passed
**45 reuse tests and all 30 FKRG tests**, including the real fast audit and
the unchanged 68-row clone scan over all 666 modules. Actual canonical-base
parser tests passed separately. Final Git-object preflight, remote checks and
resulting-main validation retain their own release receipts. No counted
Core/Compression tier or global scientific-completeness claim is promoted.

### Layer 9 — same-source long-term laws, infinite policy and rowwise SISC

This layer uses the canonical authorization base
`ff71e63256c88ad2bb527fdd3004d55c77894ab7` and extends the intact historical
666-module source census with **12 physical UnifiedClosure modules**. Eight
modules promote the same-source long-term chain, `InfiniteSupportViability`
constructs one all-times causal policy, and `RowwiseProbeSampling`,
`SISCRowwiseProbeCalibration` and `SISCRowwiseProbeWitness` implement the
rowwise scalar experiment and its SISC consumers. The frozen production
source fingerprint is
`60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`.
It identifies the actual source bytes; it is not a claim that a future Git
commit or resulting main has already been accepted.

On those bytes, the full `lake build UEOT` passed in **39.787 seconds**.
The native exporter and fixed-certificate replay both passed, in **59.215**
and **58.444 seconds**, and their complete JSON objects agree. The equality
covers physical owners, stored universes, displayed types, ordered proof
constant arrays and axiom lists, not only summary counts. Earlier failures
and their source snapshots remain separate historical records. Independent
**SOURCE / EXECUTION: CLEAR** binds this source fingerprint and the raw
execution evidence. Exact Git-object preflight, PR and resulting-main
acceptance are separate release gates, indexed by
[#146](https://github.com/MurphyHoops/UEOT/issues/146) and the corresponding
PR check runs; local proof receipts do not substitute for them.

| Artifact | SHA-256 |
| --- | --- |
| [LONGTERM_CONTROL_STATISTICS_NATIVE_V1.json](LONGTERM_CONTROL_STATISTICS_NATIVE_V1.json) | `0b6b77967ad43da71cec3a569b361501f591a7a8b384d072dda31af1b897d02c` |
| [VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean](VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean) | `0643f8dfca2daec2ce6b4638f712f6abcacf8f91f31669a37120f397d6c27213` |
| [LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json](LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json) | `cb5792eff95b2a1386a7c0832eeeedc5a283f212b462f2c6c6d3342dd5e1bb06` |

The compiler-owned scope contains **199 theorem constants**, including
**90 confirmed public source candidates**. All 199 retain their actual
physical `source_module`, `is_private`, stored `level_parameters`, `ppExpr`
type display, direct proof constants, direct theorem constants and
transitive axioms. Every axiom closure is a subset of `propext`,
`Classical.choice`, `Quot.sound`. The public list is a navigational subset
of that compiled scope; private and other non-candidate constants remain
in the native evidence.

The fixed certificate compares the 90 public types with all **4,147** prior
registered types: **373,230 cross-layer** and **4,005 internal** comparisons,
with **zero collisions**. This retains the historical raw stored-type
`Meta.isDefEq` protocol and its stored-universe and instantiation limits.
Zero collisions do not establish general logical independence. The native
public proof graph adds **149 direct registered edges**. The current graph
therefore contains **4,237 nodes and 5,567 edges**; the nine overlays account
for **444 nodes and 680 outgoing edges**, in addition to the separately
retained eighth-layer repair of one old-node edge. The 27 new lexical hint
groups bring the cumulative count from the historical 75 to **102**;
name hints are not proof-dependency or typed-equivalence certificates.

The mathematical additions retain their source and quantifier boundaries:

- The eight-module long-term chain keeps the original initial PMF,
  closed-loop kernel and stationary observation feedback through complete
  state prefixes, killed terminal masses, positive-survival conditioning,
  QSD specialization, first-exit flux and the actual infinite survival
  event. The exit-flux telescope directly reuses the canonical time-zero
  survival theorem. The infinite survival limit may be zero.
- The infinite-policy construction fixes the entire possibly nonautonomous
  transition and certification sequence before varying the horizon. Nested
  finite-action choices construct one complete causal policy, and its own
  actual row law has zero uncertified occupancy at every time. The result
  does not provide finite-memory realization or physical safety without
  the additional corresponding premises.
- Rowwise scalar calibration uses fixed positive `N j`, actual row laws and
  within-row independence, with one measurable Good event. The N3 interval
  radius is `|J|u` for the summed absolute-coordinate risk, and its
  population means must match the same model/source/action/read. N6 keeps
  its distinct reference-response match, full parent-type gap and external
  authentication. Neither constructor takes the unknown correct label.
  The failure endpoints currently provide `μ.real` outer-measure bounds;
  they do not separately export failure-event measurability certificates.
- The two-probe, two-candidate witness constructs an actual deterministic
  PMF product experiment with row sizes 128 and 256. Its scalar budget is
  `2 exp(−4) + 2 exp(−8) ≤ 28/45 < 1`. Changing only the declared kernel
  supplies a concrete exact-Good record whose interval is not calibrated.
  These are formal probability witnesses, not empirical observations.

The [results and boundaries](../../unified_closure/longterm_control_statistics_v1/RESULTS_AND_BOUNDARIES.md)
state the complete mathematical scope. The frozen counted generator and
106 P-ID classifications, and the global `NOT_ESTABLISHED` status, remain
unchanged. Historical type-group, near-type and clone evidence is retained;
the unchanged scanner still requires an actual full-current-source match
against its immutable 68-row table.

### Layer 10 — finite support fixed points and complete finite memory

This layer uses canonical authorization base `299a4e3a71914af064ccd7916bb285bac201f62a` and adds six physical
UnifiedClosure modules to the intact 678-module source census:
`FiniteMemoryPolicy`, `FiniteSupportFixedPoint`, `SupportMemoryController`,
`SupportMemoryCheck`, `FiniteMemorySeparation` and `FiniteMemoryCheckWitness`.
The frozen production source fingerprint is `179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6`. It identifies source
content; Git-object, PR and resulting-main acceptance have separate receipts.

The actual full `lake build UEOT` returned zero on this source. Native
export and fixed-certificate replay also returned zero and emitted equal
complete JSON objects. This equality covers physical owners, stored
universes, displayed types, full ordered proof-constant arrays and axiom
lists. The raw source preflight retains its original PENDING state; actual
execution and metadata registration each have their own records.

| Artifact | SHA-256 |
| --- | --- |
| [FINITE_MEMORY_NATIVE_V1.json](FINITE_MEMORY_NATIVE_V1.json) | `5a06a9df4a662327e48e34f2743f485fb7471f86f99e18fd71d6feceb7eaa471` |
| [VERIFY_FINITE_MEMORY_OVERLAY_TYPES.lean](VERIFY_FINITE_MEMORY_OVERLAY_TYPES.lean) | `0a39a7605b4454f6410bc9f382dc79feb07ef42bc655db1a900e24fd8e73b762` |
| [FINITE_MEMORY_REUSE_OVERLAY_V1.json](FINITE_MEMORY_REUSE_OVERLAY_V1.json) | `cd697c44f7a5d7e4b73a0b53d7477b2e1e8aee43ab55e105b515cd531fd63d38` |

The native census contains **82 compiler-owned theorem constants:
35 public source candidates, 22 private constants and
25 other nonprivate constants**. Each retains its physical owner,
stored universe parameters, type display, complete direct proof constants,
direct theorem constants and transitive axioms. The axiom closure of every
record is contained in `propext`, `Classical.choice`, `Quot.sound`. This full
scope also includes generated theorem constants from `FiniteMemoryPolicy`,
which has no explicit public source theorem candidate.

The 35 new public types were compared with all **4,237** prior registered
types: **148,295 cross-layer** and **595 internal** raw stored-type
`Meta.isDefEq` comparisons, with zero collisions. These checks retain the
stored-universe and instantiation limits of the historical protocol; they
do not establish general logical independence. The new proof graph adds
**47 direct registered edges**. The current ten-layer graph therefore
has **4,272 nodes and 5,614 edges**, with **479 overlay nodes
and 727 outgoing overlay edges**. The old-node repair edge from
layer eight remains separate. Six new name-hint groups bring the cumulative
count to **108**; lexical similarity does not certify theorem reuse.

The substantive reuse routes connect `finiteMemoryCheck` correctness to
`finiteRelationViabilityCheck_correct`, and connect the bounded-horizon
criterion and the actual controller's all-times occupancy to the prior
`initial_viability_iff_exists_zero_uncovered_policy` and
`zero_uncovered_iff_support_certified` theorems. The Boolean decision witness
and the stationary-feedback separation use their respective actual initial
laws and deployment row laws. The registered graph is checked against the
native proof constants, rather than inferred from source text.

The mathematical boundary is explicit:

- Nonempty supports lying within an observation fiber form a finite arena
  of size `M`. The decreasing support iteration stabilizes by `M` and yields
  its greatest fixed point. The ambient observation type need not be finite.
- The complete autonomous support controller's memory type has exactly
  `M + 1` states, including the empty support and fixed fallback, with
  `M + 1 ≤ 2 ^ |X|`. Under exact fixed-support and certification matching,
  its memory equals the actual trace support on every complete history.
  Its own deployment row law has zero uncertified occupancy at every time
  precisely when the finite initial-support criterion holds. Numerical
  transition probabilities may still vary with time.
- The executable Boolean criterion uses `B = 2 ^ |X| - 1` and the existing
  finite-horizon recursion. Exact initial support, transition support and
  certification matching are theorem premises. The implementation does not
  supply an elimination algorithm, a dynamic-programming complexity bound,
  or a computable winning-action table; the general action selector retains
  `Classical.choice`.
- The two-state singleton-initial experiment admits an autonomous memory
  controller, whereas every fixed randomized observation feedback satisfies
  `U₀ + U₁ = 1`. The checker also rejects mixed initial support under a
  different, explicitly uniform initial law. The witnesses do not identify
  the handwritten Boolean controller with the general support controller.
- Zero uncertified occupancy does not by itself imply physical safety.
  Source-supported consistency does not change the reference process's
  fallback or check budget. Fixed killed matrices still need numerical
  homogeneity or a justified finite-phase extension.

The metadata registration adds only `lexical_pr_preflight` and
`registration_provenance` to the raw candidate and archives the original
execution bytes. The existing nine overlays, historical receipts, 37
equal-type groups, 77 equal-type names, 15 near-type pairs and 68-row clone
index remain intact. Consumer regressions separately check complete native
ownership and proof edges, the concrete reuse routes, and the metadata-only
registration. Their actual execution is a subsequent consumer gate.

The [results and boundaries](../../unified_closure/finite_memory_v1/RESULTS_AND_BOUNDARIES.md)
state the exact hypotheses and remaining work. Frozen 106 P-ID counts remain
11 generated / 89 adapters / 6 boundaries, the four counted generators are
unchanged, and strong global mathematical closure remains `NOT_ESTABLISHED`.


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

    lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_FINITE_MEMORY_OVERLAY_TYPES.lean

## Strongly typed and provenance-limited evidence

- 633 immutable-base source modules = 622 UEOT-maintained + 11 adapted upstream modules;
  ten governed overlays extend the live census to 684 = 673 + 11.
- 3,793 immutable-base public source theorem proofs + 479 governed registrations
  (including one historical public-name repair) = 4,272 live graph nodes, with
  5,614 direct registered-source theorem
  references. The historical four overlays add 0, 3, 6 and 73 certified direct edges;
  the fifth adds 91, the sixth adds 98, and the seventh adds 163 certified direct edges.
  The eighth adds 97 edges from new registrations and one certified old-node repair.
  The ninth adds 149 edges and the tenth adds 47, giving 727 outgoing edges from overlay nodes;
  the old-node repair remains a separate addition.
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
  The current scanner recomputes all 684 modules and rejects any difference
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
overlay-chain hashes against the exact 684-module live source census. It refuses to
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
