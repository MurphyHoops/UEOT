# Variable registered samples to the actual selected joint

Research-only specification, 2026-10-20. Production files are unchanged.

## Artifact and current evidence

[`VariableRegisteredJoint.lean`](VariableRegisteredJoint.lean) is a research tail in this directory.
Its first actual focused compilation passed in 6.422 seconds, with exit code 0.
The combined source SHA256 is
`f124fedb8058d75d330dbf6675c8e7e5d5af7d242b00aec2b6ff7d70879c4f29`;
its exact construction and four standard-axiom reports are preserved in
[`research_evidence/joint-1/STATUS.json`](research_evidence/joint-1/STATUS.json)
and [`joint.log`](research_evidence/joint-1/joint.log).
The original pre-build specification remains a historical draft; this publication
records the subsequent execution without changing an earlier failure to PASS.

The prerequisite [`VariableRegisteredSamples.lean`](VariableRegisteredSamples.lean)
has also passed its actual focused build. Its validated source SHA256 is
`915b4f906c43429b25c010e7ffc44f766abf4066d9a32dcd91bb69fa7ce02e5f`.
It includes the explicit Sigma-coordinate type annotation; the first unsuccessful
attempt and the later successful result remain separate evidence.

For a single check, concatenate in this order:

1. `import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk`
2. The complete already validated `VariableRegisteredSamples.lean`.
3. This directory's `VariableRegisteredJoint.lean`.

Run `lake env lean` on that temporary combined file from the existing pinned
Core cache environment. There is no need to install a research `.olean`, edit
the production entry point, or run a full build. All imports occur before
any command. The tail ends with `#print axioms` for both of its theorems.

## Precise theorem

Fix finite state, action and observation types X, A, Y with measurable
singletons, a finite training space Ω with a probability measure μ, and any
measurable candidate type C. Fix before drawing ω:

- a horizon T;
- the actual source transition PMFs P(n,x,a);
- a registration predicate certified(n,x,a);
- the finite registered-row type J = CoverageRegisteredRow certified T;
- an allocation N : J → ℕ with N(j) > 0 for each j;
- nonnegative time radii ρ(n) for n < T;
- row samples S(j,k) : Ω → X for k : Fin(N(j)).

Every S(j,k) is measurable, its pushforward law under the **same** μ equals
the actual P-row indexed by j, and the samples within each individual row
are independent under μ. Independence between distinct rows is not a
premise. Neither allocation nor registration depends on the observed ω.

Define the row empirical PMF p̂_j(ω) using exactly N(j) samples and define

\[
G=\{\omega:\forall j\in J,\;
  \operatorname{TV}(P_j,\widehat p_j(\omega))\leq\rho(n_j)\},
\qquad
\alpha=\sum_{j\in J} 2^{|X|}\,2e^{-2N(j)\rho(n_j)^2}.
\]

The Lean definition writes the finite-event factor as
`Fintype.card (Finset X)`; this equals 2^{|X|}. The calibration proof obtains
μ(Gᶜ) ≤ α from the already proved generic unequal-allocation theorem. It
does not ask the caller to assume that probability estimate.

A total data-dependent selector selects c(ω) in C. Each candidate has a
coarse map q_c, initial PMF, reference transition Q_c and causal policy π_c.
Fix a common actual microscopic event E and candidate observable envelopes
F_c. On exactly G require:

1. Every registered row's actual selected empirical fit is at most η(ω,n).
   The empirical fit uses p̂_j(ω), q_{c(ω)} and Q_{c(ω)} of that same row.
2. The actual uncertified occupancy of π_{c(ω)}, under its selected initial
   law and the original P, is at most κ(ω,n).
3. E is contained in the pullback of F_{c(ω)} by the selected history map.
4. The checked budget is at most a fixed β in [0,1]:

\[
\min\left(1,\;Q^{\rm path}_{c(\omega)}(F_{c(\omega)})+
\sum_{n<T}\left[\varepsilon_{\omega n}
 +(1-\varepsilon_{\omega n})\kappa(\omega,n)\right]\right)
\leq\beta,
\qquad
\varepsilon_{\omega n}=\min(1,\rho(n)+\eta(\omega,n)).
\]

Then the selector is measurable, and the **constructed** joint experiment
first drawing ω from μ and then drawing the microscopic path under
P and π_{c(ω)} satisfies

\[
J\{(\omega,h):h\in E\}
\leq\min(1,\alpha+(1-\alpha)\beta).
\]

The common Good event is defined solely by the registered true-to-empirical
row TV conditions. Its definition is fixed before selection. All four
checks use that same event, so there is one bad-event contribution.

## Proof composition, with actual names

The tail creates two definitions and two theorems in namespace
`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck`.

| Stage | Existing declaration used | What it proves here |
|---|---|---|
| Actual calibration | `VariableRegisteredSamples.registered_row_calibration` | Apply with J = `CoverageRegisteredRow certified T`, row = actual P-row, radius j = ρ(n_j), and the original dependent sample family. |
| Canonical Good | `measureReal_mono` | The measurable calibration event is contained in the canonical all-row-TV event. Its complement inherits the same α. |
| True selected row | `empirical_coarse_row_tv` | On G, contraction and selected empirical fit produce the actual projected P-row estimate ε. |
| Actual path risk | `coverage_same_policy_microscopic_failure_risk` | Use the sampling-free endpoint on those proved actual row estimates and the selected envelope. |
| Actual occupancy | `ObservableActionCoverageContinuationCheck.deployment_coverage_budget_le_of_actual_occupancy_cap` | Replace the actual selected-policy occupancy by the same selected policy's proved κ. |
| Actual joint | `selectedTrainingDeployment_failure_le` | Integrate the Good-only conditional bound under the constructed joint and obtain α+(1−α)β. |

The source-risk theorem is in `DeploymentCoverage.lean`, the empirical row
bridge in `EmpiricalReferenceRisk.lean`, the occupancy bridge in
`ObservableActionCoverage.lean`, and the joint theorem in
`TrainingDeploymentJoint.lean`; all are under
`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/` in the actual Core.
The import of `RegisteredDeploymentRisk` supplies their established import
closure but does not invoke its old uniform-N empirical adapter.

The new proof does not reprove Hoeffding, finite event concentration,
path total variation, occupancy substitution, or the good/bad mixture.
It changes the actual sample type and supplies the missing bridge into the
sampling-free path theorem.

## Exact scope and remaining work

- Fixed unequal N(j) is supported in the proposed theorem. A data-dependent
  allocation N(j,ω), stopping rule, or registration chosen after seeing the
  samples is outside these hypotheses.
- Each row must have a positive allocation. Empty J satisfies this
  requirement vacuously and gives α = 0; it does not imply that deployment
  encounters certified rows or that its failure probability is zero.
- The general calibration permits arbitrary row radii. This joint adapter
  specializes them to ρ(n_j), so that the existing scalar-in-time path
  budget applies without an unproved row-to-time maximum bridge.
- The actual product experiment `SampleCoordinate N → X` from the already
  validated prototype automatically discharges hmeas, hindep and hlaw. This
  tail also accepts other genuine experiments satisfying those three
  contracts, including dependent rows. A separate wrapper specializing the
  entire long theorem to that product would add no mathematical bridge.
- Ω, X, Y and A remain finite at this joint endpoint. C can be infinite.
  The existing finite PMF joint argument and finite path TV endpoint have
  not been generalized by changing the calibration sample index.
- The Good-only envelope is a direct input to the already existing
  Good-branch source risk proof. If an envelope instead holds on an
  independent event H, one must control the complement of G∩H; the
  probability of H failure cannot be omitted.
- No policy existence theorem is claimed here. In particular the statement
  does not claim that all records admit a selector satisfying the checks,
  and it does not identify the selected policy with a separate classical
  viable-family choice.
- No numerical unequal-allocation adaptive witness is included in this
  draft. The N = 1,2 and empty-J companion checks test the dependent input
  boundary; the old N = 256,256 witness is not silently reclassified as an
  unequal-count witness.

## Minimal independent publication boundary

A first coherent result is the generic variable-row calibration together
with its real product experiment and the full joint bridge above, after
their focused builds, axiom reports and semantic review. The publication
must describe it as a fixed unequal sample allocation extension and retain
the finite observation type boundary. It need not include the unresolved
finite-image risk extension or a new concentration inequality.

This result is kernel-checked research outside the production import graph.
It has no new full native declaration export or production-consumer registration.
The publication boundary and independent review are recorded in the directory README.
