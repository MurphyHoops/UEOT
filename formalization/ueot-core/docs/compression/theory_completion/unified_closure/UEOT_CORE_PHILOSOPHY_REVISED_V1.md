# Universal Evolutionary Object Theory: A Conditional Science of Objects, Persistence and Purpose

**Core argument — revised manuscript V1**

This continuous draft reworks the Core argument of the supplied UEOT paper. Its source baseline is the mathematical manuscript v3.0 and canonical Core at `0c093e9fae990d6ef8d670163b84ec93bd6fb025`. Five research additions have passed formal Lean builds, the full `UEOT` build of 9352 jobs, native export and a separate fixed-verifier run. The two native outputs match as complete JSON objects. Local research integration validation has also passed; its canonical baseline and audit receipt are recorded in the verification note below. Remote research review, CI and merging are tracked by the associated Git/PR records. These verification results do not establish the empirical premises of the theorems.

## Abstract

Universal Evolutionary Object Theory investigates whether object formation, persistence, control and evolution can share a common mathematical architecture. An object is studied through its relation to a world process: what future distinctions it preserves, which interventions affect it, and how its organization continues through change. We develop this perspective through conditional constructions connecting predictive representations, controlled dynamics, realization and safety. The framework includes positive finite-model results and counterexamples that delimit stronger claims. In particular, neither a geometric loop nor a predictive quotient alone establishes physical self-maintenance, a unique objective or a unique long-run attractor. Resource and information constraints provide a common modeling interface whose interpretation requires independent identification. A finite-sample extension connects measurements from actual transition rows to coarse-model path error and microscopic failure risk under a common policy. Its guarantees retain explicit experimental, representation and failure-envelope conditions. The proposed unity is therefore an expanding set of compatible, testable implications, with clearly identified points at which a model can fail.

## 1. The problem of objects through change

Many scientific questions concern something that remains recognizable while its constituents, state or behavior change. A useful account must explain which differences matter, what maintains the pattern, and when continuation ends. UEOT approaches these questions by making the relation between a candidate object and its environment explicit.

The starting point is a world process with specified observations, actions and experimental protocols. A candidate representation groups histories or states according to the future distinctions relevant to the question. Its adequacy depends on which futures are compared and which interventions are permitted. This relativity does not make every grouping equally informative. A constant representation may discard the very distinctions the experiment detects; retaining the entire history may provide no useful compression. Object discovery must specify a nontrivial comparison and the evidence that supports it.

A predictive certificate, a causal certificate and a history of continued identity answer different questions. Prediction concerns future responses. Causal interpretation requires an intervention model. Continued identity requires a declared relation between successive realizations, including possible repair, division and loss. These structures can be connected, but their connection must be demonstrated. Formed provenance alone, for example, does not ensure that an object can be distinguished through the registered interactions.

This relational approach revises the original paper's direct identification of existence with topology. The mathematical manuscript already replaces that identification with a layered operational account. The aim is to determine when several descriptions concern the same process and preserve the properties under investigation. [Original PDF, pp. 2–5, §§1.3–2.2; Mathematics, §§0.1, 3–4, 11–12; [formal semantic boundaries](../../../../UEOT/V3/Compression/TheoryCompletion/SemanticBoundaries.lean).]

## 2. Ω as an organization-maintenance question

The original Ω-loop proposal captures a valuable question: what relations allow an organization to sustain or restore itself? A geometric cycle, a directed feedback circuit, recurrent behavior and physical regeneration are distinct answers. A stable trajectory may approach a point, while a periodically driven observation may trace a loop. Without specifying the space, observation and causal mechanism, a nonzero first homology group does not identify the required maintenance structure.

A conditional interpretation begins with a frozen object certificate, a finite horizon and explicit interventions on mechanisms. It records which interventions make the certificate fail. If failure is monotone under additional removals, its minimal destructive sets determine a failure hypergraph. If removing an inhibitor restores function, monotonicity fails and the richer response structure must be retained. Topological descriptors can still contribute, provided a realization model explains what their preservation implies.

There are substantive positive results in this direction. In a finite controlled model, the existing construction derives a maximal viable region and a preserving controller from the same source dynamics. Under the required initial-support and registered-safety conditions, it supplies an actual infinite path law that stays safe at all times. A separate nonempty example establishes that this construction need not be vacuous. These results do not require every viable object to execute a geometric cycle.

Physical reconstruction introduces further information and material requirements. If two programs share the same available physical record, no decoder using that record alone can recover both correctly. Supplying distinguishing information can resolve this information obstruction; it does not itself construct a material reproducer. Thus Ω organizes questions of dependence, recovery and persistence without declaring every answer universal. [Original PDF, p. 4, §2.2, and p. 38, Proposal 1; Mathematics, §§9, 12–13; [same-source all-times construction](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreSourceAllTimesAssembly.lean), [nonempty witness](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreNonvacuousAllTimesWitness.lean), [program-information boundary](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ProgramPurposeInformationBoundary.lean).]

## 3. A common process connects prediction, realization and control

A predictive representation supports autonomous macro dynamics only under suitable closure conditions. For a finite controlled process, a stable partition can be constructed from the original transition, output and reward tables. Exact quotient identities then connect the macro model to the same microscopic source, allowing control values and registered properties to be transported.

An arbitrary coarse map has no such automatic guarantee. Its projected process may retain dependence on the full observed history through hidden-state posteriors. A state-only macro kernel is then a comparison model, whose accuracy must be bounded. Likewise, preserving visible predictions does not ensure that a hidden-state reward, physical damage label or historical program factors through the representation.

This distinction makes scale transport a mathematical obligation. State maps compose, but identity, repairability and purpose cross those maps only with their respective preservation proofs. Changing observation scale and advancing physical time are different operations. Their compatibility, when available, comes from the common underlying process.

The same discipline applies to control. A safe controller need not maximize unconstrained immediate reward. Existing examples place nonzero reward, risk and a nonempty safe optimum within one stochastic source. They make a stronger connection than combining an unrelated prediction witness with an unrelated survival witness. [Mathematics, §§7, 18–20, 28, 31; [finite common-source assembly](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/UnifiedCoreClosureCertificate.lean), [hidden-goal obstruction](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictiveGoalClosureBoundary.lean), [scale calculus](../../../../UEOT/V3/Compression/TheoryCompletion/ObjectScaleCalculus.lean), [reward–safety example](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeRewardConflictWitness.lean).]

## 4. From measurements to finite-horizon risk

### 4.1 The deterministic path statement

Let $X,Y,A$ be finite microscopic states, coarse states and actions. Let $P_t(x,a)$ be the true transition PMF, $q:X\to Y$ a chosen representation, and $Q_t$ a macro reference kernel. Both systems use one causal policy reading the same coarse state-and-action history, with respective initial laws $p_0$ and $q_\#p_0$. Suppose

$$
\sup_{x,a}D_{\mathrm{TV}}\bigl(q_\#P_t(x,a),Q_t(q(x),a)\bigr)
\le\epsilon_t\in[0,1],\qquad t<T.
$$

The actual microscopic path law, pushed through the history map, differs from the reference path law by at most

$$
B_T=1-\prod_{t<T}(1-\epsilon_t)
\le\sum_{t<T}\epsilon_t.
$$

The history map retains past actions. This statement does not require the actual projection to be Markov on $Y$. For a microscopic failure event $E$, an observable conservative envelope $F$ must satisfy $E\subseteq q_{\mathrm{hist}}^{-1}(F)$. The resulting bound is

$$
\mathbb P_{P,\pi}(E)
\le\min\{1,\mathbb P_{Q,\pi}(F)+B_T\}.
$$

A state-level implication from microscopic failure to a coarse unsafe label supplies an envelope for failure at any time from the initial state through the declared horizon. The implementation also constructs the smallest conservative label: a coarse state is unsafe when its fibre contains any unsafe microscopic state. Coverage and minimality are proved, removing the need to assume coverage for this construction. A broad envelope may nevertheless be uninformative. [Mathematics, §7.3, P-DYN-03; [actual finite-path theorem](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonRisk.lean), [microscopic failure envelopes](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/MicroscopicFailureRisk.lean).]

### 4.2 A common sampling event

Fix bounded tests $f_{t,i}:X\to[0,1]$. For each row $(t,a,x)$, assume $N>0$ measurable, mutually independent samples whose individual laws equal the actual $P_t(x,a)$. Different rows may be dependent. These are controlled row experiments; the theorem does not extract them automatically from one observational trajectory or establish that hidden states can be reset and accessed.

For fixed nonnegative radii $\rho_t$, let $G$ be the event that every empirical test mean differs from its true row expectation by at most $\rho_t$. Existing two-sided Hoeffding results and a finite union bound give

$$
\mu(G^c)\le
\sum_{t<T,a,x}2|I|e^{-2N\rho_t^2}.
$$

Here $\mu$ is the training-data law. The new source-matching lemma identifies the population mean with the exact transition-test expectation consumed downstream; it does not substitute expected absolute loss for absolute mean mismatch.

On this single measurable good event, later choices may use the data while remaining subject to their deterministic checks. Fixing the test family, source, horizon, sample count and radii is essential. Selecting previously unregistered tests or repeatedly inspecting data under a fixed-time guarantee requires additional statistical arguments. [Mathematics, §§16.1–16.8; [sampling calibration](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskCalibration.lean).]

A concrete PMF counterexample shows why separate per-action coverage alone is insufficient. Two actions each have true failure probability $3/4$. Each fixed action has exact calibration-failure probability $1/4$, but choosing the empirically safer action from the same training data raises that probability to $7/16$. On that event, the empirical value plus $1/4$ understates the selected row's actual risk. These probabilities are computed directly from the training PMF; the example concerns training-time selection, not online adaptive sampling. [The [selection boundary](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskBoundary.lean).]

### 4.3 Two complementary reference-model routes

The first route uses a small fixed test family. Suppose each target class indicator has a uniformly accurate linear reconstruction, with residual $\delta_t$ and coefficient $\ell^1$ bound $\kappa_t$. Suppose measured test means differ by at most $\eta_t$ within each chosen class. For $m$ classes, simultaneous calibration yields

$$
\epsilon_t=
\min\left\{1,\frac m2
 [2\delta_t+(\eta_t+2\rho_t)\kappa_t]\right\}.
$$

This compares the source to the **true representative model** $Q_t(c,a)=q_\#P_t(r(c),a)$, where $q(r(c))=c$. Two calibration errors appear because two true rows are compared. The half-sum of coordinate errors is converted to TV using the existing finite-PMF identity. This route benefits from informative tests, but the reference kernel still contains unknown true rows. [Mathematics, §7.3; [calibrated row budgets](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CalibratedRiskRows.lean).]

The second route constructs the reference directly from observations. A uniform PMF on sample indices, mapped to the observed outcomes, defines a normalized empirical row $\widehat P_{t,x,a}$. Use the fixed library of all finite event indicators. Then $G$ controls $D_{\mathrm{TV}}(P_t(x,a),\widehat P_{t,x,a})$ by $\rho_t$. The library has $2^{|X|}$ tests, an explicit cost in the confidence bound.

Choose $q$ and prototypes $r$, form $\widehat Q_t(c,a)=q_\#\widehat P_{t,r(c),a}$, and check the empirical fit

$$
\sup_{x,a}D_{\mathrm{TV}}\bigl(q_\#\widehat P_{t,x,a},
                         \widehat Q_t(q(x),a)\bigr)\le\eta_t.
$$

Data processing and the triangle inequality give $\epsilon_t=\min\{1,\rho_t+\eta_t\}$. Only one statistical error is needed because the comparison endpoint is empirical. Prototypes need not be a quotient section: the fit is checked directly against their actual empirical rows. The common good event supports all subsequent finite representations, prototypes, initial laws and common policies satisfying these checks. [Mathematics, §§16.1–16.2; [empirical reference construction and certificate](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/EmpiricalReferenceRisk.lean).]

Both routes certify a statement about deployment risk with training-data confidence. A joint training-and-deployment failure probability requires a measurable data-dependent deployment law and integration of conditional risks. The reference model's event probability also needs calculation or separate certification. Neither route infers unlimited safety from a finite error budget: a genuine absorbing-leakage example has arbitrarily small positive row error while cumulative failure tends to one. [Mathematics, §§16.9, 21, 30.4; [leakage counterexample](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/AbsorbingLeakage.lean).]

### 4.4 A nontrivial instance of the common certificate

One four-state model realizes the sampling and risk contracts together. Its state has a visible Boolean bit and a persistent hidden bit $h$, with Boolean action $a$. The true probability that the next visible bit is unsafe is $1/16+\mathbf1_h/8+\mathbf1_a/8$. Dropping the hidden bit gives a noninjective representation whose partition is proved not stable: hidden-state and action effects are each nonzero, with gap $1/8$. This example instantiates the true-representative route.

The training experiment is constructed as a finite product of the actual source-row probability measures; its coordinate samples have the required marginal laws and independence. For two steps, 16 rows, two fixed class-indicator tests and $N=4096$ samples per row, take $\rho=1/32$, $\delta=0$ and $\kappa=1$. The exact confidence budget satisfies $64e^{-8}\le1/4$, so the common measurable event has $\mu(G)\ge3/4$. On $G$, the empirical fibre fit is derived to be at most $3/16$, producing row budget $1/4$ and path budget $7/16$.

Use the common constant action `false`, representatives with hidden bit `false`, and an initial law with visible bit `false` and a uniform hidden bit. Each reference transition still has failure probability $1/16$ and permits recovery. Its exact probability of ever failing from the initial state through step two is computed from the actual causal path PMF. Exact coordinate transport identifies this Boolean calculation with the reference law on reachable quotient classes. This transport concerns the reference process; the microscopic partition remains non-stable. On the same $G$,

$$
\mathbb P_{Q,\pi}(F)=\frac{31}{256},\qquad
\mathbb P_{P,\pi}(E)\le\frac{31}{256}+\frac7{16}
=\frac{143}{256}<1.
$$

The theorem `joint_statistical_microscopic_risk_witness` combines non-stability, a nonempty training event of probability at least $3/4$, and this strict finite-risk bound. It establishes that the sampling, representation, control and failure contracts can hold within one nontrivial model. The numerical instance uses a fixed policy; it does not prove that a learning procedure finds an optimal policy or supply a joint training-and-deployment failure rate. Access to the required source rows and the physical meaning of the unsafe label remain experimental obligations. [The [constructed witness](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskWitness.lean) and existing [P-FAC-01 coordinate transport](../../../../UEOT/V3/RepresentationCovariance.lean).]

## 5. Purpose and the identification of Π and Φ

Purpose enters through an evaluation bridge: admissible policies, horizon, resources, outcomes and the standpoint from which they are ordered. The same controlled dynamics can support opposite optimal actions under different evaluations. Defining the observed policy as uniquely valuable after observing it would make optimality unfalsifiable. A scientific purpose explanation must instead constrain or identify the evaluation mechanism and predict responses outside its fitting data.

GOD can then denote an optimal-action correspondence. It may be set-valued and need not coincide with an instantaneous gradient. GOA describes the appropriate long-run structure of the resulting policies: limit sets, invariant occupation, recurrent-class mixtures or conditional-survival structures. Unique convergence and stability require their own assumptions. Existing finite models exhibit multiple optimal actions and multiple invariant laws.

Π and Φ provide useful names for independently registered resource and information quantities. Their signs and units must be fixed. For an objective $J=\Pi-\lambda\Phi$, the transformation

$$
\Pi'=\Pi+\lambda\chi,\qquad\Phi'=\Phi+\chi
$$

preserves $J$. Behavior alone therefore does not uniquely identify the axes. Independent measurements or selective interventions can anchor them. A stronger claim of a common two-dimensional mechanism has testable rank consequences; compatibility within an uncertainty tolerance is weaker than proving exact rank two. Rejection must permit a richer mechanism rather than an unrestricted relabeling of drives. [Original PDF, pp. 6–7, §2.3; Mathematics, §§18–19, 21, 23; [gauge identification](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveGaugeCompleteness.lean), [two-dimensional rejection](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCJoint2DRejection.lean).]

## 6. Empirical refutation and philosophical consequences

The framework becomes informative when it commits to a source model, protocol and measurable failure criterion before interpretation. A candidate may fail because responses are not preserved, a proposed causal dependence does not survive a matched intervention, deployment leaves the sampled support, a common two-axis mechanism is rejected, or an asserted identity cannot be transported. Finite observations do not establish exact equality without separation or structural conditions. Abstention is therefore part of certification. Directional diagnostics must also distinguish forward from reverse alignment, handle zero vectors and use independently calibrated thresholds; a perpendicular-component ratio alone cannot do this.

The philosophical consequence is a qualified naturalization of functional purpose. Mechanisms can be compared by their counterfactual contribution to persistence or a declared task. Predictive, causal and reproductive structures can be related without equating them. A successful population mean operator does not prove individual immortality, and reproduction does not by itself establish continued identity of the parent.

Subjective experience and normative value remain additional questions. Stability, successful replication or alignment with collective behavior does not alone entail consciousness or an ethical obligation. The mathematical manuscript distinguishes functional meaning, representational relations and normative bridges. Preserving these distinctions allows a common architecture to clarify where empirical explanation ends and additional value commitments enter.

UEOT's unifying proposal is thus concrete: use shared processes and explicit interfaces to make predictions, interventions, control and persistence constrain one another. The strength of the theory grows when a premise is independently measured or constructively discharged, and when a counterexample changes its stated scope. This supplies a research program whose central connections can become stronger without declaring every evolving system an instance of a predetermined universal optimum. [Original PDF, pp. 26–28 and 40–41; Mathematics, §§24–27, 31; [Unified Closure Mission](UNIFIED_CLOSURE_MISSION_V1.md).]

## Source and verification note

Original philosophical source: `01-UEOT_v3_top.pdf`, 43 pages, SHA256 `6c2acdf8d8232377066c3363ce3f0b0a14b3b60608c485ce70f2089c8a2263c3`. Mathematical source: `02-UEOT_Core_Mathematics_v3.0_Complete.md`, version 3.0, SHA256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`.

The [Chinese source-by-source feedback](PHILOSOPHY_MATHEMATICS_FEEDBACK_V1.md) records exact original passages, replacement decisions and the boundary between mathematical validity and empirical applicability. The older linked results belong to the cited canonical Core. The five additions are `StatisticalRiskCalibration`, `MicroscopicFailureRisk`, `EmpiricalReferenceRisk`, `StatisticalRiskBoundary` and `StatisticalRiskWitness`; their frozen source hashes and actual build results are recorded in its §0.3.

Native export and fixed verification both passed with identical complete output. Their module-provenance census covers 126 theorem constants, including private and generated constants, and finds only standard axioms. The 91 registered proof edges support the stated reuse chains, including the sampling and reference-coordinate interfaces used by the joint witness. The observed evidence and exact comparison protocol are explained in [Statistical Risk Closure V1](STATISTICAL_RISK_CLOSURE_V1.md).

Local integration against canonical main `78852812650eff0a4803596bf3379d4d792122d0`, including merged governance PR #339, has been verified, with the 18 integration files checked at that checkpoint matching byte for byte across the two environments. FKRG, reuse checks and the full UMC local audit passed. The [local audit receipt](STATISTICAL_RISK_LOCAL_AUDIT_V1.json), SHA256 `399f7c4fbe084c4ebd78510a3c772b1de8535ae803b299184d2664fb0a038bb4`, covers 47 UMC modules and 266 public source theorem candidates. Its native census contains 471 theorem constants: 266 confirmed public source candidates, 22 private constants and 183 other native public constants; all 471 axiom closures contain only standard axioms. The full `UEOT` build passed, and all 646 source modules are reachable in an acyclic import graph. These are recorded local verification results; the associated Git/PR records track remote research review, CI and merging. Empirical and global scientific closure are not asserted.
