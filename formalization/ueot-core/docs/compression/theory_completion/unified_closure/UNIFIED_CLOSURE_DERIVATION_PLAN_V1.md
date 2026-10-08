# UEOT UMC — Formal Research Blueprint and Mathematical Derivation Plan v1

**Canonical tracker:** GitHub #302. This document supplements, but does not alter, the immutable `UNIFIED_CLOSURE_MISSION_V1.md` contract. Track TC is already registered; do not create an independent competing Theory Completion program.

## A. Re-derive the deep backbone, instead of equating similar words

### A1. One genuine process and declared operations

Start from one structure `W = (X, A, K, r, t, admissible, protocols)`; use a finite controlled `K : X → A → X → ℝ≥0` with row sums 1 for UMC-01, not arbitrary `Obj` records with unconnected states. Every other API must be derived from `W` or accompanied by an explicit, separately tested transport/faithfulness premise.

Existing Lean modules to reuse: `SISCFutureResponseCore`, `SISCFiniteStochasticQuotient`, `SISCStochasticPredictiveIntertwining`, `SISCEmissionTiming` and frozen P-QUO/P-PRED.

### A2. Derived predictive representation

For a deterministic controlled subsystem `T`, observation `h` and future action word `w`, define

`F(x)(w) := h(T_w(x))`.

The equivalence `x~y ↔ ∀ w, F(x)(w)=F(y)(w)` gives a canonical reachable quotient and a recursive update. **This is an established behavioral-equivalence theorem, not a new physics discovery.** For stochastic data, strong lumpability is required for a Markov quotient of microscopic tokens; a predictive belief-state lift can exist without that lumpability. Do not infer same physical object solely from `x~y`.

**UMC-01 target:** prove an exact conversion from a fully specified finite stochastic `K` which is Dirac on a deterministic `T`, into the SISC future response representation; prove the finite kernel induces the same next-state behavior as `T`; do not just assume two independent processes have the same names. Construct the nontrivial 2-state example and the alias/no-go counterpart.

### A3. Objecthood as a verified *additional invariant*

The correct template is not `predictiveState → SameObject` unconditionally. Instead seek a typed certificate over the **same** process whose verification implies formation/continuation:

`FormationCertificate(W, S, controls) ∧ IdentityTransportCertificate(W, history) → EligibleObjectHistory(W)`.

Source theorem families: P2 Objecthood/Agency/GOD/GOA; C4 FBT; P4 inverse/identifiability; P8 Lineage; P12 conditional lifecycle; N5 positive-support and explicit ancestry no-go. Prove boundary: fixed K and identical full microstate readout do not uniquely determine P8 parenthood.

**UMC-02 target:** one common-model witness with a nontrivial deterministic/stochastic action, predictive quotient, finite candidate certification and conditional P8 lineage; identify which objecthood/repair fields **cannot** be derived from W. Extend to P12 only after its repaired-organization/source-program/same-identity and viable-resource premises are constructively witnessed.

### A4. Quantitative composition — where unification is mathematically substantive

Let `e_F`, `e_B`, `e_T` denote independently measured formation, binding and transport errors. A new theorem should derive the unified bound in a common norm from **existing** C4/M-TC operations and propagate confidence events:

`e_total ≤ L e_F + e_B + e_T`;

`P(all good) ≥ 1 − Σ_j α_j`.

These are not automatically valid across incompatible metrics/measurable laws. Require each map type, metric, distortion Lipschitz coefficient, and shared sample probability space; prove a strict improvement or new control/action-selection consequence by importing P-CORE rather than re-proving the union bound.

**UMC-03 target:** a single-source typed certificate-producing theorem with actual derived joint upper bound and certified control robustness; include a bound-tightness or invalid-composition counterexample.

### A5. Π/Φ: separate low-rank constraint, parameterization, and mechanism

Given an observed Jacobian family `J_θ` with a shared two-dimensional latent factorization, `rank(J)≤2` is necessary. The factor matrices have `GL(2)` reparameterization freedom, so intrinsic unique coordinates require anchors or an allowed-gauge quotient. A rank≤2 condition does not imply uniquely named Π/Φ physical forces.

**UMC-04 target:** a necessary/sufficient factorization in a finite vector-space setting with precise rank and gauge assumptions; an exact no-go for uniqueness without an anchor; type-safe connection to P-DDH/C5 no-go. For 3D counterexamples, use existing C5 strict rank rejection.

### A6. Purpose, GOA and constructive autonomy

P1 teleological equivalence and P2 GOD/GOA can formalize dynamics relative to a given preference relation or viability contract. C6 proves that identical mechanism observations can support incompatible teleologies. Consequently **no unconditional objective extraction** from observations is possible. An internal source of objectives/programs needs new information/constitution assumptions and is subject to P12's physical-only synthesis no-go.

**UMC-05 target:** characterize identifiable classes of preferences under registered choices/perturbations; construct a seed/program information-source model satisfying actual P12 repair/homeostasis and resources, or prove which new information access is necessary.

### A7. Conditional generalization, not unbounded claims

The finite spine's core statement should remain meaningful under type-generalization. Do not upgrade to arbitrary measure spaces if `Kernel.condKernel` requires countability/countably-generated regularity. Do not apply IID confidence to temporally dependent streams. Do not silently exchange before/after-action emission conventions.

**UMC-06 target:** supply separate theorems for finite, Standard-Borel/regular, and correlated-sample regimes, each with explicit assumptions and negative controls.

## B. Artifact outputs and review obligations per stage

1. **Read/reuse audit:** existing theorem namespace/path and exact source hypotheses.
2. **Claim/proof:** a new proposition genuinely derived, its weakest assumptions, and its epistemic status.
3. **Joint witness:** one concrete `W` simultaneously satisfying the claimed cross-interface fields; full Lean compilation.
4. **Rejection/no-go:** a model where a tempting stronger assertion is false; does not add `False` to hypotheses.
5. **Independence accounting:** declare each unchanged externally supplied premise; count what was truly discharged.
6. **Reproducibility:** exact main base SHA, local feature HEAD, `lake build UEOT` exit, focused compilation and selected `#print axioms`; immutable diff, no ledger edits.
7. **Governance:** branch/PR only after proof review; local-first research. Tracker #302 updated with a 5-line recovery state, not a long CI stream.

## C. Critical red-line tests

- `P-GOA` steady-state / QSD / average reward / optimal value are not all the same invariant.
- Quotient property is not measure-kernel descent; choose exact conditional invariance when necessary.
- `rank≤2` is not a unique ontology of Π/Φ.
- Common dynamics do not identify parenthood (N5); candidate-source labels are not actual material/program provenance.
- A fixed external teleological contract is not an internally synthesized objective.
- Source-identity in one layer does not automatically survive repair dynamics.
- A mathematical product of five separate witnesses, each with an unrelated process, does **not** count as joint nonvacuity.
- A proof that assumes its claimed conclusion as a field is a renamed hypothesis, not closure.
- No new unconditional theory generated from Core v3 106/106 status or Compression 4-generator count.

## D. Initial local research deliverable

**UMC-01.1 `UnifiedFiniteProcessSpine.lean`:** instantiate SISC deterministic all-future responses and N1 normalized `flipObservationKernel` on the same Boolean transition; prove the exact equality of one-step semantics, the faithful/canonical predictive-state separation, and one N5 lineage nonidentifiability statement imported from the same stochastic process. This must be a *new typed cross-theorem* with explicit same-source data; theorem reuse is required. Next, attempt `UMC-01.2` with a nontrivial observation alias and Markov quotient/no-go.

**Do not label UMC-01 complete merely because the first finite example compiles.** Completion requires a generic bridge, joint model existence and failure boundary, with exact-head verification.
