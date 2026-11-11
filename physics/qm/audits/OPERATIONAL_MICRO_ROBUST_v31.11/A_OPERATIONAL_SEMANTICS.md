# Finite complex operational semantics bridge

Status: complete paper proofs with the exact machine subcoverage and validation limits in §8. Source snapshot: `16a89154183c22030d4526413167d095d94e6890`.

## 1. Domain and physical input

Let A and B be complex Hilbert spaces of finite **positive** dimensions dA,dB. Fix an orthonormal basis for matrix coordinates. The scalar system is C, with dimension one; it is not the zero vector space. States are every positive trace-one matrix. Effects are every matrix E with 0≤E≤I. A legal event is a complex-linear completely positive trace-nonincreasing map Φ:M(A)→M(B). An instrument is a finite, visibly labelled family (Φ_o) whose sum is trace preserving. A finite Kraus presentation is implementation data for an event, not the event's observational identity.

The complex field, Hilbert tensor product, PSD cone, Born trace rule and CP-event availability are **P/S inputs** of this chosen physical sector. This construction is a **B bridge within that sector**, not a derivation of it from Core. Core is read only. Empty mathematical matrix carriers remain useful boundary tests, but they do not belong to this physical adapter: `QuantumPurification.density_empty_elim` already proves that no normalized density exists on an empty carrier.

For an event Φ, record probabilities are unnormalized: q(E,ρ;Φ)=Tr[EΦ(ρ)]. The value at E=I is the event probability. Normalizing a branch first would remove information needed for the theorem. Zero events are legal and have no posterior.

## 2. Exact equivalence theorem

**A-OP-1 (contextual event identity).** For legal events Φ,Ψ:A→B, the following are equivalent.

1. For every finite positive-dimensional R, every joint normalized density ρ_AR, and every effect E_BR, Tr[E_BR(Φ⊗id_R)(ρ_AR)]=Tr[E_BR(Ψ⊗id_R)(ρ_AR)].
2. For every density ρ_A and every effect E_B, Tr[E_BΦ(ρ_A)]=Tr[E_BΨ(ρ_A)].
3. Φ and Ψ are identical as complex-linear maps on **all complex matrices**.
4. Their fixed-basis, input-first Choi matrices coincide, where J(Φ)[(i,a),(j,b)]=Φ(|i><j|)[a,b].

The matrices in 4 are unnormalized: Tr J(Φ) need not equal one; J(Φ)/dA is the result of applying id_A⊗Φ to the normalized maximally entangled state. No equality of Kraus lists, hidden indices or Stinespring environments is asserted.

### Proof

1⇒2: choose R=C and the canonical tensor-unit identifications.

2⇒3 has three explicit steps. First fix ρ. Both Φ(ρ) and Ψ(ρ) are Hermitian, without needing equal trace. If their difference H were nonzero, the spectral projector onto a positive or negative eigenspace of H would be an allowed effect and distinguish them. Hence Φ(ρ)=Ψ(ρ). This step uses full effects. An equivalent algebraic proof uses the existing affine-effect representation of every Hermitian matrix and Tr(H²)=0⇒H=0.

Second every PSD X is determined by normalized states: if Tr X=0 then X=0; otherwise X=(Tr X)ρ with ρ=X/Tr X a density. Thus Φ(X)=Ψ(X) for all PSD X. Every Hermitian H is the difference of its positive and negative spectral parts; consequently Φ(H)=Ψ(H). Equivalently, the existing affine-effect representation H=2rE−rI reduces this to two PSD inputs.

Third every complex X decomposes as X=H+iK with H=(X+X†)/2 and K=(X−X†)/(2i) Hermitian. Complex linearity gives equality on X. This step cannot be justified by a merely real-linear operation on unrestricted complex matrices.

3⇒1: map equality implies equality after tensoring by id_R. It holds on entangled joint inputs, not just products. Applying the same effect preserves equality. CP guarantees these are legal event outputs in every context, but the equality argument itself only needs the linear maps and their specified tensor extension.

3⇒4 is direct. For 4⇒3, each (i,j) block of J(Φ) recovers Φ(|i><j|); the matrix units form a complex basis. This is the rectangular version of the existing square `QuantumActionRealizability.choi_injective` proof. ∎

### What does and does not follow

The theorem identifies exact transformations inside the **full chosen complex model**. It is not an empirical tomography protocol and does not grant an experiment access to every state, effect or ancilla. Restricted testers produce a coarser equivalence. A finite-error replacement needs an explicit stability theorem and normalization convention; Choi-entry residuals are not automatically worst-case operational errors.

## 3. Visible instruments, tests and their quotient

**A-OP-2 (labelled congruence).** Fix a finite visible alphabet O. For two instruments I=(Φ_o), J=(Ψ_o), equality of their complete labelled CQ responses in all A-OP-1 contexts is equivalent to Φ_o=Ψ_o for every o. Equality descends through each following operation:

- Sequential composition: (Θ_v∘Φ_o)_(o,v).
- Parallel composition: (Φ_o⊗Θ_v)_(o,v), with the fixed tensor-factor identifications.
- Outcome coarse graining through a declared map f:O→Y: Φ'_y=Σ_{o:f(o)=y}Φ_o.
- Finite conditional tests: after visible o, use the chosen complete instrument (Θ_{v|o})_v, giving (Θ_{v|o}∘Φ_o)_(o,v).
- Classical randomization: Σ_a w_aΦ_{a,o}, with the action choice hidden and the visible o retained.
- Bounded adaptive protocols and explicit stopping: induction on the finite tree, retaining all visible prefixes and terminal labels, including failure and stop.

**Proof.** The complete output is Σ_o |o><o|⊗Φ_o(ρ). Its (o,o) block is the original event output; equality implies per-label equality. Conversely per-label equality gives CQ equality. Sum, map composition and tensor product preserve equalities; finite adaptive composition follows by induction, substituting equal maps at each node. Completeness is preserved because Σ_vΘ_{v|o} is TP for each o and Σ_oΦ_o is TP. The same argument works with arbitrary untouched references. A randomized controller must use the same weights for histories in the same declared observation fibre. It cannot branch on hidden Kraus indices or θ. ∎

The quotient is by equality of **actual CP maps per visible label**. A Kraus representation may be replaced before or after these constructions without changing the quotient. The observer's alphabet and controller policy are part of the contract. A relabelling is not equality unless the declared external recording map is relabelled too. The composition theorem concerns CP events on a state carrier containing every persistent memory, or freshly reset auxiliaries as in the shared model. Equal one-slot channels do not identify two hardware processes that retain different undeclared environments between slots; their complete intervention processes must instead be compared.

Rectangular tests are needed for preparations C→A, discards A→C, changes of system type and explicitly stored record registers. They cannot all be represented by a square trace-preserving `Process A A`. A rectangular event with Σ_k K_k†K_k≤I is always an event in a complete test for positive-dimensional B: choose a fixed output state τ_B and add X↦Tr[(I−ΣK†K)X]τ_B as the failure event. This is CP (diagonalize the positive defect and τ), and the sum is TP. The construction does not supply an event probability or desired equality as an axiom.

## 4. Positive and failure controls

1. **Different Kraus data, same actual event.** K=(I) and L=(3I/5,4I/5) give the same identity channel because 9/25+16/25=1. The hidden environment dimensions differ. Per-visible-label equivalence accepts them.
2. **Visible label swap.** On a qubit let P0=|0><0| and P1=|1><1|. Instruments (P0 X P0,P1 X P1) and (P1 X P1,P0 X P0) have the same forgotten channel. Input |0><0| yields different certain labels. Their complete CQ outputs have trace distance one.
3. **Hidden refinement is not a visible record.** Splitting an identity Kraus operator into 3I/5 and 4I/5 leaves one visible identity event. Promoting the split index to a visible label creates a new instrument and a different recording contract. A controller that branches on that index has gained access.
4. **Normalization loses success probability.** Φ(X)=X/4 and Ψ(X)=X/2 have identical normalized positive-branch posteriors for every density, but the identity effect gives probabilities 1/4 and 1/2. They are distinct events and distinct two-outcome tests after completion.
5. **Zero event.** The empty Kraus sum is zero; alternatively one zero Kraus matrix represents it. Its probability is zero for every input and effect. The theorem includes it; posterior normalization is undefined.
6. **Invalid empty physical object.** The sole 0×0 matrix has trace zero, so no normalized state exists. A one-dimensional scalar system instead has the unique normalized density [1]. Empty index types do not instantiate physical systems in this adapter.
7. **Restricted effect failure.** If only effects diagonal in the Z basis are allowed, identity and conjugation by Z give identical probabilities for every input, while their action on |+><+| differs. Full-effect separation cannot be silently transferred to this restricted laboratory.
8. **Restricted state failure.** If only Z-diagonal inputs are allowed, the same two channels agree on all allowed inputs even with full output effects. Full-space Choi equality is a stronger task than this support/tester restriction.

## 5. Existing-source bridge map

| Responsibility | Current source | Result of this iteration |
|---|---|---|
| Nonempty normalized physical state | `QuantumPurification.density_empty_elim`; vector states | Add positive-dimensional physical adapter; retain old empty-carrier tests |
| Full states/effects and Born bounds | `Basic.Density`, `Effects.Effect` | Reused; no Born reconstruction |
| Full normalized effect separation | `QuantumSeparation.density_eq_of_all_effect_probabilities_eq` | Extend the same argument to arbitrary Hermitian, nonnormalized outputs |
| Rectangular TP Kraus maps, all finite CP amplifications | `RectangularChannels` | Reused; add a Kraus TNI event with derived CP/TNI amplification; full bundled labelled-test interface remains a paper construction |
| Complex-linear branch / exact Choi | `QuantumActionRealizability.branchLinear`, `choi_injective` | Rectangular extension and normalized input statistical identity bridge |
| CQ output and finite adaptive record | `ClassicalQuantumMemory`, `ActionRecordBudget` | Reused; quotient invariance follows from per-label map congruence |
| Full complex purity, purification, local tomography, uniqueness | `QuantumPurification`, `PureStateCharacterization`, `ComplexLocalTomography`, `PurificationUniqueness` | Reused; not re-proved or reported as new |
| Classical and real countermodels | `OperationalSystems.classical_not_purification`, `real_not_localTomography` | Reused with original quantifiers |

## 6. OPT background and reconstruction boundary

The primary reconstruction source is Chiribella–D’Ariano–Perinotti, *Informational derivation of Quantum Theory*, arXiv:1011.6451v3 (15 July 2011), DOI 10.1103/PhysRevA.84.012311. Its Section II uses tests, visible events, identity and scalar systems, sequential/parallel composition, coarse graining, probabilities, closed finite-dimensional operational state spaces and equivalence in every auxiliary context. Section III's five axioms are causality, perfect distinguishability, ideal compression, local distinguishability and pure conditioning; purification includes reversible uniqueness. The detailed antecedent framework is arXiv:0908.1583v5 (2 June 2010), Sections II–VI. A proof of selected complex-model properties does not establish those abstract hypotheses for UEOT's full candidate class.

For the positive-dimensional full finite complex adapter, finite CP instruments provide these concrete background constructions. Identity and tensor unit exist; discard is trace and is uniquely deterministic because all densities separate effects; states are nonempty compact convex sets; for each fixed finite input/output pair and fixed visible outcome alphabet, event and test sets are closed in the corresponding finite matrix coordinates; composition, coarse graining and conditional tests above are legal. These are statements about this adapter. A full formally bundled causal OPT with all coherence laws and all reconstruction axioms has not thereby been machine-checked.

### Independent selection audit

A neutral parent-existence principle, “every state of A is a marginal of some state of AB”, is satisfied classically by p_A⊗δ_b. Access to all effects and stochastic maps also holds in ordinary finite classical theory. An additive nonnegative resource cost can be attached to each finite classical test, with sequential costs summed. Thus these three neutral principles do not select complex quantum theory. Strengthening parent existence to **pure** parents is a genuinely stronger purification hypothesis, whose classical obstruction is already formalized. It must be acknowledged rather than hidden inside the word “complete”.

Superselection or restricted-effect candidates require their own state/effect/composite definitions and hypothesis checks. The restricted controls above already show why A-OP-1 cannot be used outside its full-effect/full-state domain. No independent physical input has been eliminated by this operational bridge. It supplies precise semantics for the model already chosen.

## 7. Measurement and the shared micro model

In the shared probe–oscillator model, microscopic Kraus labels k are hidden; the readout o is visible. A finite control policy sees only declared previous records. The CQ map includes all readouts, failures and stop labels, and acts trivially on the reference R. Ancilla vacuum preparation, interaction and readout are part of the same θ-dependent original instrument. Operational equivalence means replacing a Kraus implementation by the same event map does not alter the finite controller's output.

A dilation by an ordinary environment is already an implementation of the resulting finite CP process. Therefore a measurement mechanism that predicts exactly the same complete intervention process as an allowed environment has no distinguishing experiment within that declared access. A new actualization claim would require an independent stochastic/activation/energy model and an observation that excludes the competing environment class. No such new mechanism is assumed here. `K_01` remains an SRN correlation-matrix coherence parameter, not a newly defined fundamental kernel.

## 8. Validation classification

A-OP-1 and A-OP-2 above have complete finite-dimensional paper proofs. The new `UEOTQM/OperationalEquivalence.lean` was accepted by Lean 4.33.1 (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) with `lake build UEOTQM.OperationalEquivalence`, exit 0, on 2026-11-11. Its frozen SHA-256 is `99fd7ecfa58322321269c7504b27923f36e5c7f36fadad6a938b640c78c14f37`. An environment enumeration followed by `#print axioms` audited all **80 exported namespace constants**, including generated constants, for **43 authored declarations / 28 authored theorems**. Every dependency was among `propext`, `Classical.choice`, and `Quot.sound`; no new axiom, `sorry`, `admit`, `unsafe`, `native_decide` or `sorryAx` occurs in executable source. These counts describe evidence coverage, not physics completion.

The machine coverage includes unnormalized full-effect separation, density spanning, the **full context-statistics ⇔ single-system statistics ⇔ actual map ⇔ rectangular Choi chain**, the positive-dimensional physical adapter, and a genuine rectangular TNI Kraus event whose tensor-id action, all finite-auxiliary positivity and TNI property are derived. The Choi convention is the existing square `QuantumActionRealizability` convention extended to distinct input/output carriers, with no normalization change.

For A-OP-2, machine coverage is deliberately narrower: per-visible-label actual-map composition and finite-sum congruence. A full labelled rectangular `Test` type with all closure/coherence laws, parallel tests, the explicit operational quotient and bounded-tree induction remain **paper proofs**, not machine-accepted claims. No complete abstract reconstruction has been formalized. Algebraic map-identity lemmas accept positive complex-linear maps; the physical subclass used here is CP/TNI, whose Kraus legality is separately proved.

`check_operational_controls.py` passed ten exact rational checks (SymPy 1.14.0), covering same-CP/different-Kraus, a rectangular map and untouched entangled reference, label swap, success-probability loss through normalization, zero events, and restricted states/effects. These finite controls are not universal proofs. The exact checker and actual build/axiom logs have separate source-bound receipts; two failed new-target attempts retain their original source/log identity and are not represented as successful runs.

No laboratory data, full-effect calibration or empirical reconstruction is claimed. The finite-error bridge, an empirically calibrated model-membership claim, infinite-dimensional formalization and a fully bundled abstract reconstruction remain separate responsibilities.
