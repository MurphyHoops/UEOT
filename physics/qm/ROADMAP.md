# UEOT-QM / Physics Roadmap

Status: active research roadmap
Date: 2026-09-09
Layer: physics/qm

## 1. Objective

The UEOT-QM program is not intended merely to reinterpret standard quantum
mechanics. Its research target is to determine whether a typed UEOT
object/process framework can reconstruct, organize, extend, or experimentally
constrain quantum theory while cleanly separating generic Core consequences from
quantum-sector inputs.

## 2. Completed / frozen development stages

The following stages summarize the current research line and should be
synchronized into dedicated technical documents rather than treated as already
formalized Core theorems.

### v23 — finite-dimensional convergence core

Focus:

- finite-dimensional operational reconstruction;
- coherent-measurement parent structures;
- generator classification;
- finite-sample inverse-object and experimental closure work.

Status:

- mature research artifact exists outside the currently synchronized public
  repository;
- requires structured migration and claim-by-claim status classification.

### v24 — infinite-dimensional / Weyl-CCR layer

Targets:

- separable Hilbert spaces;
- POVMs;
- Stone theorem;
- Weyl relations;
- Stone-von Neumann structure;
- projective representations of translations.

Discipline:

- do not infer `[x,p]` from a heuristic closed-loop phase integral;
- if ħ is externally supplied, label it as a physical input.

### Quantum Selection Minimality

Independent research thread:

- work inside a declared finite-dimensional causal convex GPT class;
- identify a minimal set of UEOT-compatible quantum-sector principles;
- compare with purification, local tomography, homogeneity, reversibility and
  mature reconstruction theorems;
- provide alternative theories violating each principle;
- audit logical independence and prior art.

Success requires a real sufficiency/necessity/minimality result, not renamed
standard axioms.

### v25 — symmetry, spin and identical particles

Targets:

- Wigner symmetry;
- Galilei central extension;
- SO(3)/SU(2);
- symmetrization/antisymmetrization;
- Fock construction;
- superselection.

Benchmarks:

- Stern-Gerlach;
- Rabi dynamics;
- Bell/CHSH;
- two-particle exchange.

### v26 — many-body, open and statistical quantum theory

Targets:

- GKSL/Lindblad;
- Davies-type limits;
- non-Markovian process tensors;
- KMS;
- linear response;
- entropy production;
- Ising/Heisenberg/Bose/Fermi few-body models.

### v27 — relativistic free fields

Targets:

- Klein-Gordon;
- Dirac;
- electromagnetic free fields;
- Fock representation;
- spectral condition;
- microcausality;
- inequivalent-representation audit.

### v28 — interacting QFT / RG / EFT

Targets:

- Dyson expansion;
- time ordering;
- generating functionals;
- Feynman rules;
- regularization;
- counterterms;
- renormalization conditions;
- running couplings and beta functions;
- EFT matching;
- fixed points and universality.

Mandatory distinction:

- Object-RG;
- process coarse-graining;
- Wilsonian RG.

Benchmarks include at least:

- phi^4 tree amplitude;
- one-loop correction;
- renormalized two-point function;
- beta function;
- EFT matching toy model.

### v29 / later frontier

The active frontier includes generation-structure questions and other attempts to
push UEOT beyond recovery of standard theory.

No result in this frontier is promoted merely because it reproduces a desired
integer, pattern, or phenomenological fact. Structural derivation and competing
explanations remain mandatory.

## 3. Repository migration plan

Target structure:

```text
physics/qm/
├── README.md
├── ROADMAP.md
├── reconstruction/
├── infinite-dimensional/
├── symmetry-spin/
├── identical-particles/
├── open-many-body/
├── benchmarks/
└── status/
```

QFT work should ultimately move into `physics/qft/` and RG/EFT work into
`physics/rg-eft/`; they remain listed here only to preserve the historical
UEOT-QM development sequence.

## 4. Promotion requirements

A sector stage is not "complete" until:

1. definitions are self-contained;
2. all added assumptions are classified by the Core-Physics contract;
3. known-theory benchmarks are reproduced;
4. prior-art overlap is audited;
5. new UEOT-specific claims have falsification targets;
6. any formalizable mathematical bridge is routed back to the appropriate Lean
   package without contaminating generic Core with sector axioms.

## 5. Immediate next repository actions

1. migrate the latest v23-v29 source artifacts;
2. create per-stage claim ledgers;
3. link each benchmark to `validation/benchmarks/`;
4. identify which mathematical results should return upstream to
   `core/bridges/`;
5. isolate genuinely new physical predictions from interpretive organization.
