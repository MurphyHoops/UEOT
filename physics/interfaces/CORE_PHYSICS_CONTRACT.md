# UEOT Core ↔ Physics Interface Contract

Status: active
Date: 2026-09-09
Layer: physics/interfaces

## 1. Purpose

This contract defines how a domain-neutral UEOT Core statement may enter a
physical theory.

A physics document must not use the phrase "derived from UEOT" unless the
dependency chain is reconstructible from the categories below.

## 2. Dependency classes

Every nontrivial physical result should classify its inputs as one or more of:

### C — Core-derived

A statement already present in the domain-neutral Core and, when claimed
`proved`, linked to a source P-ID and formal theorem.

### B — Bridge

A theorem or explicit conjecture mapping Core objects/processes to physical
objects, states, observables, symmetries, spacetime structures, fields, or
operational procedures.

A bridge is typed. It must state its domain, codomain, assumptions, and whether
it is proved or conjectural.

### S — Sector-selection principle

An additional principle selecting a physical theory class from generic UEOT.

Examples may include quantum reconstruction principles, locality assumptions,
symmetry principles, causal convexity conditions, or field-theoretic axioms.

Sector-selection principles are not generic Core results merely because they are
compatible with UEOT.

### P — Standard physical input

An input inherited from established physical theory or empirical convention,
such as a physical constant, a spacetime symmetry group, a Hamiltonian model,
a material parameter, or a laboratory calibration.

### E — Effective/modeling assumption

A scale- or regime-dependent approximation: Markovianity, weak coupling,
low-energy truncation, EFT operator basis, Born/rotating-wave approximation,
continuum limit, etc.

### O — Observable consequence

A measurable or numerically benchmarkable output that follows from the declared
input chain.

### X — Open conjecture

A proposed UEOT-specific relation that has not passed the proof/empirical gate.

## 3. Mandatory result header

Major physics results should eventually expose a header equivalent to:

```text
Result ID:
Core dependencies:
Bridge dependencies:
Sector inputs:
Standard physical inputs:
Effective assumptions:
Formal status:
Observable/benchmark:
Falsification condition:
```

## 4. Quantum-specific discipline

Generic UEOT Core has not by itself been established to force the full
quantum-specific structure.

Therefore documents must distinguish:

- generic object/process/quotient/coarse-graining results;
- operational/GPT reconstruction principles;
- complex-Hilbert selection;
- Born-rule structure;
- continuous symmetry/projective-representation input;
- Planck-scale constants such as ħ when externally supplied;
- infinite-dimensional analytic assumptions.

If a mature reconstruction theorem from prior literature supplies a step, that
step must be cited as prior art rather than renamed as an original UEOT theorem.

## 5. RG typing

The following are separate until explicitly bridged:

1. **Object-RG** — change of object representation/resolution inside UEOT Core;
2. **process coarse-graining** — stochastic/dynamical aggregation or quotient;
3. **Wilsonian RG** — integration of degrees of freedom and flow of effective
   couplings/actions.

A result may compare them, but name similarity is not an equality proof.

## 6. QFT typing

Free-field and interacting-field results must identify which axioms come from
standard QFT structure:

- Hilbert/Fock representation;
- spectral condition;
- microcausality/locality;
- Poincare covariance;
- field content;
- regularization and renormalization prescription;
- EFT matching assumptions.

UEOT may organize or constrain these structures only through an explicit bridge.

## 7. Gravity/spacetime typing

Any claim connecting UEOT to relativity must distinguish:

- kinematical spacetime assumptions;
- metric/connection structure;
- equivalence principle;
- field equations;
- thermodynamic/information interpretations;
- genuinely derived UEOT corrections.

Interpretive compatibility is not a derivation of Einstein's equations.

## 8. Validation gate

A physical result is incomplete without at least one of:

- known-theory recovery benchmark;
- limiting-case calculation;
- numerical prediction;
- experimental/null-test protocol;
- explicit no-go/counterexample.

Validation artifacts live under `validation/` and reference the result ID.

## 9. Upstream feedback

Physics is allowed to pressure Core. If a physical derivation repeatedly
requires the same additional structure, the correct response is an RFC asking
whether that structure should become:

- a generic Core axiom,
- a reusable bridge,
- a sector-selection principle,
- or remain domain-specific.

It must not be silently promoted upstream.
